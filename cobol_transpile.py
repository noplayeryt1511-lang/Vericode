# -*- coding: utf-8 -*-
"""
Automatic COBOL PROCEDURE DIVISION to Python transpiler.

This is the component that closes the largest previously unaddressed
gap: until now, the "ground truth" (legacy_fn) for every test case was
read off COBOL by a HUMAN and written out by hand as Python. This
module translates the PROCEDURE DIVISION instead, DETERMINISTICALLY and
AUTOMATICALLY -- no LLM, no human in the loop.

SUPPORTED STATEMENTS (deliberately narrowly scoped):
  - MOVE <value> TO <target>
  - COMPUTE <target> = <arith-expression>
  - ADD <value> TO <target>
  - SUBTRACT <value> FROM <target>
  - IF <condition> ... [ELSE ...] END-IF  (arbitrarily nested)
  - PERFORM VARYING <var> FROM <const> BY <const> UNTIL <var> > <const>
    (ONLY with constant bounds -- data-dependent PERFORM UNTIL loops
    are explicitly rejected as UnsupportedCobolConstruct rather than
    translated incorrectly)
  - STOP RUN (program end)

EVERYTHING ELSE (EVALUATE, PERFORM THRU/with paragraph names,
STRING/UNSTRING, CALL, file I/O, ...) leads to a CLEAR error naming the
location -- exactly the "unresolved rather than silently wrong"
principle from cobol_extract.py.
"""

import re

from cobol_expr import cobol_expr_to_python, cobol_condition_to_python, CobolExpressionError


class UnsupportedCobolConstruct(Exception):
    """A COBOL statement/construct that this transpiler does not (yet)
    cover -- deliberately NOT guessed at or ignored."""
    pass


def _raw_text(node):
    return node.ctx.start.getInputStream().getText(node.ctx.start.start, node.ctx.stop.stop)


def _split_targets_respecting_parens(text):
    """Splits a space-separated list of MOVE targets WITHOUT splitting
    inside parentheses (table indices like 'TABLE-ITEM (I)' consist of
    multiple tokens but must not be torn apart)."""
    targets = []
    current = []
    depth = 0
    for tok in text.split():
        current.append(tok)
        depth += tok.count("(") - tok.count(")")
        if depth <= 0:
            targets.append(" ".join(current))
            current = []
            depth = 0
    if current:
        targets.append(" ".join(current))
    return targets


class CobolStatementTranspiler:
    def __init__(self, field_decimal_scales, table_index_vars=None, known_cobol_names=None, field_lengths=None,
                 condition_name_map=None, table_occurs=None, redefines_map=None, group_picx_fields=None,
                 param_names=None):
        """field_decimal_scales: dict[python_name -> decimal_digits] --
        needed to correctly scale decimal literals in expressions. The
        scale is derived per-statement from the TARGET FIELD (the
        deliberate simplification from cobol_expr.py: ONE scale per
        expression).
        known_cobol_names: ALL known COBOL names (scalar fields AND
        groups/records, not just the ones with their own scaling) --
        needed ONLY for _check_not_truncated(), since a group like
        WS-PAYMENT has no decimal_scale of its own and would otherwise
        remain unknown to the truncation safety net.
        field_lengths: dict[python_name -> PicX.length] -- ONLY for PicX
        fields, needed for MOVE SPACES/SPACE (the target length
        determines how many spaces are actually inserted).
        param_names: the declared function parameters (Python names) --
        needed ONLY for READ INTO (see _stmt_ReadStatement): a READ into
        a field that is already a function parameter is a safe no-op
        (the parameter is already a free symbolic value anyway -- exactly
        what a real READ means), but not for a NON-parameter field
        (whose previous value would incorrectly remain in place instead
        of being replaced by a new, unknown value)."""
        self.field_decimal_scales = field_decimal_scales
        self.known_cobol_names = known_cobol_names or set(field_decimal_scales.keys())
        self.field_lengths = field_lengths or {}
        self.condition_name_map = condition_name_map or {}
        self.table_occurs = table_occurs or {}  # Python table name -> declared OCCURS count (for SEARCH)
        self.redefines_map = redefines_map or {}  # Python field name -> derived read expression (REDEFINES)
        self.group_picx_fields = group_picx_fields or {}  # Python group name -> [child field names] (for IS NUMERIC on pure PicX groups)
        self.table_index_vars = table_index_vars or {}
        self.param_names = set(param_names) if param_names is not None else None
        self.lines = []
        self.indent = 1  # statements land in a function body -> base indent 1
        self._perform_stack = []  # cycle detection for PERFORM <paragraph-name>
        self.used_unstring = False  # controls whether helper defs are prepended
        self.used_char_at = False  # same for char_at() (INSPECT)

    def _emit(self, line):
        self.lines.append("    " * self.indent + line)

    def _py_name(self, cobol_name):
        return cobol_name.strip().lower().replace("-", "_")

    def _scale_for(self, py_target_name):
        return self.field_decimal_scales.get(py_target_name, 0)

    def _check_not_truncated(self, raw_text, context_label):
        """SAFETY NET against a concretely confirmed cobol-py bug: for
        certain statements, cobol-py's own ctx.stop/ctx.start token
        boundaries sometimes yield MUTILATED text (e.g. "WS-DISTANCE"
        instead of "WS-DISTANCE-KM", or even mid-word like "W" instead of
        "WS-PAYMENT" -- both forms empirically confirmed). This is not a
        bug in this module but in the library itself -- but we must NEVER
        silently accept such a case as correct. Heuristic: if the text
        ends with a (possibly very short) fragment that is a STRICT
        PREFIX of a known (longer) field name -- AT ANY POSITION, not
        only at a hyphen boundary --, that is a strong indication of
        exactly this bug. Deliberately cast wide (including non-hyphen
        boundaries), at the cost of occasional false alarms for genuinely
        short field names that happen to be a prefix of another field --
        an unnecessary abort is preferable to silently wrong code.

        AN ATTEMPTED REFINEMENT (later reverted): a version that
        additionally checked the ACTUAL NEXT character in the original
        source text (identifier continuation vs. a natural word boundary)
        did fix a genuine false positive on external code (CBACT04C.cbl,
        see examples/CBACT04C.cbl) -- but it broke ANOTHER,
        already-known genuine truncation case (COPY REPLACING with two
        OF-qualified field references in a combined expression, see
        test_copybook_advanced.py): there, cobol-py apparently discards
        ENTIRE SUBSEQUENT TOKENS, not just a suffix WITHIN an identifier
        -- the "next character" check does not recognize that as
        truncation even though it is one. A safety net that misses a
        known real case is worse than occasional false alarms -- so this
        refinement was deliberately reverted entirely, not just narrowed."""
        last_word_match = re.search(r"([A-Za-z][A-Za-z0-9-]*)\s*$", raw_text)
        if not last_word_match:
            return
        last_word = last_word_match.group(1).upper()
        for known_field in self.known_cobol_names:
            known_cobol = known_field.upper().replace("_", "-")
            if known_cobol != last_word and known_cobol.startswith(last_word):
                raise UnsupportedCobolConstruct(
                    f"{context_label}: text ends with '{last_word}', which is a prefix of "
                    f"the known field '{known_cobol}' -- a strong indication of a "
                    f"known cobol-py bug with nested IF statements using long "
                    f"hyphenated identifiers (the statement boundary is determined "
                    f"incorrectly by the library itself). Raw text: {raw_text!r}"
                )

    def transpile_statements(self, statements):
        """Translates a list of COBOL statements. ALWAYS guarantees at
        least one emitted Python line -- if the list is empty OR
        consists entirely of no-op statements (CONTINUE, EXIT, DISPLAY),
        an EMPTY Python block would otherwise result (invalid syntax).
        Therefore this does NOT check the COBOL list for emptiness, but
        actually checks whether any lines were emitted during this call."""
        lines_before = len(self.lines)
        for stmt in statements:
            self.transpile_statement(stmt)
        if len(self.lines) == lines_before:
            self._emit("pass")

    def transpile_statement(self, stmt):
        type_name = type(stmt).__name__
        handler = getattr(self, f"_stmt_{type_name}", None)
        if handler is None:
            raise UnsupportedCobolConstruct(
                f"Unsupported statement: {type_name} -- text: {_raw_text(stmt)!r}"
            )
        handler(stmt)

    # --- MOVE ------------------------------------------------------------
    def _stmt_MoveStatement(self, stmt):
        text = _raw_text(stmt)
        self._check_not_truncated(text, "MOVE statement")
        m = re.match(r"^MOVE\s+(.+?)\s+TO\s+(.+)$", text, re.IGNORECASE | re.DOTALL)
        if not m:
            raise UnsupportedCobolConstruct(f"MOVE statement not in the expected format: {text!r}")
        source_text, target_text = m.group(1).strip(), m.group(2).strip()

        # Multi-target MOVE ('MOVE source TO target1 target2 ...') -- COBOL
        # allows any number of space-separated targets that ALL receive
        # the same source value. Split ONLY at the top level (parentheses
        # for table indices like 'TABLE-ITEM (I)' must NOT be broken up).
        targets = _split_targets_respecting_parens(target_text)
        if len(targets) > 1:
            if re.fullmatch(r"SPACES?", source_text, re.IGNORECASE):
                raise UnsupportedCobolConstruct(
                    f"MOVE SPACES TO with multiple targets is not supported: {text!r}"
                )
            scale_first = self._scale_for(self._resolve_target(targets[0]))
            try:
                source_py = cobol_expr_to_python(source_text, decimal_scale=scale_first, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"MOVE source could not be resolved: {e}") from e
            source_py = self._rescale_move_source(source_py, scale_first)
            # Intermediate variable so the source is evaluated only ONCE
            # (important should it ever gain side effects later, and
            # simply cleaner generated code).
            self._emit(f"__move_src = {source_py}")
            for t in targets:
                target_py = self._resolve_target(t)
                self._emit(f"{target_py} = __move_src")
            return

        target_py = self._resolve_target(target_text)

        # MOVE SPACE(S) TO <PicX field> -- the generic expression
        # evaluator deliberately rejects SPACE (length unknown there),
        # but HERE we know the target length (field_lengths), so we can
        # pad correctly.
        if re.fullmatch(r"SPACES?", source_text, re.IGNORECASE):
            if target_py not in self.field_lengths:
                raise UnsupportedCobolConstruct(
                    f"MOVE SPACES TO '{target_text}': target is not a known PicX field with "
                    f"a known length -- cannot reliably determine the number of spaces"
                )
            length = self.field_lengths[target_py]
            self._emit(f"{target_py} = {' ' * length!r}")
            return

        scale = self._scale_for(target_py)
        try:
            source_py = cobol_expr_to_python(source_text, decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"MOVE source expression: {e}") from e
        source_py = self._rescale_move_source(source_py, scale)
        self._emit(f"{target_py} = {source_py}")

    def _scale_lookup_key(self, operand):
        """Same as ExpressionParser._scale_lookup_key in cobol_expr.py
        (reused there for comparisons/multiplication/division) -- kept
        separate here since MOVE/ADD/SUBTRACT run through a different
        transpiler class context. This handles the same class of
        scaling bug: a table-element operand like 'ws_item[i]' was not
        previously recognized by the direct dictionary lookup, because
        only bare field names were checked as an exact key. It also
        handles OF-qualified field references ('ws_invoice.inv_amount')
        -- field_decimal_scales only indexes the field name after the
        last dot."""
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_.]*)\[", operand)
        base = m.group(1) if m else operand
        if "." in base:
            base = base.rsplit(".", 1)[-1]
        return base

    def _rescale_move_source(self, source_py, target_scale):
        """Handles the same class of scaling bug as multiplication,
        ADD/SUBTRACT and comparisons: a MOVE source that is a single
        field already scaled up to ITS OWN scale was previously carried
        over UNCHANGED -- 'MOVE WS-SRC TO WS-DST' with WS-SRC at one
        decimal digit and WS-DST at two would have incorrectly rendered
        7.6 as 0.76 instead of 7.60 (a factor of 10 too small). Likely
        the MOST FREQUENTLY triggered of these cases, since MOVE is by
        far the most common COBOL statement. Correctable ONLY for a
        simple, known field reference (source_py is then exactly the
        field name)."""
        source_scale = self.field_decimal_scales.get(self._scale_lookup_key(source_py))
        if source_scale is None or source_scale == target_scale:
            return source_py
        exponent = target_scale - source_scale
        return f"({source_py} * {10 ** exponent})" if exponent >= 0 else f"({source_py} // {10 ** -exponent})"

    # --- COMPUTE -----------------------------------------------------------
    def _find_top_level_slash(self, expr_text):
        """Finds the position of ONE division ('/') OUTSIDE any
        parentheses, AND ensures that no other operator (+, -, *) is at
        the same level outside parentheses. Returns None if the pattern
        does not match unambiguously (none, or more than one top-level
        division, or another top-level operator). Deliberately
        conservative: when in doubt, return None rather than guess."""
        depth = 0
        slash_pos = None
        i = 0
        n = len(expr_text)
        while i < n:
            ch = expr_text[i]
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            elif depth == 0:
                if ch == "/":
                    if slash_pos is not None:
                        return None  # more than one top-level division
                    slash_pos = i
                elif ch == "*":
                    return None
                elif ch in "+-" and 0 < i < n - 1 and expr_text[i - 1] == " " and expr_text[i + 1] == " ":
                    # Only count REAL operators (surrounded by spaces),
                    # not the hyphen of a hyphenated identifier (COBOL
                    # names like WS-A contain '-' WITHOUT surrounding
                    # spaces).
                    return None
            i += 1
        return slash_pos

    def _stmt_ComputeStatement(self, stmt):
        text = _raw_text(stmt)
        self._check_not_truncated(text, "COMPUTE statement")
        m = re.match(r"^COMPUTE\s+(.+?)\s*=\s*(.+)$", text, re.IGNORECASE | re.DOTALL)
        if not m:
            raise UnsupportedCobolConstruct(f"COMPUTE statement not in the expected format: {text!r}")
        target_text, expr_text = m.group(1).strip(), m.group(2).strip()
        rounded = bool(stmt.stores) and getattr(stmt.stores[0], "rounded", False)
        if rounded:
            target_text = re.sub(r"\bROUNDED\b", "", target_text, flags=re.IGNORECASE).strip()
        target_py = self._resolve_target(target_text)
        scale = self._scale_for(target_py)

        if rounded:
            # ONLY the most common case is supported: 'COMPUTE TARGET
            # ROUNDED = A / B' as the SOLE division, with no other
            # operators at the top level -- anything more complex would
            # need genuine scale tracking through the whole expression
            # (the same unsolved underlying problem as mixed-scale
            # multiplications, see cobol_expr.py), which is deliberately
            # NOT guessed at.
            #
            # IMPORTANT: "no other operator" must NOT be checked via a
            # character class that excludes '-' -- COBOL identifiers
            # CONTAIN hyphens (WS-A), which would incorrectly flag every
            # identifier as "an operator was found". In our raw text,
            # operators ALWAYS have surrounding spaces, identifier
            # hyphens NEVER do -- this reliably distinguishes the two.
            # Deliberately extended in a measured way (not generalized to
            # arbitrary expressions): what is allowed is EXACTLY ONE
            # division at the TOP parenthesis level ('A / B'), where A
            # and B may themselves be arbitrarily complex expressions
            # with +/-/*, AS LONG AS they are fully enclosed in
            # parentheses OR the entire top level has no other operators
            # besides the one division. Anything that does NOT match this
            # pattern (e.g. 'A / B + C', where '+' itself is at the top
            # level) remains deliberately rejected -- full scale tracking
            # through an arbitrary expression tree is still the same
            # unsolved underlying problem as with mixed-scale
            # multiplications.
            split_pos = self._find_top_level_slash(expr_text)
            if split_pos is None:
                raise UnsupportedCobolConstruct(
                    "COMPUTE ... ROUNDED is only supported for the form 'TARGET ROUNDED = A / B' "
                    f"(exactly ONE division at the top level, no further "
                    f"operators OUTSIDE parentheses): {expr_text!r}"
                )
            num_text, den_text = expr_text[:split_pos], expr_text[split_pos + 1:]
            try:
                num_py = cobol_expr_to_python(num_text.strip(), decimal_scale=scale,
                                               table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                den_py = cobol_expr_to_python(den_text.strip(), decimal_scale=scale,
                                               table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"COMPUTE ROUNDED expression: {e}") from e
            # Integer "round half away from zero" without floating point
            # -- COBOL's default ROUNDED mode (without an explicit MODE clause).
            self._emit(
                f"{target_py} = (2 * ({num_py}) + ({den_py})) // (2 * ({den_py})) "
                f"if ({num_py}) >= 0 else -((2 * (-({num_py})) + ({den_py})) // (2 * ({den_py})))"
            )
            return

        try:
            expr_py = cobol_expr_to_python(expr_text, decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"COMPUTE expression: {e}") from e
        self._emit(f"{target_py} = {expr_py}")

    # --- ADD / SUBTRACT ------------------------------------------------
    def _stmt_AddStatement(self, stmt):
        self._add_or_subtract(stmt, "TO", "+")

    def _stmt_SubtractStatement(self, stmt):
        self._add_or_subtract(stmt, "FROM", "-")

    def _add_or_subtract(self, stmt, keyword, py_op):
        text = _raw_text(stmt)
        self._check_not_truncated(text, f"{type(stmt).__name__}")
        m = re.match(rf"^(?:ADD|SUBTRACT)\s+(.+?)\s+{keyword}\s+(.+)$", text, re.IGNORECASE | re.DOTALL)
        if not m:
            raise UnsupportedCobolConstruct(f"{type(stmt).__name__} not in the expected format: {text!r}")
        source_text, target_text = m.group(1).strip(), m.group(2).strip()
        target_py = self._resolve_target(target_text)
        scale = self._scale_for(target_py)
        try:
            source_py = cobol_expr_to_python(source_text, decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"{type(stmt).__name__} expression: {e}") from e
        # An important, related finding (the same class of bug as
        # field-times-field multiplication): a SOURCE that is a single
        # field already scaled up to ITS OWN scale is returned unchanged
        # by cobol_expr_to_python() -- WITHOUT adjustment to the target
        # scale. 'ADD TEMP2 TO GRADES' with TEMP2 at one decimal digit
        # and GRADES at two would otherwise incorrectly treat TEMP2 as
        # already at scale 2. Correctable ONLY for a simple, known field
        # reference (source_py is then exactly the field name) -- for
        # more complex source expressions, the existing,
        # documented-as-incomplete behavior is left unchanged.
        source_scale = self.field_decimal_scales.get(self._scale_lookup_key(source_py))
        if source_scale is not None and source_scale != scale:
            exponent = scale - source_scale
            source_py = f"({source_py} * {10 ** exponent})" if exponent >= 0 else f"({source_py} // {10 ** -exponent})"
        self._emit(f"{target_py} = {target_py} {py_op} {source_py}")

    # --- MULTIPLY / DIVIDE -----------------------------------------------
    def _stmt_MultiplyStatement(self, stmt):
        self._multiply_or_divide(stmt, "MULTIPLY", "*")

    def _stmt_DivideStatement(self, stmt):
        self._multiply_or_divide(stmt, "DIVIDE", "/")

    def _multiply_or_divide(self, stmt, keyword, py_op):
        text = _raw_text(stmt)
        self._check_not_truncated(text, f"{type(stmt).__name__}")
        # DIVIDE allows TWO equivalent prepositions ('DIVIDE A BY B' AND
        # 'DIVIDE A INTO B', both with optional GIVING) -- MULTIPLY only
        # 'BY'. Both forms (WITH and WITHOUT GIVING) are supported.
        preps = ["BY", "INTO"] if keyword == "DIVIDE" else ["BY"]
        prep_pattern = "|".join(preps)

        # DIVIDE ... GIVING <quotient> REMAINDER <remainder> -- its own,
        # narrower form checked BEFORE the general GIVING form (otherwise
        # "GIVING (.+)$" would misinterpret the whole rest, including the
        # REMAINDER clause, as ONE target name). Found via an external
        # COBOL example (exm11.cbl, DoHITB/COBOL-Examples) -- fully
        # supported.
        m_remainder = re.match(
            rf"^{keyword}\s+(.+?)\s+(?:{prep_pattern})\s+(.+?)\s+GIVING\s+(.+?)\s+REMAINDER\s+(.+)$",
            text, re.IGNORECASE | re.DOTALL,
        )
        if m_remainder and keyword == "DIVIDE":
            left_text, right_text, quotient_text, remainder_text = (
                m_remainder.group(1).strip(), m_remainder.group(2).strip(),
                m_remainder.group(3).strip(), m_remainder.group(4).strip(),
            )
            prep_used = self._which_prep(text, keyword, preps)
            quotient_py = self._resolve_target(quotient_text)
            remainder_py = self._resolve_target(remainder_text)
            quotient_scale = self._scale_for(quotient_py)
            remainder_scale = self._scale_for(remainder_py)
            # Deliberately narrowly scoped to the case of equal scale
            # (scale 0, pure integers) between dividend/divisor/remainder
            # -- the REMAINDER concept itself is tied to integer
            # division; a fully general, mixed-scale REMAINDER semantics
            # would be the same unsolved underlying problem as with
            # multiplication chains and COMPUTE ... ROUNDED.
            dividend_scale = self.field_decimal_scales.get(right_text if prep_used == "INTO" else left_text)
            divisor_scale = self.field_decimal_scales.get(left_text if prep_used == "INTO" else right_text)
            if dividend_scale not in (0, None) or divisor_scale not in (0, None) or remainder_scale != 0:
                raise UnsupportedCobolConstruct(
                    "DIVIDE ... GIVING ... REMAINDER is only supported for pure integers (scale 0) "
                    "-- mixed-scale REMAINDER semantics is not covered"
                )
            quotient_expr = self._build_combined_expr(keyword, prep_used, left_text, right_text, py_op)
            try:
                quotient_py_expr = cobol_expr_to_python(quotient_expr, decimal_scale=quotient_scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                # IMPORTANT: cobol_expr_to_python parses COBOL syntax, not
                # Python -- '%' does not exist in COBOL. The two operands
                # are therefore resolved INDIVIDUALLY (scale 0, pure
                # integers -- see above) and only THEN combined with
                # Python's own '%', instead of sending a string containing
                # "%" through the COBOL expression parser.
                dividend_text = right_text if prep_used == "INTO" else left_text
                divisor_text = left_text if prep_used == "INTO" else right_text
                dividend_py = cobol_expr_to_python(dividend_text, decimal_scale=0, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                divisor_py = cobol_expr_to_python(divisor_text, decimal_scale=0, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                remainder_py_expr = f"({dividend_py} % {divisor_py})"
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"{type(stmt).__name__} expression (REMAINDER): {e}") from e
            self._emit(f"{quotient_py} = {quotient_py_expr}")
            self._emit(f"{remainder_py} = {remainder_py_expr}")
            return

        m_giving = re.match(
            rf"^{keyword}\s+(.+?)\s+(?:{prep_pattern})\s+(.+?)\s+GIVING\s+(.+)$", text, re.IGNORECASE | re.DOTALL
        )
        if m_giving:
            left_text, prep_used, right_text, target_text = self._extract_prep(m_giving, text, keyword, preps)
            target_py = self._resolve_target(target_text)
            scale = self._scale_for(target_py)
            combined = self._build_combined_expr(keyword, prep_used, left_text, right_text, py_op)
            try:
                expr_py = cobol_expr_to_python(combined, decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"{type(stmt).__name__} expression: {e}") from e
            self._emit(f"{target_py} = {expr_py}")
            return

        # WITHOUT GIVING: implicit write-back into the SECOND operand --
        # 'MULTIPLY A BY B' means 'B = A * B', 'DIVIDE A INTO B' means
        # 'B = B / A' (the second operand is simultaneously source AND
        # target). A very common COBOL idiom (shorter than the GIVING
        # form).
        m_implicit = re.match(
            rf"^{keyword}\s+(.+?)\s+(?:{prep_pattern})\s+(.+)$", text, re.IGNORECASE | re.DOTALL
        )
        if not m_implicit:
            raise UnsupportedCobolConstruct(
                f"{keyword} statement not in the expected format (neither GIVING nor implicit form): {text!r}"
            )
        left_text, prep_used, right_text = self._extract_prep_implicit(m_implicit, text, keyword, preps)
        target_py = self._resolve_target(right_text)
        scale = self._scale_for(target_py)
        combined = self._build_combined_expr(keyword, prep_used, left_text, right_text, py_op)
        try:
            expr_py = cobol_expr_to_python(combined, decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"{type(stmt).__name__} expression: {e}") from e
        self._emit(f"{target_py} = {expr_py}")

    def _extract_prep(self, m, text, keyword, preps):
        """Finds out whether 'BY' or 'INTO' was actually matched (the
        alternative regex group itself does not reveal that directly) --
        simply check the text again for which preposition appears
        between the two captured groups."""
        left_text, right_text, target_text = m.group(1).strip(), m.group(2).strip(), m.group(3).strip()
        prep_used = self._which_prep(text, keyword, preps)
        return left_text, prep_used, right_text, target_text

    def _extract_prep_implicit(self, m, text, keyword, preps):
        left_text, right_text = m.group(1).strip(), m.group(2).strip()
        prep_used = self._which_prep(text, keyword, preps)
        return left_text, prep_used, right_text

    def _which_prep(self, text, keyword, preps):
        for p in preps:
            if re.search(rf"\s{p}\s", text, re.IGNORECASE):
                return p.upper()
        return preps[0]

    def _build_combined_expr(self, keyword, prep_used, left_text, right_text, py_op):
        """DIVIDE with 'INTO' has a SWAPPED operand order compared to
        'BY': 'DIVIDE A INTO B' means 'B / A', whereas 'DIVIDE A BY B'
        means 'A / B'. MULTIPLY has no such distinction (multiplication
        is commutative, but we keep the written order for clarity)."""
        if keyword == "DIVIDE" and prep_used == "INTO":
            return f"{right_text} {py_op} {left_text}"
        return f"{left_text} {py_op} {right_text}"

    # --- IF/ELSE ---------------------------------------------------------
    def _substitute_condition_names(self, text):
        """Replaces every occurrence of a known 88-level condition name in
        the raw text with its equivalent COBOL comparison clause (FIELD =
        VALUE), BEFORE the generic expression parser gets to it -- it does
        not know about condition names, but it can process the resulting
        COBOL comparison syntax unchanged. Uses self.condition_name_map
        (collected once, globally, from the DATA DIVISION, see
        cobol_extract.extract_condition_names) instead of walking the ASG
        again per statement -- more robust, since some statement types
        (e.g. EVALUATE-WHEN clauses) are only available as raw text
        anyway, not as a typed condition tree."""
        if not self.condition_name_map:
            return text
        for name in sorted(self.condition_name_map, key=len, reverse=True):
            text = re.sub(rf"\b{re.escape(name)}\b", self.condition_name_map[name], text, flags=re.IGNORECASE)
        return text

    def _stmt_IfStatement(self, stmt):
        cond_text = _raw_text(stmt.condition)
        cond_text = self._substitute_condition_names(cond_text)
        scale = self._guess_condition_scale(cond_text)
        try:
            cond_py = cobol_condition_to_python(cond_text, decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"IF condition: {e}") from e
        self._emit(f"if {cond_py}:")
        self.indent += 1
        self.transpile_statements(stmt.then.statements)
        self.indent -= 1
        if stmt.else_ is not None and stmt.else_.statements:
            self._emit("else:")
            self.indent += 1
            self.transpile_statements(stmt.else_.statements)
            self.indent -= 1

    def _guess_condition_scale(self, cond_text):
        for word in re.findall(r"[A-Za-z][A-Za-z0-9-]*", cond_text):
            py = self._py_name(word)
            if py in self.field_decimal_scales:
                return self.field_decimal_scales[py]
        return 0

    # --- PERFORM VARYING / PERFORM <paragraph-name> -----------------------------
    def _stmt_PerformStatement(self, stmt):
        if str(stmt.perform_type) == "PerformType.INLINE":
            self._perform_inline_varying(stmt)
        elif str(stmt.perform_type) == "PerformType.PROCEDURE":
            self._perform_procedure(stmt)
        else:
            raise UnsupportedCobolConstruct(f"Unsupported PERFORM type: {stmt.perform_type}: {_raw_text(stmt)!r}")

    def _perform_inline_varying(self, stmt):
        inline = stmt.perform_inline_statement
        header = stmt.ctx.start.getInputStream().getText(
            stmt.ctx.start.start, inline.statements[0].ctx.start.start - 1
        ) if inline.statements else _raw_text(stmt)

        m = re.match(
            r"^\s*PERFORM\s+VARYING\s+([A-Za-z][A-Za-z0-9-]*)\s+FROM\s+(\d+)\s+BY\s+(\d+)"
            r"\s+UNTIL\s+\1\s*(>=|>)\s*(\d+)\s*$",
            header.strip(), re.IGNORECASE,
        )
        if not m:
            raise UnsupportedCobolConstruct(
                f"Only 'PERFORM VARYING X FROM <const> BY <const> UNTIL X (>|>=) <const>' "
                f"is supported (constant, non-data-dependent bounds; only ascending "
                f"counters): {header.strip()!r}"
            )
        var_name, start, step, op, bound = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4), int(m.group(5))
        if step < 1:
            raise UnsupportedCobolConstruct(f"Only positive step sizes are supported (BY {step})")
        py_var = self._py_name(var_name)
        stop = bound + 1 if op == ">" else bound
        self._emit(f"for {py_var} in range({start}, {stop}, {step}):")
        self.indent += 1
        self.transpile_statements(inline.statements)
        self.indent -= 1

    def _perform_procedure(self, stmt):
        """PERFORM <paragraph> | PERFORM <paragraph-A> THRU <paragraph-B>
        [<n> TIMES | UNTIL <condition>] -- the paragraphs are not
        translated as a function call (our engine has no concept of
        subprograms), but INLINE-expanded: their statements are inserted
        directly at this point (recursively, with cycle detection against
        direct/indirect self-calls). With THRU, ALL paragraphs between A
        and B (in source order, inclusive) are combined into ONE
        statement list."""
        text = _raw_text(stmt)
        m = re.match(
            r"^PERFORM\s+([A-Za-z0-9][A-Za-z0-9-]*)"
            r"(?:\s+THRU\s+([A-Za-z0-9][A-Za-z0-9-]*))?"
            r"\s*(?:(\d+)\s+TIMES|UNTIL\s+(.+))?$",
            text.strip(), re.IGNORECASE | re.DOTALL,
        )
        if not m:
            raise UnsupportedCobolConstruct(
                f"Only 'PERFORM <paragraph>[ THRU <paragraph>]', '... <n> TIMES' or "
                f"'... UNTIL <condition>' is supported: {text!r}"
            )
        para_name, thru_name, times_text, until_text = m.group(1), m.group(2), m.group(3), m.group(4)
        target_statements, involved_names = self._resolve_perform_target(stmt, para_name, thru_name)

        for name in involved_names:
            if name in self._perform_stack:
                raise UnsupportedCobolConstruct(
                    f"Recursive/cyclic PERFORM call detected ({' -> '.join(self._perform_stack)} -> {name}) "
                    f"-- not supported (our model only handles finitely expandable calls)"
                )
        self._perform_stack.extend(involved_names)
        try:
            if times_text is not None:
                n = int(times_text)
                self._emit(f"for _perform_i in range({n}):")
                self.indent += 1
                self.transpile_statements(target_statements)
                self.indent -= 1
            elif until_text is not None:
                scale = self._guess_condition_scale(until_text)
                try:
                    cond_py = cobol_condition_to_python(until_text.strip(), decimal_scale=scale,
                                                          table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                except CobolExpressionError as e:
                    raise UnsupportedCobolConstruct(f"PERFORM ... UNTIL condition: {e}") from e
                # "PERFORM X UNTIL <cond>" -> the loop runs as long as NOT <cond>
                self._emit(f"while not ({cond_py}):")
                self.indent += 1
                self.transpile_statements(target_statements)
                self.indent -= 1
            else:
                # Simple one-time call -- statements inserted directly inline
                self.transpile_statements(target_statements)
        finally:
            for _ in involved_names:
                self._perform_stack.pop()

    def _resolve_perform_target(self, stmt, para_name, thru_name):
        """Resolves PERFORM <A> [THRU <B>] into a combined statement
        list. Without THRU: just the one paragraph. With THRU: ALL
        paragraphs between A and B in source order (root_paragraphs),
        inclusive -- THRU targeting a paragraph that comes BEFORE A in
        the source is rejected as an error, not silently treated as
        empty."""
        pd = stmt.program_unit.procedure_division
        root = pd.root_paragraphs
        if not root and pd.sections:
            root = pd.sections[0].paragraphs  # same sections fallback logic as for the entry point
        names = [p.name.upper() for p in root]

        if thru_name is None:
            target_para = pd.get_paragraph(para_name)
            if target_para is None:
                raise UnsupportedCobolConstruct(f"Paragraph '{para_name}' not found")
            return target_para.statements, [para_name.upper()]

        try:
            i_start = names.index(para_name.upper())
            i_end = names.index(thru_name.upper())
        except ValueError as e:
            raise UnsupportedCobolConstruct(f"Paragraph for PERFORM ... THRU not found: {e}") from e
        if i_end < i_start:
            raise UnsupportedCobolConstruct(
                f"PERFORM {para_name} THRU {thru_name}: '{thru_name}' comes BEFORE '{para_name}' "
                f"in the source -- not supported (no backward range)"
            )
        involved = root[i_start:i_end + 1]
        combined = []
        for p in involved:
            combined.extend(p.statements)
        return combined, [p.name.upper() for p in involved]

    # --- STOP RUN ----------------------------------------------------------
    def _stmt_StopStatement(self, stmt):
        pass  # pure program termination -- no Python equivalent needed, return happens separately

    # --- CONTINUE / EXIT (pure no-ops) -------------------------------------
    def _stmt_ContinueStatement(self, stmt):
        pass  # "do nothing" by COBOL definition -- transpile_statements()
              # itself ensures valid Python still results

    def _stmt_ExitStatement(self, stmt):
        pass  # pure paragraph marker/end, no effect of its own

    # --- DISPLAY (no-op) ---------------------------------------------------
    def _stmt_DisplayStatement(self, stmt):
        # Pure output -- NEVER changes program state, so it has no
        # consequence for our verification model (which only compares a
        # function's input/output values). Deliberately treated as a
        # no-op rather than rejected -- unlike, e.g., file I/O, which
        # touches real state outside the function.
        pass

    # --- OPEN/CLOSE (no-op) -- a first, deliberately narrow step towards
    # a "hybrid mode" for file I/O (see docs/VERIFICATION_GUARANTEES.md,
    # section 4, "Partially supported (hybrid mode)").
    # OPEN/CLOSE themselves do NOT change any field we track -- they only
    # prepare or release a file handle. The genuinely difficult part
    # (READ/WRITE, which move real data) remains deliberately rejected
    # rather than guessed at -- that would need a model of "file content
    # as symbolic input", which does not yet exist.
    def _stmt_OpenStatement(self, stmt):
        pass

    def _stmt_CloseStatement(self, stmt):
        pass

    def _stmt_ReadStatement(self, stmt):
        """A SECOND step towards a "hybrid mode" for file I/O (after
        OPEN/CLOSE). Deliberately narrow: 'READ <file> INTO <target>' is
        a safe no-op ONLY when <target> is already a declared function
        parameter -- in that case the symbolic value is already a free,
        unconstrained value, exactly what a real READ means (the file
        content is arbitrary, unpredictable). If <target> is NOT a
        parameter (e.g. a WORKING-STORAGE field with a declared initial
        value), a no-op would be WRONG -- the previous value would
        incorrectly remain in place instead of being replaced by a new,
        unknown value. In that case this is clearly rejected, not
        guessed at. 'READ <file>' WITHOUT INTO (which writes into the FD
        record area ITSELF) remains outside this narrow step -- that
        would additionally need an FD-record -> parameter mapping that
        does not currently exist."""
        text = _raw_text(stmt)
        m = re.match(r"^READ\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+INTO\s+(.+)$", text, re.IGNORECASE | re.DOTALL)
        if not m:
            raise UnsupportedCobolConstruct(
                f"Only 'READ <file> INTO <target>' is supported (and only when <target> "
                f"is already a function parameter): {text!r}"
            )
        target_text = m.group(2).strip()
        target_py = self._resolve_target(target_text)
        if self.param_names is None or target_py not in self.param_names:
            raise UnsupportedCobolConstruct(
                f"READ ... INTO {target_text!r}: the target is not a declared function parameter -- "
                f"a no-op would be WRONG here, since the previous (default) value would incorrectly "
                f"remain in place instead of being replaced by a new, unknown value. Declare the "
                f"target as a parameter if its value should be treated as arbitrary, symbolic input."
            )
        pass  # safe no-op: target_py is already a free symbolic value

    def _stmt_WriteStatement(self, stmt):
        """Unlike READ (which could potentially OVERWRITE a TRACKED field
        state), WRITE only reads FROM a field OUT to a file -- it NEVER
        writes back into a tracked field. Just like DISPLAY: pure output,
        with no consequence for our verification model. Therefore
        UNCONDITIONALLY safe, no parameter check needed (unlike the READ
        handler above)."""
        pass

    def _stmt_RewriteStatement(self, stmt):
        """Same reasoning as WRITE: 'REWRITE <record> FROM <source>'
        reads FROM <source> and updates a file record -- it NEVER writes
        back into a tracked WORKING-STORAGE field. Unconditionally safe
        as a no-op, no parameter check needed."""
        pass

    def _stmt_DeleteStatement(self, stmt):
        """'DELETE <file>' removes a record from an indexed/relative
        file -- sets NO WORKING-STORAGE field, affects only file state
        outside our verification model. Unconditionally safe as a no-op,
        no parameter check needed (the same category as WRITE/REWRITE:
        purely "goes out", nothing comes back into a tracked field)."""
        pass

    def _stmt_StartStatement(self, stmt):
        """A further step towards a hybrid mode for file I/O:
        'START <file> KEY IS ...' positions for the next sequential
        access -- it itself sets NO WORKING-STORAGE field. An earlier
        concern was that START could influence WHICH record a subsequent
        READ returns. On closer inspection this is IRRELEVANT for our model: READ INTO is
        already modeled as an arbitrary, unconstrained value (see
        _stmt_ReadStatement above) -- regardless of what START
        positioned, the result of a subsequent READ remains "some
        possible value". START itself therefore has NO observable effect
        in our model, just like OPEN/CLOSE. IMPORTANT LIMITATION (not a
        new one, but an existing one): our model does NOT represent
        INVALID KEY/AT END -- READ is always considered to succeed in
        our model. This was already the case before, and treating START
        as a no-op does not make it worse."""
        pass

    # --- SET <condition-name> TO TRUE ---------------------------------------
    # --- INITIALIZE (only numeric scalar fields -> 0) ---------------------
    def _stmt_InitializeStatement(self, stmt):
        text = _raw_text(stmt)
        self._check_not_truncated(text, "INITIALIZE statement")
        for call in stmt.data_item_calls:
            name = getattr(call, "name", None)
            if name is None:
                raise UnsupportedCobolConstruct(f"INITIALIZE target could not be resolved: {text!r}")
            target_py = self._py_name(name)
            if target_py not in self.field_decimal_scales:
                raise UnsupportedCobolConstruct(
                    f"INITIALIZE '{name}': only numeric scalar fields are supported (no PicX, "
                    f"no group/table -- their field type is not known well enough at this "
                    f"point in the transpiler to reliably determine the correct default value)"
                )
            self._emit(f"{target_py} = 0")

    def _stmt_SetStatement(self, stmt):
        text = _raw_text(stmt)
        self._check_not_truncated(text, "SET statement")

        # Pattern 2: index/counter assignment ('SET target TO value'
        # without TRUE, or 'SET target UP BY value' / 'SET target DOWN BY
        # value') -- COBOL's INDEX data type (for manual table traversal,
        # complementing PERFORM VARYING) is treated in our model like a
        # normal integer field, so a simple assignment/increment/
        # decrement suffices.
        m_up_down = re.match(r"^SET\s+(.+?)\s+(UP|DOWN)\s+BY\s+(.+)$", text.strip(), re.IGNORECASE | re.DOTALL)
        if m_up_down:
            target_text, direction, amount_text = m_up_down.groups()
            target_py = self._resolve_target(target_text.strip())
            scale = self._scale_for(target_py)
            try:
                amount_py = cobol_expr_to_python(amount_text.strip(), decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"SET UP/DOWN BY amount could not be resolved: {e}") from e
            op = "+" if direction.upper() == "UP" else "-"
            self._emit(f"{target_py} = ({target_py} {op} {amount_py})")
            return

        if str(stmt.set_type) == "SetType.SET_TO" and not re.search(r"\bTRUE\b", text, re.IGNORECASE):
            m_simple = re.match(r"^SET\s+(.+?)\s+TO\s+(.+)$", text.strip(), re.IGNORECASE | re.DOTALL)
            if m_simple:
                target_text, value_text = m_simple.groups()
                # ONLY when the target is NOT a condition name (88-level)
                # -- otherwise fall through to the existing 'SET
                # <condition-name> TO TRUE' path below (which explicitly
                # rejects FALSE, and that remains deliberate).
                entry = getattr(stmt.receiving_calls[0].delegate, "data_description_entry", None) if len(stmt.receiving_calls) == 1 else None
                is_condition_name = entry is not None and type(entry).__name__ == "DataDescriptionEntryCondition"
                if not is_condition_name:
                    target_py = self._resolve_target(target_text.strip())
                    scale = self._scale_for(target_py)
                    try:
                        value_py = cobol_expr_to_python(value_text.strip(), decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                    except CobolExpressionError as e:
                        raise UnsupportedCobolConstruct(f"SET value could not be resolved: {e}") from e
                    self._emit(f"{target_py} = {value_py}")
                    return

        if str(stmt.set_type) != "SetType.SET_TO" or not re.search(r"\bTRUE\b", text, re.IGNORECASE):
            raise UnsupportedCobolConstruct(
                f"Only 'SET <condition-name> TO TRUE', 'SET <target> TO <value>' or 'SET <target> "
                f"UP/DOWN BY <value>' is supported (no SET TO FALSE): {text!r}"
            )
        if len(stmt.receiving_calls) != 1:
            raise UnsupportedCobolConstruct(f"Only a single SET target is supported: {text!r}")

        entry = getattr(stmt.receiving_calls[0].delegate, "data_description_entry", None)
        if entry is None or type(entry).__name__ != "DataDescriptionEntryCondition":
            raise UnsupportedCobolConstruct(f"SET target is not a condition name (88-level): {text!r}")
        parent = entry.parent_data_description_entry_group
        if parent is None:
            raise UnsupportedCobolConstruct(f"Condition name '{entry.name}' has no parent field: {text!r}")
        value_clause = entry.value_clause
        if value_clause is None:
            raise UnsupportedCobolConstruct(f"Condition name '{entry.name}' has no VALUE clause: {text!r}")

        value_text = _raw_text(value_clause)
        m = re.match(r"^VALUE\s+(.+)$", value_text.strip(), re.IGNORECASE | re.DOTALL)
        if not m:
            raise UnsupportedCobolConstruct(f"VALUE clause not in the expected format: {value_text!r}")
        value_expr_text = m.group(1).strip()
        if re.search(r"\bTHRU\b", value_expr_text, re.IGNORECASE) or "," in value_expr_text:
            raise UnsupportedCobolConstruct(
                f"Only a SINGLE VALUE is supported (no THRU range/multiple value "
                f"on the condition name): {value_expr_text!r}"
            )

        target_py = self._py_name(parent.name)
        scale = self._scale_for(target_py)
        try:
            value_py = cobol_expr_to_python(value_expr_text, decimal_scale=scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"SET value: {e}") from e
        self._emit(f"{target_py} = {value_py}")

    # --- STRING (concatenation) ------------------------------------------------
    def _stmt_StringStatement(self, stmt):
        text = _raw_text(stmt)
        self._check_not_truncated(text, "STRING statement")
        m = re.match(r"^STRING\s+(.+)\s+INTO\s+(.+)$", text, re.IGNORECASE | re.DOTALL)
        if not m:
            raise UnsupportedCobolConstruct(f"STRING statement not in the expected format: {text!r}")
        pieces_text, target_text = m.group(1), m.group(2)
        # The explicit scope-terminator keyword 'END-STRING' (instead of
        # implicit termination by a period) is NOT part of the
        # assignment target -- it must be removed BEFORE resolving the
        # target, otherwise it would be incorrectly interpreted as part
        # of the target expression.
        target_text = re.sub(r"\s*\bEND-STRING\b\s*$", "", target_text, flags=re.IGNORECASE)
        target_py = self._resolve_target(target_text.strip())

        segments = re.split(r"\bDELIMITED\s+BY\s+SIZE\b", pieces_text, flags=re.IGNORECASE)
        segments = [s.strip() for s in segments if s.strip()]
        if not segments:
            raise UnsupportedCobolConstruct(f"STRING with no recognizable source segments: {text!r}")
        # ONLY "DELIMITED BY SIZE" is supported (take each segment in
        # full) -- "DELIMITED BY <other delimiter>" (e.g. up to the first
        # space) is explicitly rejected, not guessed at.
        if re.search(r"\bDELIMITED\s+BY\s+(?!SIZE\b)", pieces_text, flags=re.IGNORECASE):
            raise UnsupportedCobolConstruct(
                f"Only 'DELIMITED BY SIZE' is supported, no other delimiter: {text!r}"
            )
        # COBOL allows several comma-separated sources that share ONE
        # 'DELIMITED BY SIZE' clause ('STRING A, B DELIMITED BY SIZE INTO
        # C') -- each segment split this way must therefore be split ONE
        # MORE time on commas, otherwise the expression parser would see
        # a comma it does not know.
        expanded_segments = []
        for seg in segments:
            expanded_segments.extend(p.strip() for p in seg.split(",") if p.strip())
        segments = expanded_segments

        piece_exprs = []
        for seg in segments:
            try:
                piece_exprs.append(cobol_expr_to_python(seg, decimal_scale=0, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields))
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"STRING segment {seg!r}: {e}") from e
        combined = " + ".join(piece_exprs)
        self._emit(f"{target_py} = {combined}")

    # --- UNSTRING (splitting, EXACTLY 2 targets, ONE delimiter) -------------
    def _stmt_UnstringStatement(self, stmt):
        text = _raw_text(stmt)
        self._check_not_truncated(text, "UNSTRING statement")
        m = re.match(
            r"^UNSTRING\s+(.+?)\s+DELIMITED\s+BY\s+(\"[^\"]*\"|'[^']*')\s+INTO\s+(.+)$",
            text, re.IGNORECASE | re.DOTALL,
        )
        if not m:
            raise UnsupportedCobolConstruct(
                f"Only 'UNSTRING <source> DELIMITED BY <a single literal delimiter> INTO <target1> <target2>' "
                f"is supported (no ALL prefix, no COUNT/TALLYING clause, no multiple "
                f"delimiters, no more than 2 targets): {text!r}"
            )
        source_text, delim_literal, targets_text = m.group(1).strip(), m.group(2), m.group(3).strip()
        # Same as STRING: the explicit scope terminator 'END-UNSTRING' is
        # not part of the targets.
        targets_text = re.sub(r"\s*\bEND-UNSTRING\b\s*$", "", targets_text, flags=re.IGNORECASE).strip()
        targets = targets_text.split()
        if len(targets) != 2:
            raise UnsupportedCobolConstruct(
                f"Only EXACTLY 2 target fields are supported (got: {len(targets)}): {text!r}"
            )
        try:
            source_py = cobol_expr_to_python(source_text, decimal_scale=0, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"UNSTRING source: {e}") from e
        target1_py = self._resolve_target(targets[0])
        target2_py = self._resolve_target(targets[1])
        delim_py = repr(delim_literal[1:-1])  # strip COBOL quotes

        self.used_unstring = True
        self._emit(f"{target1_py} = unstring_before({source_py}, {delim_py})")
        self._emit(f"{target2_py} = unstring_after({source_py}, {delim_py})")

    # --- SEARCH (linear search only, EXACTLY ONE WHEN) -------------------------
    def _stmt_SearchStatement(self, stmt):
        """Only 'SEARCH <table> [AT END ...] WHEN <table> (<index>) = ...
        <statements> END-SEARCH' is supported -- no SEARCH ALL (binary
        search, requires sortedness), no multiple WHEN clauses.
        Translates to: a 'found' flag + a loop over all positions that
        stops checking further after the first hit (no 'break' needed,
        since our engine does not support it -- instead 'if not found: if
        condition: ...', which symbolically yields exactly the same
        result)."""
        text = _raw_text(stmt)
        self._check_not_truncated(text, "SEARCH statement")
        if len(stmt.when_phrases) != 1:
            raise UnsupportedCobolConstruct(
                "SEARCH: only EXACTLY ONE WHEN clause is supported (no SEARCH ALL, no multiple WHEN)"
            )

        table_name = stmt.data_call.name
        table_py = self._py_name(table_name)
        if table_py not in self.table_occurs:
            raise UnsupportedCobolConstruct(
                f"SEARCH '{table_name}': no known OCCURS table (table_occurs is missing this name)"
            )
        occurs = self.table_occurs[table_py]

        when = stmt.when_phrases[0]
        cond_text = _raw_text(when.condition)
        self._check_not_truncated(cond_text, "SEARCH WHEN condition")

        m = re.search(rf"\b{re.escape(table_name)}\s*\(\s*([A-Za-z][A-Za-z0-9-]*)\s*\)", cond_text, re.IGNORECASE)
        if not m:
            raise UnsupportedCobolConstruct(
                f"SEARCH WHEN condition must reference '{table_name} (index)' (the INDEXED BY index "
                f"in the condition): {cond_text!r}"
            )
        index_name = m.group(1)

        loop_var = f"_search_idx_{table_py}"
        found_var = f"_search_found_{table_py}"
        saved_index_map = self.table_index_vars.get(index_name, "__unset__")
        self.table_index_vars[index_name] = loop_var
        try:
            scale = self._guess_condition_scale(cond_text)
            try:
                cond_py = cobol_condition_to_python(cond_text, decimal_scale=scale,
                                                      table_index_vars=self.table_index_vars,
                                                      field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"SEARCH WHEN condition: {e}") from e

            self._emit(f"{found_var} = False")
            self._emit(f"for {loop_var} in range({occurs}):")
            self.indent += 1
            self._emit(f"if not {found_var}:")
            self.indent += 1
            self._emit(f"if {cond_py}:")
            self.indent += 1
            self._emit(f"{found_var} = True")
            self.transpile_statements(when.statements)
            self.indent -= 3

            if stmt.at_end_phrase is not None and stmt.at_end_phrase.statements:
                self._emit(f"if not {found_var}:")
                self.indent += 1
                self.transpile_statements(stmt.at_end_phrase.statements)
                self.indent -= 1
        finally:
            if saved_index_map == "__unset__":
                self.table_index_vars.pop(index_name, None)
            else:
                self.table_index_vars[index_name] = saved_index_map

    # --- INSPECT (only TALLYING/REPLACING FOR ALL <a single character>) -------------
    def _stmt_InspectStatement(self, stmt):
        """AN IMPORTANT, EMPIRICALLY CONFIRMED PRACTICAL LIMIT with
        REPLACING: the string reconstruction generated here (chained
        If/Concat expressions, one term per character position) is
        logically correct and fast for SHORT fields (tested: 5 characters
        -> 0.3s), but Z3's string solver shows a dramatic, exponential-
        looking drop-off starting at just 6 characters (>15s, no longer
        practical). TALLYING (pure integer summation, no string rebuild)
        is NOT affected by this and stays fast even for longer fields.
        REPLACING is therefore currently NOT practical for most real
        COBOL PicX fields (typically 10-50+ characters) -- a known,
        unsolved problem, not a silent limitation."""
        text = _raw_text(stmt)
        self._check_not_truncated(text, "INSPECT statement")

        m_tally = re.match(
            r'^INSPECT\s+(.+?)\s+TALLYING\s+(.+?)\s+FOR\s+ALL\s+("[^"]*"|\'[^\']*\')\s*$',
            text, re.IGNORECASE | re.DOTALL,
        )
        m_replace = re.match(
            r'^INSPECT\s+(.+?)\s+REPLACING\s+ALL\s+("[^"]*"|\'[^\']*\')\s+BY\s+("[^"]*"|\'[^\']*\')\s*$',
            text, re.IGNORECASE | re.DOTALL,
        )

        if m_tally:
            source_text, counter_text = m_tally.group(1).strip(), m_tally.group(2).strip()
            literal = m_tally.group(3)[1:-1]
            if len(literal) != 1:
                raise UnsupportedCobolConstruct(
                    f"INSPECT TALLYING: only a SINGLE character is supported as the search literal "
                    f"(no multi-character pattern, no FOR LEADING/CHARACTERS): {literal!r}"
                )
            source_py = self._resolve_target(source_text)
            counter_py = self._resolve_target(counter_text)
            if source_py not in self.field_lengths:
                raise UnsupportedCobolConstruct(
                    f"INSPECT TALLYING: source '{source_text}' is not a known PicX field "
                    f"with a known length -- character-by-character counting needs a fixed length"
                )
            length = self.field_lengths[source_py]
            self.used_char_at = True
            terms = " + ".join(
                f"(1 if char_at({source_py}, {i}) == {literal!r} else 0)" for i in range(length)
            )
            self._emit(f"{counter_py} = {counter_py} + ({terms})")
            return

        if m_replace:
            source_text = m_replace.group(1).strip()
            from_lit, to_lit = m_replace.group(2)[1:-1], m_replace.group(3)[1:-1]
            if len(from_lit) != 1 or len(to_lit) != 1:
                raise UnsupportedCobolConstruct(
                    f"INSPECT REPLACING: only SINGLE characters are supported (no multi-character "
                    f"pattern): {from_lit!r} BY {to_lit!r}"
                )
            source_py = self._resolve_target(source_text)
            if source_py not in self.field_lengths:
                raise UnsupportedCobolConstruct(
                    f"INSPECT REPLACING: source '{source_text}' is not a known PicX field "
                    f"with a known length -- positional replacement needs a fixed length"
                )
            length = self.field_lengths[source_py]
            self.used_char_at = True
            terms = " + ".join(
                f"({to_lit!r} if char_at({source_py}, {i}) == {from_lit!r} else char_at({source_py}, {i}))"
                for i in range(length)
            )
            self._emit(f"{source_py} = {terms}")
            return

        raise UnsupportedCobolConstruct(
            f"Only 'INSPECT <field> TALLYING <counter> FOR ALL <single-character-literal>' or "
            f"'INSPECT <field> REPLACING ALL <single-character-literal> BY <single-character-literal>' "
            f"is supported (no FOR LEADING/CHARACTERS, no CONVERTING, no multi-character "
            f"pattern): {text!r}"
        )

    # --- EVALUATE ------------------------------------------------------
    def _stmt_EvaluateStatement(self, stmt):
        subject_text = _raw_text(stmt.subject_value_stmt).strip()
        is_true_form = subject_text.upper() == "TRUE"
        subject_py = None
        subject_scale = 0
        if not is_true_form:
            try:
                subject_py = cobol_expr_to_python(subject_text, decimal_scale=0, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
            except CobolExpressionError as e:
                raise UnsupportedCobolConstruct(f"EVALUATE subject: {e}") from e
            subject_scale = self._guess_condition_scale(subject_text)

        first = True
        for when in stmt.when_phrases:
            header = self._when_header_text(when)
            self._check_not_truncated(header, "EVALUATE WHEN clause")
            if is_true_form:
                # EVALUATE TRUE / WHEN <condition> -- each WHEN clause is
                # itself a complete condition (a classic If/Elif chain).
                # Repeated WHEN clauses (a shared body) -- if present --
                # are likewise combined with OR.
                sub_conds = [c.strip() for c in re.split(r"\bWHEN\b", header, flags=re.IGNORECASE) if c.strip()]
                if not sub_conds:
                    raise UnsupportedCobolConstruct(f"EVALUATE TRUE / WHEN without a condition: {header!r}")
                rendered = []
                for sc in sub_conds:
                    sc = self._substitute_condition_names(sc)
                    when_scale = self._guess_condition_scale(sc)
                    try:
                        rendered.append(cobol_condition_to_python(sc, decimal_scale=when_scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields))
                    except CobolExpressionError as e:
                        raise UnsupportedCobolConstruct(f"EVALUATE TRUE / WHEN condition: {e}") from e
                cond_py = "(" + " or ".join(rendered) + ")"
            else:
                # EVALUATE <subject> / WHEN <value> -- equality comparison,
                # now including THRU ranges and comma-separated multiple values.
                cond_py = self._when_value_condition(header, subject_py, subject_scale)
            self._emit(f"{'if' if first else 'elif'} {cond_py}:")
            first = False
            self.indent += 1
            self.transpile_statements(when.statements)
            self.indent -= 1

        if stmt.when_other is not None and stmt.when_other.statements:
            self._emit("else:")
            self.indent += 1
            self.transpile_statements(stmt.when_other.statements)
            self.indent -= 1
        elif first:
            # There was no WHEN clause at all -- should never happen, but
            # rejected clearly just in case, instead of generating empty code
            raise UnsupportedCobolConstruct("EVALUATE without any WHEN clause")

    def _normalize_scale_pair_transpile(self, left, right):
        """Same correction as cobol_expr.py: ExpressionParser._normalize_scale_pair,
        needed here for the EVALUATE WHEN comparisons (which do NOT go
        through the normal condition parser, but build Python comparison
        strings directly -- hence the same correction is needed
        separately)."""
        left_scale = self.field_decimal_scales.get(left)
        right_scale = self.field_decimal_scales.get(right)
        if left_scale is None or right_scale is None or left_scale == right_scale:
            return left, right
        if left_scale < right_scale:
            return f"({left} * {10 ** (right_scale - left_scale)})", right
        return left, f"({right} * {10 ** (left_scale - right_scale)})"

    def _when_value_condition(self, header, subject_py, subject_scale):
        """Builds the comparison condition for 'EVALUATE <subject> / WHEN
        <value>'. Supports: a single value, a THRU range, and repeated
        WHEN clauses with a shared body ("WHEN 1 WHEN 2 WHEN 3 <body>" --
        the COBOL idiom that cobol-py returns as ONE phrase with multiple
        "WHEN" in the raw text). Comma-separated multiple values in ONE
        WHEN clause ("WHEN 1, 2, 3") are NOT supported -- the underlying
        cobol-py parser itself already rejects this as a syntax error,
        this is not a limitation of this module."""
        clauses = [c.strip() for c in re.split(r"\bWHEN\b", header, flags=re.IGNORECASE) if c.strip()]
        if not clauses:
            raise UnsupportedCobolConstruct(f"WHEN clause with no recognizable value: {header!r}")

        conds = []
        for clause in clauses:
            if re.search(r"\bTHRU\b", clause, re.IGNORECASE):
                parts = re.split(r"\bTHRU\b", clause, flags=re.IGNORECASE, maxsplit=1)
                if len(parts) != 2:
                    raise UnsupportedCobolConstruct(f"WHEN ... THRU not in the expected format: {clause!r}")
                lo_text, hi_text = parts[0].strip(), parts[1].strip()
                try:
                    lo_py = cobol_expr_to_python(lo_text, decimal_scale=subject_scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                    hi_py = cobol_expr_to_python(hi_text, decimal_scale=subject_scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                except CobolExpressionError as e:
                    raise UnsupportedCobolConstruct(f"WHEN ... THRU bounds: {e}") from e
                subj_lo, lo_n = self._normalize_scale_pair_transpile(subject_py, lo_py)
                subj_hi, hi_n = self._normalize_scale_pair_transpile(subject_py, hi_py)
                conds.append(f"({subj_lo} >= {lo_n} and {subj_hi} <= {hi_n})")
            else:
                try:
                    value_py = cobol_expr_to_python(clause, decimal_scale=subject_scale, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
                except CobolExpressionError as e:
                    raise UnsupportedCobolConstruct(
                        f"EVALUATE WHEN clause not supported (only a single value, "
                        f"a THRU range, or a repeated WHEN with a shared body): "
                        f"{clause!r} -- {e}"
                    ) from e
                subj_n, value_n = self._normalize_scale_pair_transpile(subject_py, value_py)
                conds.append(f"({subj_n} == {value_n})")

        return "(" + " or ".join(conds) + ")"

    def _when_header_text(self, when):
        """Isolates the head of a WHEN clause (the value/condition, WITH
        all repeated 'WHEN' occurrences if present) from the statement
        body -- the same boundary-finding technique as for the
        PERFORM-VARYING header. Unlike before, the leading 'WHEN' is NOT
        stripped -- _when_value_condition() needs it to recognize
        repeated WHEN clauses."""
        full = _raw_text(when)
        if when.statements:
            body_start = when.statements[0].ctx.start.start
            istream = when.ctx.start.getInputStream()
            header = istream.getText(when.ctx.start.start, body_start - 1)
        else:
            header = full
        return header.strip()

    def _resolve_target(self, target_text):
        # Write access to a REDEFINES field is NOT supported (see
        # cobol_extract.extract_redefines_map -- derived READ-ONLY).
        # This must be checked BEFORE the generic expression parser,
        # otherwise the derived read expression would be incorrectly
        # inserted as the assignment target (invalid Python code instead
        # of a clear error).
        bare_name = re.sub(r"\s*\([^)]*\)\s*$", "", target_text.strip())  # strip a possible table index
        py_bare = self._py_name(bare_name)
        if py_bare in self.redefines_map:
            raise UnsupportedCobolConstruct(
                f"Write access to REDEFINES field '{target_text}' is not supported -- "
                f"REDEFINES is only derived READ-ONLY (see extract_redefines_map)"
            )
        try:
            return cobol_expr_to_python(target_text, decimal_scale=0, table_index_vars=self.table_index_vars, field_lengths=self.field_lengths, redefines_map=self.redefines_map, field_decimal_scales=self.field_decimal_scales, group_picx_fields=self.group_picx_fields)
        except CobolExpressionError as e:
            raise UnsupportedCobolConstruct(f"Assignment target could not be resolved: {e}") from e


def transpile_procedure_division(program, function_name, param_names, return_field_py,
                                  field_decimal_scales, table_index_vars=None, known_cobol_names=None,
                                  field_lengths=None, condition_name_map=None, table_occurs=None,
                                  redefines_map=None, group_picx_fields=None):
    """Automatically translates the PROCEDURE DIVISION of a parsed
    cobol-py program (from CobolParserRunner().analyze(...)) into a
    Python function definition (as a source-text string).

    field_decimal_scales: dict[python_field_name -> decimal_digits] --
    derivable from cobol_extract.py's extract_data_items()/
    extract_record_and_table_types() (PicField.decimal_digits per field).
    known_cobol_names: see CobolStatementTranspiler -- ALL COBOL names
    (including groups without their own PIC clause), for the truncation
    safety net.
    return_field_py: name of the Python field returned at the end.

    Raises UnsupportedCobolConstruct with the exact location of the error
    if ANY statement in the program is not covered -- NO partial
    translation, no silent omission of code."""
    pu = program.compilation_unit.program_unit
    pd = pu.procedure_division
    paragraphs = pd.root_paragraphs
    if not paragraphs and pd.sections:
        # The PROCEDURE DIVISION uses SECTIONs instead of direct
        # paragraphs (common in formally written/older COBOL, e.g. NIST
        # test programs) -- the entry point is then the first paragraph
        # of the first section. PERFORM <paragraph> already works across
        # sections (get_paragraph searches all sections); only the
        # selection of the entry point here had to follow suit.
        paragraphs = pd.sections[0].paragraphs
    if not paragraphs:
        raise UnsupportedCobolConstruct("No PROCEDURE DIVISION paragraphs found")

    transpiler = CobolStatementTranspiler(field_decimal_scales, table_index_vars=table_index_vars,
                                           known_cobol_names=known_cobol_names, field_lengths=field_lengths,
                                           condition_name_map=condition_name_map, table_occurs=table_occurs,
                                           redefines_map=redefines_map, group_picx_fields=group_picx_fields,
                                           param_names=param_names)
    # ONLY the first paragraph (the entry point) is executed directly --
    # further paragraphs are inserted ONLY where they are referenced via
    # PERFORM (see _perform_procedure), not automatically "fallen
    # through" in sequence. A program with no PERFORM call to a second
    # paragraph would accordingly never have it in the generated code --
    # this matches real COBOL behavior only for the case where every
    # subsequent paragraph is actually reached via PERFORM (plain
    # "fall-through" without PERFORM is NOT supported).
    transpiler.transpile_statements(paragraphs[0].statements)

    py_params = ", ".join(param_names)
    body = "\n".join(transpiler.lines) if transpiler.lines else "    pass"
    helper_defs = ""
    if transpiler.used_unstring:
        # Real, concretely callable implementations -- these are NOT
        # executed by the symbolic proof path (Z3 evaluates
        # unstring_before/-after directly as IndexOf/SubString, see
        # engine.py), but EVERY concrete Python call (fuzzing, concolic
        # execution, sandbox display code) needs these real definitions,
        # otherwise a NameError. The semantics are deliberately kept
        # identical to the Z3 evaluation (no match -> the whole string
        # resp. an empty string).
        helper_defs += (
            "def unstring_before(source, delim):\n"
            "    idx = source.find(delim)\n"
            "    return source if idx == -1 else source[:idx]\n\n"
            "def unstring_after(source, delim):\n"
            "    idx = source.find(delim)\n"
            "    return '' if idx == -1 else source[idx + len(delim):]\n\n"
        )
    if transpiler.used_char_at:
        # Same logic as above: engine.py evaluates char_at() symbolically
        # directly as SubString(s, i, 1), but the concrete fallback path
        # needs a real definition.
        helper_defs += (
            "def char_at(s, i):\n"
            "    return s[i:i + 1]\n\n"
        )
    if "is_numeric_string(" in body:
        # Comes from 'IS [NOT] NUMERIC' on PicX fields (see cobol_expr.py)
        # -- no separate usage flag needed, a direct text search in the
        # finished body suffices, since this function can never
        # accidentally occur as a substring of another identifier (the
        # parenthesis is part of the pattern).
        helper_defs += (
            "def is_numeric_string(s):\n"
            "    return s.isdigit()\n\n"
        )
    source = f"{helper_defs}def {function_name}({py_params}):\n{body}\n    return {return_field_py}\n"
    return source
