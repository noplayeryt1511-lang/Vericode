# -*- coding: utf-8 -*-
"""
COBOL expression parser: converts COBOL arithmetic/condition expressions
(as raw text, e.g. "WS-A * WS-B + 2" or "WS-A <= 5.00") into Python
expression strings that our SymbolicEvaluator (engine.py) understands
directly.

WHY RAW TEXT INSTEAD OF THE FULL cobol-py ASG TREE STRUCTURE: for
expressions, the ASG has a great many nested wrapper classes
(ArithmeticValueStmt -> plus_minuses -> MultDivs -> ...) that mirror
COBOL grammar precedence. A small, purpose-built tokenizer + Pratt
parser on the raw source text (available via
ctx.start.getInputStream().getText(...)) is more robust and easier to
verify than rebuilding every level of that ASG.

IMPORTANT, DELIBERATE LIMITATION regarding decimal scaling: COBOL
literals with a decimal point (e.g. "5.00") have no intrinsic scaling
in our system -- they must be brought to the same scale as the
surrounding computation (implicit decimal places as an integer
factor). This parser scales EVERY decimal literal in an expression
using a SINGLE decimal_scale (number of decimal places) supplied by
the caller -- it does NOT attempt to automatically reconcile different
scales within one expression (that would be true COBOL decimal
alignment, a separate problem NOT solved here). When in doubt, raise a
ParseError rather than silently produce an incorrectly scaled number.
"""

import re
import math


class CobolExpressionError(Exception):
    """The expression could not be (safely) translated to Python --
    raised deliberately instead of a silent mistranslation."""
    pass


class _Lit:
    """Marks a COBOL numeric literal that has NOT YET been scaled -- the
    decision whether it is treated additively (_scale_literal) or
    multiplicatively (_literal_as_ratio) is made by the respective call
    context (parse_arith_expr resp. parse_term/_combine_mult)."""
    __slots__ = ("raw",)

    def __init__(self, raw):
        self.raw = raw


_TOKEN_SPEC = [
    ("STR", r'"[^"]*"' + "|'[^']*'"),
    ("NUM", r"\d+[.,]\d+|\d+"),  # dot OR comma as decimal separator (DECIMAL-POINT IS COMMA)
    ("ID", r"[A-Za-z][A-Za-z0-9-]*(?:\s*\(\s*[A-Za-z0-9-]+\s*\))?"),  # incl. optional TABLE(INDEX)
    ("LE", r"<="), ("GE", r">="), ("NE", r"<>"),
    ("LT", r"<"), ("GT", r">"), ("EQ", r"="),
    ("LPAREN", r"\("), ("RPAREN", r"\)"),
    ("PLUS", r"\+"), ("MINUS", r"-"), ("STAR", r"\*"), ("SLASH", r"/"),
    ("WS", r"\s+"),
]
_TOKEN_RE = re.compile("|".join(f"(?P<{name}>{pattern})" for name, pattern in _TOKEN_SPEC))

_KEYWORDS = {"AND", "OR", "NOT", "OF", "IN", "IS", "EQUAL", "TO", "GREATER", "THAN", "LESS",
             "NUMERIC", "ALPHABETIC", "FUNCTION",
             "EQ", "NE", "LT", "GT", "LE", "GE"}  # abbreviated comparison operators as separate words
_SUPPORTED_FUNCTIONS = {"MAX", "MIN", "LENGTH"}
# COBOL "figurative constants" -- reserved words that denote fixed
# values, NOT identifiers. ZERO/ZEROS/ZEROES is supported (resolves to
# numeric 0); the string-related ones (SPACE, HIGH-VALUE, LOW-VALUE,
# QUOTE) are recognized but deliberately REJECTED rather than guessed --
# their correct length depends on the target field, which the
# expression parser does not know at this point.
_ZERO_CONSTANTS = {"ZERO", "ZEROS", "ZEROES"}
_UNSUPPORTED_FIGURATIVE_CONSTANTS = {"SPACE", "SPACES", "HIGH-VALUE", "HIGH-VALUES",
                                      "LOW-VALUE", "LOW-VALUES", "QUOTE", "QUOTES"}


def tokenize(text):
    tokens = []
    pos = 0
    while pos < len(text):
        m = _TOKEN_RE.match(text, pos)
        if not m:
            raise CobolExpressionError(f"Unknown character at position {pos}: {text[pos:pos+20]!r}")
        pos = m.end()
        kind = m.lastgroup
        value = m.group(kind)
        if kind == "WS":
            continue
        if kind == "ID" and value.upper() in _KEYWORDS:
            kind = value.upper()
        tokens.append((kind, value))
    tokens.append(("EOF", ""))
    return tokens


def cobol_name_to_python(name):
    """WS-TOTAL-AMOUNT -> ws_total_amount. TABLE(IDX) -> table[_idx_minus_1]
    is NOT resolved HERE (the 1-based->0-based index conversion happens
    in the statement transpiler, which knows the context) -- pure name
    normalization."""
    return name.strip().lower().replace("-", "_")


class ExpressionParser:
    """Recursive-descent parser with the operator precedence customary
    for COBOL: parentheses > * / > + - > comparison operators > NOT >
    AND > OR."""

    def __init__(self, tokens, decimal_scale=0, table_index_vars=None, field_lengths=None, redefines_map=None,
                 field_decimal_scales=None, group_picx_fields=None):
        self.tokens = tokens
        self.pos = 0
        self.decimal_scale = decimal_scale
        self.field_decimal_scales = field_decimal_scales or {}  # Python field name -> its OWN decimal digits (for correct scaling in mixed-scale multiplication)
        self.group_picx_fields = group_picx_fields or {}  # Python group name -> [child field names], ONLY for groups made up entirely of PicX subfields (for IS NUMERIC on group fields)
        self.table_index_vars = table_index_vars or {}  # COBOL index name -> Python expression (0-based)
        self.field_lengths = field_lengths or {}  # Python field name -> PicX.length, only needed for FUNCTION LENGTH
        self.redefines_map = redefines_map or {}  # Python field name -> derived read expression (REDEFINES)

    def peek(self):
        return self.tokens[self.pos]

    def advance(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect_end(self):
        if self.peek()[0] != "EOF":
            raise CobolExpressionError(f"Unexpected tokens at end: {self.tokens[self.pos:]}")

    # --- Conditions (for IF/UNTIL) -----------------------------------
    def parse_condition(self):
        node = self.parse_or()
        self.expect_end()
        return node

    def parse_or(self):
        left = self.parse_and()
        while self.peek()[0] == "OR":
            self.advance()
            right = self.parse_and()
            left = f"({left} or {right})"
        return left

    def parse_and(self):
        left = self.parse_not()
        while self.peek()[0] == "AND":
            self.advance()
            right = self.parse_not()
            left = f"({left} and {right})"
        return left

    def parse_not(self):
        if self.peek()[0] == "NOT":
            self.advance()
            return f"(not {self.parse_not()})"
        return self.parse_condition_atom()

    def parse_condition_atom(self):
        """Resolves the ambiguity of "(" -> parenthesized CONDITION (e.g.
        "(A > B) AND (C > D)") vs. "(" -> parenthesized ARITHMETIC
        subexpression (e.g. inside one side of a comparison): first try
        to parse a COMPLETE condition; if that lands cleanly on ")", it
        was a parenthesized condition. Otherwise, reset and instead parse
        it as an ordinary relation (whose operands may in turn contain
        parentheses for arithmetic, via parse_arith_expr/parse_factor)."""
        if self.peek()[0] == "LPAREN":
            saved_pos = self.pos
            self.advance()
            try:
                inner = self.parse_or()
                if self.peek()[0] == "RPAREN":
                    self.advance()
                    return f"({inner})"
            except CobolExpressionError:
                pass
            self.pos = saved_pos
        return self.parse_relation()

    _REL_OPS = {"LE": "<=", "GE": ">=", "NE": "!=", "LT": "<", "GT": ">", "EQ": "=="}
    _WORD_RELATION_STARTERS = {"EQUAL", "GREATER", "LESS", "NUMERIC", "ALPHABETIC"}

    def _scale_lookup_key(self, operand):
        """Extracts the base field name for the scale lookup in
        field_decimal_scales -- for a table access like
        'ws_item[(ws_i - 1)]' that is 'ws_item' (the table name itself
        carries the element scale from the PIC clause), not the whole
        indexed expression. This handles a table-element operand that
        was not covered by the plain field-name lookup, because the
        lookup logic only checked bare field names as an exact
        dictionary key. For a simple field name without brackets, the
        name is left unchanged.

        This also handles an OF-qualified field reference such as
        'INV-AMOUNT OF WS-INVOICE', which the expression transpiles to
        'ws_invoice.inv_amount' (dot notation for record access) --
        field_decimal_scales, however, only indexes the FIELD itself
        ('inv_amount'), not the full path. So any table index is
        stripped first, and THEN, if dot notation remains, only the
        part AFTER the last dot is taken."""
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_.]*)\[", operand)
        base = m.group(1) if m else operand
        if "." in base:
            base = base.rsplit(".", 1)[-1]
        return base

    def _normalize_scale_pair(self, left, right):
        """Brings two operands of a COMPARISON to a common scale, WHEN
        both are known, bare field names with different scales -- the
        same class of bug as the multiplication and ADD scaling issues
        elsewhere in this module, here for comparisons: 'TEMP2 > GRADES'
        with TEMP2 at one decimal digit and GRADES at two would otherwise
        compare the RAW, differently scaled integers directly (7.6 > 7.50
        would incorrectly evaluate as 76 > 750 = FALSE, even though the
        true statement is TRUE). The side with the LOWER scale is scaled
        up so both sides share the same scale -- for a plain comparison,
        unlike an assignment, there is no target field that would dictate
        the common scale."""
        left_scale = self.field_decimal_scales.get(self._scale_lookup_key(left))
        right_scale = self.field_decimal_scales.get(self._scale_lookup_key(right))
        if left_scale is None or right_scale is None or left_scale == right_scale:
            return left, right
        if left_scale < right_scale:
            return f"({left} * {10 ** (right_scale - left_scale)})", right
        return left, f"({right} * {10 ** (left_scale - right_scale)})"

    def parse_relation(self):
        left = self.parse_arith_expr()
        kind = self.peek()[0]
        if kind in self._REL_OPS:
            self.advance()
            right = self.parse_arith_expr()
            left_n, right_n = self._normalize_scale_pair(left, right)
            return f"({left_n} {self._REL_OPS[kind]} {right_n})"
        if kind == "IS":
            self.advance()
            negate = False
            if self.peek()[0] == "NOT":
                self.advance()
                negate = True
            return self._parse_word_relation(left, negate)
        if kind == "NOT":
            # Postfix NOT WITHOUT a preceding "IS" -- also valid COBOL
            # ("X NOT EQUAL TO Y", not only "X IS NOT EQUAL TO Y").
            self.advance()
            return self._parse_word_relation(left, negate=True)
        if kind in self._WORD_RELATION_STARTERS:
            # In COBOL, "IS" is OPTIONAL before EQUAL/GREATER/LESS/
            # NUMERIC/ALPHABETIC -- "X EQUAL TO Y" is just as valid as
            # "X IS EQUAL TO Y". Without this check, any IS-less
            # occurrence would fall through to here and be rejected with
            # a misleading message.
            return self._parse_word_relation(left, negate=False)
        raise CobolExpressionError(f"Expected a comparison operator, got: {self.peek()}")

    def _parse_word_relation(self, left, negate):
        """Word-based COBOL comparison operators ("EQUAL TO"/"GREATER
        THAN"/"LESS THAN") as well as class conditions
        ("NUMERIC"/"ALPHABETIC"), with optional negation (from "IS NOT
        ..." or bare "NOT ..."). NUMERIC: for a known PicX field (in
        self.field_lengths), a REAL character-by-character check via Z3
        regex (see engine.py: is_numeric_string); otherwise (PicField --
        our model only allows numeric content there anyway) trivially
        TRUE. ALPHABETIC remains unsupported (would need the same regex
        technique again for letters, not implemented)."""
        kind = self.peek()[0]
        if kind in self._REL_OPS:
            # Abbreviated form AFTER "IS"/"NOT" ("IS EQ"/"IS NE"/...) --
            # the same abbreviations that are also recognized directly as
            # an operator WITHOUT "IS" (see parse_relation), here
            # additionally allowed after "IS"/"NOT".
            self.advance()
            right = self.parse_arith_expr()
            op = self._REL_OPS[kind]
            if negate:
                op = {"==": "!=", "!=": "==", "<": ">=", ">=": "<", ">": "<=", "<=": ">"}[op]
            left_n, right_n = self._normalize_scale_pair(left, right)
            return f"({left_n} {op} {right_n})"
        if kind == "NUMERIC":
            self.advance()
            if left in self.field_lengths:
                cond = f"is_numeric_string({left})"
            elif left in self.group_picx_fields:
                # Group field made up ENTIRELY of PicX subfields: "the
                # concatenated byte sequence is purely numeric" is
                # equivalent to "EVERY subfield individually is purely
                # numeric" (concatenating two digit sequences again
                # yields a digit sequence, and vice versa) -- no new
                # concept needed, just an AND of the existing single-field
                # check. Applicable ONLY to pure PicX groups (see how
                # group_picx_fields is built).
                children = self.group_picx_fields[left]
                cond = "(" + " and ".join(f"is_numeric_string({left}.{c})" for c in children) + ")"
            else:
                cond = "True"  # PicField: our model allows only numeric content there anyway
            return f"(not {cond})" if negate else f"({cond})"
        if kind == "ALPHABETIC":
            self.advance()
            raise CobolExpressionError("'[IS] [NOT] ALPHABETIC' is not supported.")
        if kind == "EQUAL":
            self.advance()
            if self.peek()[0] != "TO":
                raise CobolExpressionError(f"'EQUAL' expects 'TO', got: {self.peek()}")
            self.advance()
            right = self.parse_arith_expr()
            left_n, right_n = self._normalize_scale_pair(left, right)
            return f"({left_n} != {right_n})" if negate else f"({left_n} == {right_n})"
        if kind == "GREATER":
            self.advance()
            if self.peek()[0] != "THAN":
                raise CobolExpressionError(f"'GREATER' expects 'THAN', got: {self.peek()}")
            self.advance()
            right = self.parse_arith_expr()
            left_n, right_n = self._normalize_scale_pair(left, right)
            return f"({left_n} <= {right_n})" if negate else f"({left_n} > {right_n})"
        if kind == "LESS":
            self.advance()
            if self.peek()[0] != "THAN":
                raise CobolExpressionError(f"'LESS' expects 'THAN', got: {self.peek()}")
            self.advance()
            right = self.parse_arith_expr()
            left_n, right_n = self._normalize_scale_pair(left, right)
            return f"({left_n} >= {right_n})" if negate else f"({left_n} < {right_n})"
        raise CobolExpressionError(f"Unexpected token after IS/NOT: {self.peek()}")

    # --- Arithmetic (for COMPUTE/ADD/SUBTRACT/MOVE) --------------------
    # IMPORTANT DISTINCTION: a literal that is ADDED/SUBTRACTED (e.g.
    # "ADD 5.00 TO WS-TOTAL") represents an amount at the SAME scale as
    # the target field -> it is scaled up directly (_scale_literal). A
    # literal that is MULTIPLIED/DIVIDED (e.g. "* 1.5", "* 10") is a
    # DIMENSIONLESS RATIO (a rate/factor, not an amount of its own) -- it
    # is applied as a fraction (numerator // denominator) to the OTHER
    # operand, rather than being scaled itself. This is exactly the
    # pattern that must be handled ("* 3 // 2" instead of "* 150") -- the
    # transpiler must make this distinction automatically, otherwise
    # incorrectly scaled results occur (e.g. "WS-INC * 10" being
    # incorrectly translated to "ws_inc * 1000").
    def parse_arith_expr(self):
        left = self.parse_term()
        while self.peek()[0] in ("PLUS", "MINUS"):
            op_kind, _ = self.advance()
            left = self._as_expr(left)
            right = self._as_expr(self.parse_term())
            left = f"({left} + {right})" if op_kind == "PLUS" else f"({left} - {right})"
        return self._as_expr(left)

    def parse_term(self):
        left = self.parse_factor()
        while self.peek()[0] in ("STAR", "SLASH"):
            op_kind, _ = self.advance()
            right = self.parse_factor()
            left = self._combine_mult(left, op_kind, right)
        return left

    def _combine_mult(self, left, op_kind, right):
        left_lit = isinstance(left, _Lit)
        right_lit = isinstance(right, _Lit)
        if left_lit and right_lit:
            ln, ld = self._literal_as_ratio(left.raw)
            rn, rd = self._literal_as_ratio(right.raw)
            if op_kind == "STAR":
                num, den = ln * rn, ld * rd
            else:
                num, den = ln * rd, ld * rn
            return str(num // den) if den != 0 else "0"
        if right_lit:
            num, den = self._literal_as_ratio(right.raw)
            other = self._as_expr(left)
            return self._scaled_literal_combine(other, op_kind, num, den)
        if left_lit:
            num, den = self._literal_as_ratio(left.raw)
            other = self._as_expr(right)
            if op_kind == "STAR":
                return self._scaled_literal_combine(other, op_kind, num, den)
            raise CobolExpressionError(
                f"A literal DIVIDED BY an expression ('{left.raw} / ...') is not "
                f"supported (unusual COBOL pattern, cannot be resolved automatically)."
            )
        return self._scaled_field_mult_combine(left, op_kind, right)

    def _scaled_field_mult_combine(self, left, op_kind, right):
        """Multiplication/division of two NON-literal operands (e.g. two
        fields like 'STD-HOURS * RATE-OF-PAY'). Both operands are
        ALREADY integers scaled up to their own scale -- a plain
        multiplication WITHOUT correction also multiplies the scaling
        factors together (scale1 * scale2 instead of the target scale),
        which makes the result too large by a factor of
        10^(scale1+scale2-target_scale) (e.g.: 37.50 * 15.00 would come
        out as 56250.00 instead of 562.50 -- a factor of 100 too large).

        The same class of bug (after multiplication, ADD/SUBTRACT,
        comparisons, MOVE, EVALUATE) was previously also missing its
        correction for SLASH (division): 'DIVIDE WS-DIVISOR INTO
        WS-VALUE' with differing numbers of decimal digits produced 50
        instead of the correct 500 (a factor of 10 too small). Division
        scales differently from multiplication: true value =
        (dividend_raw/divisor_raw) * 10^(divisor_scale - dividend_scale);
        brought to the target scale: exponent = target_scale +
        divisor_scale - dividend_scale.

        The correction is applied ONLY when we reliably know the scale of
        BOTH operands (plain field names in field_decimal_scales) -- for
        complex subexpressions, the previous, documented-as-incomplete
        behavior is left unchanged (no guessing, no worsening of an
        already-known edge case)."""
        left_key, right_key = self._scale_lookup_key(left), self._scale_lookup_key(right)
        if left_key not in self.field_decimal_scales or right_key not in self.field_decimal_scales:
            return f"({left} * {right})" if op_kind == "STAR" else f"({left} // {right})"
        left_scale = self.field_decimal_scales[left_key]
        right_scale = self.field_decimal_scales[right_key]
        if op_kind == "STAR":
            exponent = self.decimal_scale - left_scale - right_scale
            if exponent >= 0:
                return f"({left} * {right} * {10 ** exponent})" if exponent else f"({left} * {right})"
            return f"({left} * {right} // {10 ** -exponent})"
        # SLASH: left is the dividend, right the divisor (the call site
        # in _build_combined_expr already ensures that for "A INTO B" the
        # order arrives swapped accordingly).
        exponent = self.decimal_scale + right_scale - left_scale
        if exponent >= 0:
            factor = 10 ** exponent
            return f"({left} * {factor} // {right})" if factor != 1 else f"({left} // {right})"
        return f"({left} // ({right} * {10 ** -exponent}))"

    def _scaled_literal_combine(self, other, op_kind, num, den):
        """Combines an expression (other, already given as Python text)
        with a literal ratio num/den, TAKING INTO ACCOUNT that 'other' is
        not necessarily already at the target scale (e.g. a scale-less
        integer field like a plain quantity, multiplied by a literal that
        ITSELF carries the target scale, such as 'FS-DEP * 189.59' for a
        2-decimal-digit target field). Derived general formula:

            scaled_result = other_raw * num * 10^(target_scale - other_scale) // den

        (for STAR; for SLASH analogous with num/den swapped). For the
        COMMON case where 'other' is already at the target scale (e.g. a
        monetary amount multiplied by a dimensionless rate),
        other_scale == target_scale, so the exponent is 0 -- identical to
        the previous (correct) behavior, hence backward compatible."""
        other_scale = self.field_decimal_scales.get(other, self.decimal_scale)
        exponent = self.decimal_scale - other_scale
        scale_factor = 10 ** exponent if exponent >= 0 else None
        if op_kind == "STAR":
            eff_num = num * scale_factor if scale_factor is not None else num
            eff_den = den if scale_factor is not None else den * (10 ** -exponent)
            return f"({other} * {eff_num} // {eff_den})" if eff_den != 1 else f"({other} * {eff_num})"
        eff_num = den * scale_factor if scale_factor is not None else den
        eff_den = num if scale_factor is not None else num * (10 ** -exponent)
        return f"({other} * {eff_num} // {eff_den})" if eff_den != 1 else f"({other} * {eff_num})"

    def _as_expr(self, x):
        """Resolves a possibly still-unresolved literal (additive
        context) into a finished Python expression; an already-finished
        expression (string) is left unchanged."""
        if isinstance(x, _Lit):
            return self._scale_literal(x.raw)
        return x

    def _literal_as_ratio(self, raw):
        """Decomposes a COBOL numeric literal into a reduced fraction
        (numerator, denominator) -- '1.5' -> (3, 2), '0.10' -> (1, 10),
        '2' -> (2, 1). This is the correct representation for a
        DIMENSIONLESS ratio (multiplier/rate), as opposed to
        _scale_literal (additive context, an amount at the SAME scale as
        the target field). Both dot AND comma are accepted as the decimal
        separator (DECIMAL-POINT IS COMMA -- common internationally, e.g.
        in Brazilian COBOL)."""
        if "." in raw or "," in raw:
            int_part, dec_part = re.split(r"[.,]", raw)
            numerator = int(int_part + dec_part)
            denominator = 10 ** len(dec_part)
        else:
            numerator, denominator = int(raw), 1
        g = math.gcd(numerator, denominator) or 1
        return numerator // g, denominator // g

    def _parse_function_call(self):
        """COBOL 'FUNCTION NAME(arg1 arg2 ...)' -- arguments are
        SPACE-separated, not comma-separated (unlike Python/most other
        languages). Special case: for EXACTLY ONE argument without a
        space (e.g. 'LENGTH(WS-NAME)'), the tokenizer already applies its
        TABLE(INDEX) pattern and returns function-name+paren+argument as
        a SINGLE ID token -- this must be manually split apart again
        here."""
        self.advance()  # consume 'FUNCTION'
        kind, raw = self.peek()
        if kind != "ID":
            raise CobolExpressionError(f"Expected a function name after FUNCTION, got: {(kind, raw)}")
        self.advance()

        m = re.match(r"^([A-Za-z][A-Za-z0-9-]*)\s*\(\s*([A-Za-z0-9-]+)\s*\)$", raw)
        if m:
            # Single-argument special case (see docstring): already fully contained in the token
            func_name, arg_names = m.group(1).upper(), [m.group(2)]
            args = [self._resolve_plain_identifier(a) for a in arg_names]
        else:
            func_name = raw.upper()
            if self.peek()[0] != "LPAREN":
                raise CobolExpressionError(f"FUNCTION {func_name}: expected '(', got {self.peek()}")
            self.advance()
            args = []
            while self.peek()[0] != "RPAREN":
                args.append(self.parse_arith_expr())
            self.advance()  # ')'

        if func_name not in _SUPPORTED_FUNCTIONS:
            raise CobolExpressionError(
                f"FUNCTION {func_name} is not supported (only MAX, MIN, LENGTH)"
            )
        if func_name in ("MAX", "MIN"):
            if len(args) < 2:
                raise CobolExpressionError(f"FUNCTION {func_name} needs at least 2 arguments")
            return f"{func_name.lower()}({', '.join(args)})"
        # LENGTH: either a plain PicX field name (length known from
        # field_lengths at transpile time) OR a string LITERAL directly
        # (e.g. 'FUNCTION LENGTH("ABC")') -- its length is likewise
        # trivially known at transpile time (character count of the
        # literal), no runtime computation needed.
        if len(args) != 1:
            raise CobolExpressionError("FUNCTION LENGTH expects exactly ONE argument")
        arg_py = args[0]
        if len(arg_py) >= 2 and arg_py[0] == arg_py[-1] and arg_py[0] in ("'", '"'):
            return str(len(arg_py) - 2)  # don't count the quote characters themselves
        if arg_py not in self.field_lengths:
            raise CobolExpressionError(
                f"FUNCTION LENGTH: '{arg_py}' is not a known PicX field with a known length "
                f"and not a string literal"
            )
        return str(self.field_lengths[arg_py])

    def parse_factor(self):
        kind, value = self.peek()
        if kind == "FUNCTION":
            return self._parse_function_call()
        if kind == "MINUS":
            self.advance()
            inner = self._as_expr(self.parse_factor())  # negated literals: resolved additively (a known, documented simplification)
            return f"(-{inner})"
        if kind == "LPAREN":
            self.advance()
            inner = self.parse_arith_expr()  # already returns a finished string
            if self.peek()[0] != "RPAREN":
                raise CobolExpressionError("Missing closing parenthesis")
            self.advance()
            return f"({inner})"
        if kind == "NUM":
            self.advance()
            return _Lit(value)  # NOT YET scaled -- the context (additive/multiplicative) decides
        if kind == "STR":
            self.advance()
            return repr(value[1:-1])  # strip COBOL quotes, render as a Python string literal
        if kind == "ID":
            self.advance()
            upper = value.upper()
            if upper in _ZERO_CONSTANTS:
                return _Lit("0")  # figurative constant -- numeric 0, treated additively/multiplicatively like a literal
            if upper in _UNSUPPORTED_FIGURATIVE_CONSTANTS:
                raise CobolExpressionError(
                    f"Figurative constant '{value}' is not supported (its correct length "
                    f"depends on the target field, which is not known here) -- deliberately rejected rather than guessed."
                )
            return self._resolve_identifier(value)
        raise CobolExpressionError(f"Unexpected token in expression: {(kind, value)}")

    def _scale_literal(self, raw):
        if "." in raw or "," in raw:
            int_part, dec_part = re.split(r"[.,]", raw)
            if len(dec_part) > self.decimal_scale:
                raise CobolExpressionError(
                    f"Decimal literal '{raw}' has {len(dec_part)} decimal places, "
                    f"but the target field only has {self.decimal_scale} -- this would lose precision "
                    f"and cannot be resolved automatically."
                )
            dec_part_padded = dec_part.ljust(self.decimal_scale, "0")
            return str(int(int_part + dec_part_padded))
        # integer literal without a point -> scale up to decimal_scale
        return str(int(raw) * (10 ** self.decimal_scale))


    def _resolve_identifier(self, raw):
        # Qualified name: "FIELD OF GROUP" or "FIELD OF TABLE(INDEX)"
        # -- COBOL writes this "back to front", Python needs
        # "group.field" resp. "table[index].field".
        if self.peek()[0] in ("OF", "IN"):
            self.advance()
            base_kind, base_raw = self.advance()
            if base_kind != "ID":
                raise CobolExpressionError(f"Expected an identifier after OF/IN, got: {(base_kind, base_raw)}")
            base_py = self._resolve_plain_identifier(base_raw)
            field_py = cobol_name_to_python(raw)
            return f"{base_py}.{field_py}"
        return self._resolve_plain_identifier(raw)

    def _resolve_plain_identifier(self, raw):
        # Recognize the TABLE(INDEX) pattern
        m = re.match(r"^([A-Za-z][A-Za-z0-9-]*)\s*\(\s*([A-Za-z0-9-]+)\s*\)$", raw)
        if m:
            table_name, index_name = m.group(1), m.group(2)
            py_table = cobol_name_to_python(table_name)
            if index_name.isdigit():
                py_index = str(int(index_name) - 1)  # COBOL 1-based -> Python 0-based
            elif index_name in self.table_index_vars:
                py_index = self.table_index_vars[index_name]
            else:
                py_index = f"({cobol_name_to_python(index_name)} - 1)"  # assumption: the index variable is COBOL 1-based
            return f"{py_table}[{py_index}]"
        py_name = cobol_name_to_python(raw)
        if py_name in self.redefines_map:
            # REDEFINES field -- substitute the derived read expression
            # (see cobol_extract.extract_redefines_map). This is already
            # a finished, parenthesized Python expression, so return it
            # directly instead of running it through cobol_name_to_python again.
            return self.redefines_map[py_name]
        return py_name


def cobol_expr_to_python(text, decimal_scale=0, table_index_vars=None, field_lengths=None, redefines_map=None,
                          field_decimal_scales=None, group_picx_fields=None):
    tokens = tokenize(text)
    parser = ExpressionParser(tokens, decimal_scale=decimal_scale, table_index_vars=table_index_vars,
                               field_lengths=field_lengths, redefines_map=redefines_map,
                               field_decimal_scales=field_decimal_scales, group_picx_fields=group_picx_fields)
    result = parser.parse_arith_expr()
    parser.expect_end()
    return result


def cobol_condition_to_python(text, decimal_scale=0, table_index_vars=None, field_lengths=None, redefines_map=None,
                               field_decimal_scales=None, group_picx_fields=None):
    tokens = tokenize(text)
    parser = ExpressionParser(tokens, decimal_scale=decimal_scale, table_index_vars=table_index_vars,
                               field_lengths=field_lengths, redefines_map=redefines_map,
                               field_decimal_scales=field_decimal_scales, group_picx_fields=group_picx_fields)
    return parser.parse_condition()
