# -*- coding: utf-8 -*-
"""
Go frontend for VeriCode: the third target language besides Java/C#.

Same architecture as java_bridge.py/csharp_bridge.py: Go -> our
existing, supported Python subset -> engine.py UNCHANGED. Market
research named Go as a common modern migration target (simpler syntax
than Java/C#, no inheritance model -- fits well with our already flat
record model).

Uses `tree-sitter` + `tree-sitter-go` (PyPI) -- the same reputable,
established library as for C#, of no questionable origin.

SUPPORTED SUBSET: identical to java_bridge.py/csharp_bridge.py --
int parameters/return, string, arrays (Go: []int slices), local
variables (both var AND :=), if/else if/else, for loops with constant
bounds (Go: 'for i := 0; i < n; i++' AND the simpler 'for cond {}'
form, which plays the role of while in Go), switch (Go needs NO
break -- no implicit fall-through as in Java/C#, so it's simpler),
records via structs with public (capitalized) fields,
+=/-=/*=//= .

IMPORTANT difference from Java/C#: Go has NO ternary operator -- this
is deliberately NOT emulated here (simulating a?b:c via if/else would
no longer be an expression but a statement, which does not fit our
expression model)."""

import tree_sitter_go as tsgo
from tree_sitter import Language, Parser

_LANGUAGE = Language(tsgo.language())
_INT_TYPES = {"int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64"}


class UnsupportedGoConstruct(Exception):
    """A Go construct that this bridge does not (yet) cover -- deliberately
    NOT guessed at or ignored."""
    pass


def _text(node):
    return node.text.decode("utf-8")


def _unwrap_expr_list(node):
    """Go always wraps assignment/return values in an expression_list,
    even for exactly one value. For multiple values (a, b := f()) we
    reject -- only a single value is supported."""
    if node.type != "expression_list":
        return node
    if len(node.named_children) != 1:
        raise UnsupportedGoConstruct(
            f"Only single values are supported (no multi-value assignment/return "
            f"'a, b := ...'): {_text(node)!r}"
        )
    return node.named_children[0]


class GoToPythonBridge:
    def __init__(self, param_rename=None, field_rename=None):
        self.lines = []
        self.indent = 1
        self.param_rename = param_rename or {}
        self.field_rename = field_rename or {}

    def _emit(self, line):
        self.lines.append("    " * self.indent + line)

    def transpile_function(self, fn):
        params_node = fn.child_by_field_name("parameters")
        for param in params_node.named_children:
            type_node = param.child_by_field_name("type")
            is_primitive = type_node.type == "type_identifier" and _text(type_node) in _INT_TYPES
            is_string = type_node.type == "type_identifier" and _text(type_node) == "string"
            is_slice = (type_node.type == "slice_type" and type_node.child_by_field_name("element") is not None
                        and type_node.child_by_field_name("element").type == "type_identifier"
                        and _text(type_node.child_by_field_name("element")) in _INT_TYPES)
            is_record = type_node.type == "type_identifier" and not is_primitive and not is_string
            if not (is_primitive or is_string or is_slice or is_record):
                raise UnsupportedGoConstruct(
                    f"Parameter '{_text(param.child_by_field_name('name'))}' has an "
                    f"unsupported type: {_text(type_node)} (only int variants, string, []int, or structs)"
                )
        result_node = fn.child_by_field_name("result")
        is_string_return = result_node is not None and result_node.type == "type_identifier" and _text(result_node) == "string"
        if result_node is not None and not is_string_return and not (
                result_node.type == "type_identifier" and _text(result_node) in _INT_TYPES):
            raise UnsupportedGoConstruct(
                f"Only a primitive int return type or string is supported, got: {_text(result_node)}"
            )

        body = fn.child_by_field_name("body")
        stmt_list = body.named_children[0] if body.named_children else None
        self.transpile_block(stmt_list.named_children if stmt_list else [])

    def transpile_block(self, statements):
        if not statements:
            self._emit("pass")
            return
        i = 0
        while i < len(statements):
            stmt = statements[i]
            nxt = statements[i + 1] if i + 1 < len(statements) else None
            # Go special case: 'var i int = 0' (or 'var i int' + a later
            # assignment of 0) followed by 'for cond { ...; i++ }' -- Go's
            # only loop form without its own init/update ('for cond {}')
            # plays the role of while in Go. See _try_emit_counted_for_cond_only.
            if (nxt is not None and nxt.type == "for_statement"
                    and stmt.type in ("short_var_declaration", "var_declaration")):
                info = self._extract_simple_int_init(stmt)
                if info is not None:
                    loop_var, start = info
                    if self._try_emit_counted_while(loop_var, start, nxt):
                        i += 2
                        continue
            self.transpile_statement(stmt)
            i += 1

    def _extract_simple_int_init(self, stmt):
        """Returns (variable_name, start_value) if stmt is a simple
        integer initialization ('i := 0' or 'var i int = 0'),
        otherwise None."""
        if stmt.type == "short_var_declaration":
            left = _unwrap_expr_list(stmt.child_by_field_name("left"))
            right = _unwrap_expr_list(stmt.child_by_field_name("right"))
            if left.type == "identifier" and right.type == "int_literal":
                return _text(left), int(_text(right))
        return None

    def _try_emit_counted_while(self, loop_var, start, for_stmt):
        """Recognizes Go's 'for COND { ...; i++/i--; }' form (without its
        own init/update in the for clause -- this is Go's equivalent of
        a while loop) and translates it to 'for i in range(...)', PROVIDED
        COND is a simple comparison against a constant and the last
        statement in the body is 'i++'/'i--'. Returns False (not an
        error) when the pattern does not match."""
        clause_children = [c for c in for_stmt.children if c.type not in ("for", "block")]
        if len(clause_children) != 1 or clause_children[0].type != "binary_expression":
            return False  # has a real for_clause (with its own init) -- not this pattern
        cond = clause_children[0]
        cond_left = cond.child_by_field_name("left")
        cond_right = cond.child_by_field_name("right")
        cond_op = _text(cond.child_by_field_name("operator"))
        if not (cond_left.type == "identifier" and _text(cond_left) == loop_var
                and cond_right.type == "int_literal" and cond_op in ("<", "<=", ">", ">=")):
            return False
        bound = int(_text(cond_right))

        body_node = for_stmt.child_by_field_name("body")
        body_stmt_list = body_node.named_children[0] if body_node.named_children else None
        body = body_stmt_list.named_children if body_stmt_list else []
        if not body:
            return False
        last = body[-1]
        if last.type not in ("inc_statement", "dec_statement"):
            return False
        operand = last.named_children[0]
        if not (operand.type == "identifier" and _text(operand) == loop_var):
            return False
        step = 1 if last.type == "inc_statement" else -1

        if step == 1:
            if cond_op not in ("<", "<="):
                return False
            stop = bound if cond_op == "<" else bound + 1
        else:
            if cond_op not in (">", ">="):
                return False
            stop = bound if cond_op == ">" else bound - 1

        self._emit(f"for {loop_var} in range({start}, {stop}, {step}):")
        self.indent += 1
        self.transpile_block(body[:-1])
        self.indent -= 1
        return True

    def transpile_statement(self, stmt):
        handler = getattr(self, f"_stmt_{stmt.type}", None)
        if handler is None:
            raise UnsupportedGoConstruct(f"Unsupported Go statement: {stmt.type}")
        handler(stmt)

    # --- Variable declaration ('var x int' or 'var x int = 5' or 'x := 5') ---
    def _stmt_var_declaration(self, stmt):
        for var_spec in stmt.named_children:
            name = _text(var_spec.child_by_field_name("name"))
            value_node = var_spec.child_by_field_name("value")
            if value_node is not None:
                val = self.transpile_expr(_unwrap_expr_list(value_node) if value_node.type == "expression_list" else value_node)
                self._emit(f"{name} = {val}")
            # without an initializer: Go enforces "definite assignment" via
            # the respective zero value (0 for numbers, "" for string) --
            # our engine likewise requires an EXPLICIT value before use
            # (see the has_returned fix), so we set it explicitly instead
            # of leaving it out. IMPORTANT: check the type -- a mistaken
            # '= 0' for 'var r string' produces a real Z3 sort conflict
            # (int vs. string), not a Python error that would surface immediately.
            else:
                type_node = var_spec.child_by_field_name("type")
                if type_node is not None and type_node.type == "type_identifier" and _text(type_node) == "string":
                    self._emit(f'{name} = ""')
                else:
                    self._emit(f"{name} = 0")

    def _stmt_short_var_declaration(self, stmt):
        left = _unwrap_expr_list(stmt.child_by_field_name("left"))
        right = _unwrap_expr_list(stmt.child_by_field_name("right"))
        if left.type != "identifier":
            raise UnsupportedGoConstruct(f"Only a simple short declaration 'x := ...' is supported: {_text(stmt)!r}")
        val = self.transpile_expr(right)
        self._emit(f"{_text(left)} = {val}")

    # --- Assignment ---------------------------------------------------------
    _COMPOUND_OPS = {"+=": "+", "-=": "-", "*=": "*", "/=": "//", "%=": "%"}

    def _stmt_assignment_statement(self, stmt):
        left = _unwrap_expr_list(stmt.child_by_field_name("left"))
        right = _unwrap_expr_list(stmt.child_by_field_name("right"))
        op_nodes = [c for c in stmt.children if c.type in ("=",) or c.type in self._COMPOUND_OPS]
        op = op_nodes[0].type if op_nodes else "="
        target = self.transpile_expr(left)
        val = self.transpile_expr(right)
        if op == "=":
            self._emit(f"{target} = {val}")
        elif op in self._COMPOUND_OPS:
            self._emit(f"{target} = ({target} {self._COMPOUND_OPS[op]} {val})")
        else:
            raise UnsupportedGoConstruct(f"Assignment operator not supported: '{op}'")

    def _stmt_inc_statement(self, stmt):
        operand = self.transpile_expr(stmt.named_children[0])
        self._emit(f"{operand} = ({operand} + 1)")

    def _stmt_dec_statement(self, stmt):
        operand = self.transpile_expr(stmt.named_children[0])
        self._emit(f"{operand} = ({operand} - 1)")

    # --- IF/ELSE -------------------------------------------------------
    def _stmt_if_statement(self, stmt):
        cond = self.transpile_expr(stmt.child_by_field_name("condition"))
        self._emit(f"if {cond}:")
        self.indent += 1
        self._transpile_nested_block(stmt.child_by_field_name("consequence"))
        self.indent -= 1
        alt = stmt.child_by_field_name("alternative")
        if alt is not None:
            if alt.type == "if_statement":
                self._emit_elif(alt)
            else:
                self._emit("else:")
                self.indent += 1
                self._transpile_nested_block(alt)
                self.indent -= 1

    def _emit_elif(self, stmt):
        cond = self.transpile_expr(stmt.child_by_field_name("condition"))
        self._emit(f"elif {cond}:")
        self.indent += 1
        self._transpile_nested_block(stmt.child_by_field_name("consequence"))
        self.indent -= 1
        alt = stmt.child_by_field_name("alternative")
        if alt is not None:
            if alt.type == "if_statement":
                self._emit_elif(alt)
            else:
                self._emit("else:")
                self.indent += 1
                self._transpile_nested_block(alt)
                self.indent -= 1

    def _transpile_nested_block(self, node):
        if node.type == "block":
            stmt_list = node.named_children[0] if node.named_children else None
            self.transpile_block(stmt_list.named_children if stmt_list else [])
        else:
            self.transpile_statement(node)

    # --- FOR loop with its own init/update (classic form) -------------
    def _stmt_for_statement(self, stmt):
        clause = [c for c in stmt.children if c.type == "for_clause"]
        if not clause:
            raise UnsupportedGoConstruct(
                "'for cond {}' without a preceding short declaration is not supported "
                "(see transpile_block -- must immediately follow 'i := START')"
            )
        fc = clause[0]
        init = fc.child_by_field_name("initializer")
        cond = fc.child_by_field_name("condition")
        update = fc.child_by_field_name("update")
        if init is None or init.type != "short_var_declaration":
            raise UnsupportedGoConstruct("FOR init must be a simple short declaration 'i := 0'")
        info = self._extract_simple_int_init(init)
        if info is None:
            raise UnsupportedGoConstruct("FOR start value must be a constant integer literal")
        loop_var, start = info

        if cond is None or cond.type != "binary_expression":
            raise UnsupportedGoConstruct(f"FOR condition must be a simple comparison, e.g. '{loop_var} < N'")
        cond_left = cond.child_by_field_name("left")
        cond_right = cond.child_by_field_name("right")
        cond_op = _text(cond.child_by_field_name("operator"))
        if not (cond_left.type == "identifier" and _text(cond_left) == loop_var and cond_right.type == "int_literal"
                and cond_op in ("<", "<=", ">", ">=")):
            raise UnsupportedGoConstruct(f"FOR condition must be '{loop_var} (< | <= | > | >=) <constant>'")
        bound = int(_text(cond_right))

        if update is None or update.type not in ("inc_statement", "dec_statement"):
            raise UnsupportedGoConstruct(f"FOR update must be '{loop_var}++' or '{loop_var}--'")
        upd_operand = update.named_children[0]
        if not (upd_operand.type == "identifier" and _text(upd_operand) == loop_var):
            raise UnsupportedGoConstruct(f"FOR update must act on '{loop_var}'")
        step = 1 if update.type == "inc_statement" else -1

        if step == 1:
            if cond_op not in ("<", "<="):
                raise UnsupportedGoConstruct(f"'{loop_var}++' needs '<' or '<=', not '{cond_op}'")
            stop = bound if cond_op == "<" else bound + 1
        else:
            if cond_op not in (">", ">="):
                raise UnsupportedGoConstruct(f"'{loop_var}--' needs '>' or '>=', not '{cond_op}'")
            stop = bound if cond_op == ">" else bound - 1

        self._emit(f"for {loop_var} in range({start}, {stop}, {step}):")
        self.indent += 1
        self._transpile_nested_block(stmt.child_by_field_name("body"))
        self.indent -= 1

    # --- SWITCH (Go needs NO break -- no fall-through by default) ----
    def _stmt_expression_switch_statement(self, stmt):
        subject = self.transpile_expr(stmt.child_by_field_name("value"))
        first = True
        default_body = None
        for case in stmt.named_children:
            if case.type == "expression_case":
                values_node = case.child_by_field_name("value")
                # expression_case does not reliably have field names for
                # value/body across all tree-sitter-go versions -- go via
                # child types instead: 'expression_list' + 'statement_list'
                expr_list = [c for c in case.named_children if c.type == "expression_list"][0]
                stmt_lists = [c for c in case.named_children if c.type == "statement_list"]
                body = stmt_lists[0].named_children if stmt_lists else []
                values = [self.transpile_expr(v) for v in expr_list.named_children]
                cond = " or ".join(f"({subject} == {v})" for v in values)
                self._emit(f"{'if' if first else 'elif'} {cond}:")
                first = False
                self.indent += 1
                self.transpile_block(list(body))
                self.indent -= 1
            elif case.type == "default_case":
                stmt_lists = [c for c in case.named_children if c.type == "statement_list"]
                default_body = stmt_lists[0].named_children if stmt_lists else []

        if default_body is not None:
            self._emit("else:")
            self.indent += 1
            self.transpile_block(list(default_body))
            self.indent -= 1
        elif first:
            raise UnsupportedGoConstruct("SWITCH without any case/default")

    # --- RETURN --------------------------------------------------------
    def _stmt_return_statement(self, stmt):
        if not stmt.named_children:
            raise UnsupportedGoConstruct("'return' without a value is not supported")
        val_node = _unwrap_expr_list(stmt.named_children[0])
        val = self.transpile_expr(val_node)
        self._emit(f"return {val}")

    # --- Expressions -----------------------------------------------------
    _BIN_OPS = {"+": "+", "-": "-", "*": "*", "/": "//", "%": "%",
                "==": "==", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">=",
                "&&": "and", "||": "or"}

    def transpile_expr(self, node):
        if node.type == "int_literal":
            return _text(node)
        if node.type == "interpreted_string_literal" or node.type == "raw_string_literal":
            return _text(node)  # Go keeps quotes like Python -- can be used as-is
        if node.type == "identifier":
            name = _text(node)
            return self.param_rename.get(name, name)
        if node.type == "selector_expression":
            base = self.transpile_expr(node.child_by_field_name("operand"))
            field = _text(node.child_by_field_name("field"))
            field = self.field_rename.get(field, field)
            return f"{base}.{field}"
        if node.type == "index_expression":
            base = self.transpile_expr(node.child_by_field_name("operand"))
            index_py = self.transpile_expr(node.child_by_field_name("index"))
            return f"{base}[{index_py}]"
        if node.type == "binary_expression":
            op = _text(node.child_by_field_name("operator"))
            if op not in self._BIN_OPS:
                raise UnsupportedGoConstruct(f"Operator not supported: {op}")
            left = self.transpile_expr(node.child_by_field_name("left"))
            right = self.transpile_expr(node.child_by_field_name("right"))
            return f"({left} {self._BIN_OPS[op]} {right})"
        if node.type == "parenthesized_expression":
            return f"({self.transpile_expr(node.named_children[0])})"
        if node.type == "unary_expression":
            op_node = [c for c in node.children if c.type == "-"]
            if not op_node:
                raise UnsupportedGoConstruct(f"Prefix operator not supported: {_text(node)}")
            operand = node.child_by_field_name("operand")
            return f"(-{self.transpile_expr(operand)})"
        raise UnsupportedGoConstruct(f"Unsupported expression type: {node.type}")


def find_function(go_source, function_name):
    """Finds the function with the given name in the source (Go has
    no classes -- functions live directly at package level)."""
    parser = Parser(_LANGUAGE)
    tree = parser.parse(go_source.encode("utf-8"))
    for node in tree.root_node.named_children:
        if node.type == "function_declaration" and _text(node.child_by_field_name("name")) == function_name:
            return node
    raise UnsupportedGoConstruct(f"Function '{function_name}' not found")


def transpile_go_function(go_source, function_name, param_names=None, python_function_name=None, field_rename=None):
    """Translates a single Go function deterministically into Python
    source that engine.py can verify UNCHANGED. Raises
    UnsupportedGoConstruct with the exact error location for anything
    outside the supported subset. param_names/field_rename: see
    java_bridge.py/csharp_bridge.py -- engine.py requires exactly
    matching parameter names, and Go often uses a different naming
    convention (camelCase) than our COBOL reference (snake_case)."""
    fn = find_function(go_source, function_name)
    py_name = python_function_name or function_name
    params_node = fn.child_by_field_name("parameters")
    go_param_names = [_text(p.child_by_field_name("name")) for p in params_node.named_children]
    if param_names is not None:
        if len(param_names) != len(go_param_names):
            raise UnsupportedGoConstruct(
                f"param_names has {len(param_names)} entries, the function has {len(go_param_names)} parameters"
            )
        rename = dict(zip(go_param_names, param_names))
        final_param_names = param_names
    else:
        rename = {}
        final_param_names = go_param_names

    bridge = GoToPythonBridge(param_rename=rename, field_rename=field_rename)
    bridge.transpile_function(fn)
    body = "\n".join(bridge.lines) if bridge.lines else "    pass"
    return f"def {py_name}({', '.join(final_param_names)}):\n{body}\n"
