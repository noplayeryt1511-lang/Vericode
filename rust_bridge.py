# -*- coding: utf-8 -*-
"""
Rust frontend for VeriCode: the fourth target language besides Java/C#/Go.

Same architecture as java_bridge.py/csharp_bridge.py/go_bridge.py:
Rust -> our existing, supported Python subset -> engine.py
UNCHANGED.

IMPORTANT structural difference from the other three languages: Rust
is EXPRESSION-oriented. A function needs NO explicit 'return' -- the
last expression WITHOUT a trailing semicolon in the function body is
automatically the return value. In addition, 'if' itself is an
EXPRESSION (can produce a value), not just a control structure.

SOLVED using what the engine already handles (see engine.py: the
has_returned fix for early returns in if branches): an
'if/else if/else' chain whose LAST expression per branch is implicitly
the function's return value is translated into a Python if/elif/else
chain where EVERY branch gets its own 'return <expression>' --
exactly the pattern our engine handles correctly.

DELIBERATELY NOT supported: 'if' as a value INSIDE an assignment
('let x = if cond { a } else { b };') -- only as a function tail
expression. That would require an additional case distinction that is
out of scope for now.
"""

import tree_sitter_rust as tsrust
from tree_sitter import Language, Parser

_LANGUAGE = Language(tsrust.language())
_INT_TYPES = {"i8", "i16", "i32", "i64", "i128", "isize",
              "u8", "u16", "u32", "u64", "u128", "usize"}


class UnsupportedRustConstruct(Exception):
    """A Rust construct that this bridge does not (yet) cover --
    deliberately NOT guessed at or ignored."""
    pass


def _text(node):
    return node.text.decode("utf-8")


def _is_tail_expression(node):
    """The return value of a block is the last element WITHOUT a
    trailing semicolon. Rust still wraps tail expressions like if/match
    in 'expression_statement' too (unlike a bare identifier, which is
    NOT wrapped at all in tail position) -- the actual distinguishing
    feature is NOT the node type, but whether the LAST child token is
    a ';' or not."""
    if node.type == "let_declaration":
        return False
    if node.type != "expression_statement":
        return True  # not wrapped -> necessarily a tail (e.g. a bare identifier)
    children = node.children
    return not (children and children[-1].type == ";")


class RustToPythonBridge:
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
            if param.type != "parameter":
                continue  # e.g. 'self' on methods -- not relevant here, methods are not supported
            type_node = param.child_by_field_name("type")
            is_primitive = type_node.type == "primitive_type" and _text(type_node) in _INT_TYPES
            is_string = type_node.type == "type_identifier" and _text(type_node) == "String"
            is_array = (type_node.type == "array_type"
                        and type_node.child_by_field_name("element") is not None
                        and type_node.child_by_field_name("element").type == "primitive_type"
                        and _text(type_node.child_by_field_name("element")) in _INT_TYPES)
            is_record = type_node.type == "type_identifier" and not is_string
            if not (is_primitive or is_string or is_array or is_record):
                raise UnsupportedRustConstruct(
                    f"Parameter has an unsupported type: {_text(type_node)} "
                    f"(only int variants, String, [T; N] arrays, or structs)"
                )
        return_type = fn.child_by_field_name("return_type")
        is_string_return = return_type is not None and return_type.type == "type_identifier" and _text(return_type) == "String"
        if return_type is not None and not is_string_return and not (
                return_type.type == "primitive_type" and _text(return_type) in _INT_TYPES):
            raise UnsupportedRustConstruct(
                f"Only a primitive int return type or String is supported, got: {_text(return_type)}"
            )

        body = fn.child_by_field_name("body")
        self.transpile_block(list(body.named_children), tail_is_return=True)

    def transpile_block(self, statements, tail_is_return=False):
        if not statements:
            self._emit("pass")
            return
        # Special case: the last element is the implicit return value
        # (no semicolon, see the module docstring) -- must be detected
        # BEFORE normal processing.
        if tail_is_return and _is_tail_expression(statements[-1]):
            if len(statements) > 1:
                self.transpile_block(statements[:-1], tail_is_return=False)
            tail_node = statements[-1]
            if tail_node.type == "expression_statement":
                tail_node = tail_node.named_children[0]
            self._emit_tail_as_return(tail_node)
            return

        i = 0
        while i < len(statements):
            stmt = statements[i]
            nxt = statements[i + 1] if i + 1 < len(statements) else None
            # A countable for loop over a range ('for i in 0..12'), OR
            # (analogous to Go) 'let mut i = 0; while <similar pattern>'
            # does NOT exist in Rust (Rust has no plain while-with-
            # counting-variable idiom like Go/Java) -- so only the
            # range-based for loop is handled directly here.
            self.transpile_statement(stmt)
            i += 1

    def _emit_tail_as_return(self, node):
        """The return value of a block (no semicolon). For a simple
        expression: 'return <expression>'. For an if_expression as the
        tail: EVERY branch gets its OWN 'return', see the module
        docstring -- this is the trick that maps Rust's 'if as a value'
        onto our engine without special handling."""
        if node.type == "if_expression":
            self._emit_if_with_tail_returns(node)
            return
        val = self.transpile_expr(node)
        self._emit(f"return {val}")

    def _emit_if_with_tail_returns(self, node):
        cond = self.transpile_expr(node.child_by_field_name("condition"))
        self._emit(f"if {cond}:")
        self.indent += 1
        cons = node.child_by_field_name("consequence")
        self.transpile_block(list(cons.named_children), tail_is_return=True)
        self.indent -= 1
        alt = node.child_by_field_name("alternative")
        if alt is None:
            raise UnsupportedRustConstruct(
                "if as a tail expression WITHOUT else is not supported -- Rust would only "
                "allow that for a '()' return type anyway, not for int/String"
            )
        # 'alternative' is ALWAYS wrapped in an 'else_clause' node,
        # whose single named child is either another if_expression
        # ('else if') or a 'block' (a plain 'else').
        inner = alt.named_children[0] if alt.type == "else_clause" else alt
        if inner.type == "if_expression":
            self._emit("else:")
            self.indent += 1
            self._emit_if_with_tail_returns(inner)
            self.indent -= 1
        else:
            self._emit("else:")
            self.indent += 1
            self.transpile_block(list(inner.named_children), tail_is_return=True)
            self.indent -= 1

    def transpile_statement(self, stmt):
        if stmt.type == "expression_statement":
            inner = stmt.named_children[0]
            handler = getattr(self, f"_stmt_{inner.type}", None)
            if handler is None:
                raise UnsupportedRustConstruct(f"Unsupported Rust statement: {inner.type}")
            handler(inner)
            return
        handler = getattr(self, f"_stmt_{stmt.type}", None)
        if handler is None:
            raise UnsupportedRustConstruct(f"Unsupported Rust statement: {stmt.type}")
        handler(stmt)

    # --- let declaration ('let x: i64 = 5;' or 'let mut x: i64;') -------
    def _stmt_let_declaration(self, stmt):
        name = _text(stmt.child_by_field_name("pattern"))
        value_node = stmt.child_by_field_name("value")
        if value_node is not None:
            val = self.transpile_expr(value_node)
            self._emit(f"{name} = {val}")
        else:
            # Without an initializer: Rust enforces "definite assignment"
            # before use just like our engine does -- BUT we STILL need
            # to set a placeholder (see the has_returned mechanism),
            # otherwise a NameError occurs on the first assignment in an
            # if branch. Uses the declared type to pick the right zero
            # value (0 for numbers, "" for String) -- a wrong type here
            # would NOT surface as a Python error, but only as a Z3 sort
            # conflict during the proof (see go_bridge.py: the same issue).
            type_node = stmt.child_by_field_name("type")
            if type_node is not None and type_node.type == "type_identifier" and _text(type_node) == "String":
                self._emit(f'{name} = ""')
            else:
                self._emit(f"{name} = 0")

    # --- Assignment / compound assignment ---------------------------------------
    _COMPOUND_OPS = {"+=": "+", "-=": "-", "*=": "*", "/=": "//", "%=": "%"}

    def _stmt_assignment_expression(self, stmt):
        target = self.transpile_expr(stmt.child_by_field_name("left"))
        val = self.transpile_expr(stmt.child_by_field_name("right"))
        self._emit(f"{target} = {val}")

    def _stmt_compound_assignment_expr(self, stmt):
        target = self.transpile_expr(stmt.child_by_field_name("left"))
        op_node = [c for c in stmt.children if _text(c) in self._COMPOUND_OPS]
        if not op_node:
            raise UnsupportedRustConstruct(f"Compound assignment operator not recognized: {_text(stmt)!r}")
        op = self._COMPOUND_OPS[_text(op_node[0])]
        val = self.transpile_expr(stmt.child_by_field_name("right"))
        self._emit(f"{target} = ({target} {op} {val})")

    # --- IF/ELSE as a plain control-flow statement -------------------------
    def _stmt_if_expression(self, stmt):
        cond = self.transpile_expr(stmt.child_by_field_name("condition"))
        self._emit(f"if {cond}:")
        self.indent += 1
        cons = stmt.child_by_field_name("consequence")
        self.transpile_block(list(cons.named_children))
        self.indent -= 1
        alt = stmt.child_by_field_name("alternative")
        if alt is not None:
            inner = alt.named_children[0] if alt.type == "else_clause" else alt
            if inner.type == "if_expression":
                self._emit("else:")
                self.indent += 1
                self._stmt_if_expression(inner)
                self.indent -= 1
            else:
                self._emit("else:")
                self.indent += 1
                self.transpile_block(list(inner.named_children))
                self.indent -= 1

    # --- FOR loop over a range ('for i in 0..12') --------------------
    def _stmt_for_expression(self, stmt):
        pattern = stmt.child_by_field_name("pattern")
        if pattern is None or pattern.type != "identifier":
            raise UnsupportedRustConstruct("Only 'for i in START..END' with a simple variable is supported")
        loop_var = _text(pattern)
        range_node = stmt.child_by_field_name("value")
        if range_node is None or range_node.type not in ("range_expression",):
            raise UnsupportedRustConstruct(
                "Only range-based for loops are supported ('for i in START..END'), "
                "no iterating over collections/iterators"
            )
        bounds = [c for c in range_node.children if c.type == "integer_literal"]
        if len(bounds) != 2:
            raise UnsupportedRustConstruct("Range bounds must be constant integer literals")
        start, stop = int(_text(bounds[0])), int(_text(bounds[1]))
        inclusive = any(c.type == "..=" for c in range_node.children)
        if inclusive:
            stop += 1

        self._emit(f"for {loop_var} in range({start}, {stop}, 1):")
        self.indent += 1
        body = stmt.child_by_field_name("body")
        self.transpile_block(list(body.named_children))
        self.indent -= 1

    # --- RETURN (explicit) ------------------------------------------------
    def _stmt_return_expression(self, stmt):
        if not stmt.named_children:
            raise UnsupportedRustConstruct("'return;' without a value is not supported")
        val = self.transpile_expr(stmt.named_children[0])
        self._emit(f"return {val}")

    # --- Expressions -----------------------------------------------------
    _BIN_OPS = {"+": "+", "-": "-", "*": "*", "/": "//", "%": "%",
                "==": "==", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">=",
                "&&": "and", "||": "or"}

    def transpile_expr(self, node):
        if node.type == "integer_literal":
            return _text(node).rstrip("iu8163264128sze_")  # Rust allows "100i64"-style suffixes
        if node.type == "string_literal":
            raw = _text(node)
            return raw.replace("'", '"') if not raw.startswith('"') else raw
        if node.type == "identifier":
            name = _text(node)
            return self.param_rename.get(name, name)
        if node.type == "field_expression":
            base = self.transpile_expr(node.child_by_field_name("value"))
            field = _text(node.child_by_field_name("field"))
            field = self.field_rename.get(field, field)
            return f"{base}.{field}"
        if node.type == "index_expression":
            base = self.transpile_expr(node.named_children[0])
            index_py = self.transpile_expr(node.named_children[1])
            return f"{base}[{index_py}]"
        if node.type == "binary_expression":
            op_node = node.child_by_field_name("operator")
            op = _text(op_node) if op_node else [c for c in node.children if _text(c) in self._BIN_OPS][0].text.decode()
            if op not in self._BIN_OPS:
                raise UnsupportedRustConstruct(f"Operator not supported: {op}")
            left = self.transpile_expr(node.child_by_field_name("left"))
            right = self.transpile_expr(node.child_by_field_name("right"))
            return f"({left} {self._BIN_OPS[op]} {right})"
        if node.type == "parenthesized_expression":
            return f"({self.transpile_expr(node.named_children[0])})"
        if node.type == "unary_expression":
            op_node = [c for c in node.children if c.type == "-"]
            if not op_node:
                raise UnsupportedRustConstruct(f"Prefix operator not supported: {_text(node)}")
            operand = node.named_children[0]
            return f"(-{self.transpile_expr(operand)})"
        raise UnsupportedRustConstruct(f"Unsupported expression type: {node.type}")


def find_function(rust_source, function_name):
    """Finds the function with the given name in the source (Rust has
    no classes in the COBOL-relevant sense -- functions live at module
    level, possibly alongside struct declarations)."""
    parser = Parser(_LANGUAGE)
    tree = parser.parse(rust_source.encode("utf-8"))
    for node in tree.root_node.named_children:
        if node.type == "function_item" and _text(node.child_by_field_name("name")) == function_name:
            return node
    raise UnsupportedRustConstruct(f"Function '{function_name}' not found")


def transpile_rust_function(rust_source, function_name, param_names=None, python_function_name=None, field_rename=None):
    """Translates a single Rust function deterministically into Python
    source that engine.py can verify UNCHANGED. Raises
    UnsupportedRustConstruct with the exact error location for anything
    outside the supported subset."""
    fn = find_function(rust_source, function_name)
    py_name = python_function_name or function_name
    params_node = fn.child_by_field_name("parameters")
    rust_param_names = [_text(p.child_by_field_name("pattern")) for p in params_node.named_children
                         if p.type == "parameter"]
    if param_names is not None:
        if len(param_names) != len(rust_param_names):
            raise UnsupportedRustConstruct(
                f"param_names has {len(param_names)} entries, the function has {len(rust_param_names)} parameters"
            )
        rename = dict(zip(rust_param_names, param_names))
        final_param_names = param_names
    else:
        rename = {}
        final_param_names = rust_param_names

    bridge = RustToPythonBridge(param_rename=rename, field_rename=field_rename)
    bridge.transpile_function(fn)
    body = "\n".join(bridge.lines) if bridge.lines else "    pass"
    return f"def {py_name}({', '.join(final_param_names)}):\n{body}\n"
