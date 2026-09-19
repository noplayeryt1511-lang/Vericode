# -*- coding: utf-8 -*-
"""
C frontend for VeriCode -- PROOF OF CONCEPT, built to answer the
question "can we also verify C-to-Rust?". Same architecture as
java_bridge.py/csharp_bridge.py/go_bridge.py/rust_bridge.py: C -> our
existing, supported Python subset -> engine.py UNCHANGED.

KEY DIFFERENCE from the four earlier bridges: those were always used
as the TARGET language. This bridge demonstrates that the same
technique also works as the SOURCE language -- here C becomes the
"legacy_fn" side, e.g. verified against a Rust reference translated
with rust_bridge.py. The verification core (engine.py) does not
distinguish between "legacy" and "modern" -- it compares two Python
functions.

DELIBERATELY MINIMAL (proof of concept, not production-ready): int
parameters/return values, local int declarations, if/else, for loops
with constant bounds, simple arithmetic/comparisons, return. NO
pointers, NO structs, NO array access, NO malloc/free."""

import tree_sitter_c as tsc
from tree_sitter import Language, Parser

_LANGUAGE = Language(tsc.language())
_INT_TYPES = {"int", "long", "short", "unsigned", "signed", "long long"}


class UnsupportedCConstruct(Exception):
    pass


def _text(node):
    return node.text.decode("utf-8")


class CToPythonBridge:
    def __init__(self, param_rename=None):
        self.param_rename = param_rename or {}
        self.lines = []
        self.indent = 1

    def _emit(self, line):
        self.lines.append("    " * self.indent + line)

    def _name(self, cobol_like_name):
        return self.param_rename.get(cobol_like_name, cobol_like_name)

    def transpile_block(self, compound_stmt):
        for child in compound_stmt.named_children:
            self.transpile_statement(child)

    def transpile_statement(self, stmt):
        handler = getattr(self, f"_stmt_{stmt.type}", None)
        if handler is None:
            raise UnsupportedCConstruct(f"Unsupported C construct: {stmt.type} — text: {_text(stmt)!r}")
        handler(stmt)

    def _stmt_declaration(self, stmt):
        type_node = stmt.child_by_field_name("type")
        if type_node is None or _text(type_node) not in _INT_TYPES:
            raise UnsupportedCConstruct(f"Only int-like declarations are supported: {_text(stmt)!r}")
        for child in stmt.named_children:
            if child.type == "init_declarator":
                name = _text(child.child_by_field_name("declarator"))
                value_node = child.child_by_field_name("value")
                val = self._as_int_value(value_node)
                self._emit(f"{self._name(name)} = {val}")
            elif child.type == "identifier":
                self._emit(f"{self._name(_text(child))} = 0")

    def _stmt_expression_statement(self, stmt):
        expr = stmt.named_children[0]
        if expr.type == "assignment_expression":
            target = _text(expr.child_by_field_name("left"))
            val = self._as_int_value(expr.child_by_field_name("right"))
            self._emit(f"{self._name(target)} = {val}")
        else:
            raise UnsupportedCConstruct(f"Unsupported expression as statement: {_text(expr)!r}")

    def _stmt_if_statement(self, stmt):
        cond = self.transpile_expr(stmt.child_by_field_name("condition"))
        self._emit(f"if {cond}:")
        self.indent += 1
        consequence = stmt.child_by_field_name("consequence")
        if consequence.type == "compound_statement":
            self.transpile_block(consequence)
        else:
            self.transpile_statement(consequence)
        self.indent -= 1
        alt = stmt.child_by_field_name("alternative")
        if alt is not None:
            self._emit("else:")
            self.indent += 1
            body = alt.named_children[0] if alt.type == "else_clause" else alt
            if body.type == "compound_statement":
                self.transpile_block(body)
            elif body.type == "if_statement":
                self.transpile_statement(body)
            else:
                self.transpile_statement(body)
            self.indent -= 1

    def _stmt_for_statement(self, stmt):
        init = stmt.child_by_field_name("initializer")
        cond = stmt.child_by_field_name("condition")
        update = stmt.child_by_field_name("update")
        if init is None or init.type != "declaration":
            raise UnsupportedCConstruct(f"Only 'for (int i = <const>; ...; ...)' is supported: {_text(stmt)!r}")
        init_decl = next(c for c in init.named_children if c.type == "init_declarator")
        var_name = self._name(_text(init_decl.child_by_field_name("declarator")))
        start_val = init_decl.child_by_field_name("value")
        if start_val.type != "number_literal":
            raise UnsupportedCConstruct("Only a constant start value is supported in for loops")
        if cond is None or cond.type != "binary_expression" or _text(cond.child_by_field_name("operator")) != "<":
            raise UnsupportedCConstruct("Only 'i < <expression>' is supported as a for condition")
        end_expr = self.transpile_expr(cond.child_by_field_name("right"))
        if update is None or update.type != "update_expression" or _text(update)[-2:] != "++":
            raise UnsupportedCConstruct("Only 'i++' is supported as a for update")
        self._emit(f"for {var_name} in range({_text(start_val)}, {end_expr}):")
        self.indent += 1
        body = stmt.child_by_field_name("body")
        if body.type == "compound_statement":
            self.transpile_block(body)
        else:
            self.transpile_statement(body)
        self.indent -= 1

    def _stmt_return_statement(self, stmt):
        if not stmt.named_children:
            raise UnsupportedCConstruct("'return;' without a value is not supported")
        val = self._as_int_value(stmt.named_children[0])
        self._emit(f"return {val}")

    _BIN_OPS = {"+": "+", "-": "-", "*": "*", "/": "//", "%": "%",
                "==": "==", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">=",
                "&&": "and", "||": "or",
                "&": "&", "|": "|", "^": "^", "<<": "<<", ">>": ">>"}

    _COMPARISON_OPS = {"==", "!=", "<", "<=", ">", ">=", "&&", "||"}

    def _as_int_value(self, expr_node):
        """Translates an expression AND, if it is a comparison/logical
        expression, explicitly converts it to 0/1 -- IMPORTANT: in C,
        comparison/boolean expressions are themselves of type 'int'
        (0 or 1), unlike Python's separate bool type. Only needed at
        VALUE positions (assignment, return) -- NOT for an if's own
        condition (there engine.py needs a real Z3 bool, not a 0/1
        integer)."""
        expr = self.transpile_expr(expr_node)
        if expr_node.type == "binary_expression" and _text(expr_node.child_by_field_name("operator")) in self._COMPARISON_OPS:
            return f"(1 if {expr} else 0)"
        return expr

    def transpile_expr(self, node):
        if node.type == "number_literal":
            return _text(node)
        if node.type == "identifier":
            return self._name(_text(node))
        if node.type == "parenthesized_expression":
            return f"({self.transpile_expr(node.named_children[0])})"
        if node.type == "binary_expression":
            op = _text(node.child_by_field_name("operator"))
            if op not in self._BIN_OPS:
                raise UnsupportedCConstruct(f"Unsupported operator: {op!r}")
            left = self.transpile_expr(node.child_by_field_name("left"))
            right = self.transpile_expr(node.child_by_field_name("right"))
            return f"({left} {self._BIN_OPS[op]} {right})"
        if node.type == "unary_expression":
            op = _text(node.child_by_field_name("operator"))
            if op == "-":
                return f"(-{self.transpile_expr(node.child_by_field_name('argument'))})"
            if op == "~":
                return f"(~{self.transpile_expr(node.child_by_field_name('argument'))})"
            if op == "!":
                return f"(not {self.transpile_expr(node.child_by_field_name('argument'))})"
            raise UnsupportedCConstruct(f"Unsupported unary operator: {op!r}")
        raise UnsupportedCConstruct(f"Unsupported expression type: {node.type} — text: {_text(node)!r}")


def transpile_c_function(c_source, function_name, param_names=None):
    parser = Parser(_LANGUAGE)
    tree = parser.parse(c_source.encode("utf-8"))

    func_node = None
    for node in tree.root_node.named_children:
        if node.type == "function_definition":
            declarator = node.child_by_field_name("declarator")
            name_node = declarator.child_by_field_name("declarator") if declarator.type == "function_declarator" else None
            if name_node is not None and _text(name_node) == function_name:
                func_node = node
                break
    if func_node is None:
        raise UnsupportedCConstruct(f"Function '{function_name}' not found in source")

    declarator = func_node.child_by_field_name("declarator")
    param_list = declarator.child_by_field_name("parameters")
    c_params = []
    for p in param_list.named_children:
        if p.type == "parameter_declaration":
            ident = p.child_by_field_name("declarator")
            if ident is not None:
                c_params.append(_text(ident))

    param_rename = {}
    if param_names:
        if len(param_names) != len(c_params):
            raise UnsupportedCConstruct(
                f"Number of provided parameter names ({len(param_names)}) does not match the "
                f"function signature ({len(c_params)})"
            )
        param_rename = dict(zip(c_params, param_names))
    py_params = ", ".join(param_rename.get(p, p) for p in c_params)

    bridge = CToPythonBridge(param_rename=param_rename)
    body = func_node.child_by_field_name("body")
    bridge.transpile_block(body)

    return f"def {function_name}({py_params}):\n" + "\n".join(bridge.lines) + "\n"
