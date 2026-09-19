# -*- coding: utf-8 -*-
"""
C# frontend for VeriCode: the second target language besides Java/Python.

Same architecture as java_bridge.py: C# -> our existing, supported
Python subset -> engine.py UNCHANGED. Market research explicitly named
C# as the most natural .NET target language (the native 128-bit decimal
type maps directly onto COBOL's packed decimal numbers).

Uses `tree-sitter` + `tree-sitter-c-sharp` (PyPI) -- unlike `javalang`
NOT pure Python (compiled bindings), but an established, reputable,
widely used library (used by GitHub itself for syntax highlighting,
among others), of no questionable origin.

SUPPORTED SUBSET: identical to java_bridge.py (see there) --
int/long parameters and return type, local variables, if/else if/else,
for loops with constant bounds, records via classes with public
fields, +=/-=/*=//= .
"""

import tree_sitter_c_sharp as tscsharp
from tree_sitter import Language, Parser

_LANGUAGE = Language(tscsharp.language())
_INT_TYPES = {"int", "long", "short", "sbyte", "uint", "ulong", "ushort", "byte"}


class UnsupportedCSharpConstruct(Exception):
    """A C# construct that this bridge does not (yet) cover -- deliberately
    NOT guessed at or ignored."""
    pass


def _text(node):
    return node.text.decode("utf-8")


class CSharpToPythonBridge:
    def __init__(self, param_rename=None, field_rename=None):
        self.lines = []
        self.indent = 1
        self.param_rename = param_rename or {}
        self.field_rename = field_rename or {}  # C# field name (e.g. "Balance") -> target name ("balance")

    def _emit(self, line):
        self.lines.append("    " * self.indent + line)

    def transpile_method(self, method):
        params_node = method.child_by_field_name("parameters")
        for param in params_node.named_children:
            type_node = param.child_by_field_name("type")
            type_text = _text(type_node)
            is_primitive = type_node.type == "predefined_type" and type_text in _INT_TYPES
            is_string = type_node.type == "predefined_type" and type_text == "string"
            is_array = (type_node.type == "array_type"
                        and type_node.child_by_field_name("type") is not None
                        and _text(type_node.child_by_field_name("type")) in _INT_TYPES)
            is_reference = type_node.type == "identifier"  # class name used as the type
            if not (is_primitive or is_string or is_array or is_reference):
                raise UnsupportedCSharpConstruct(
                    f"Parameter '{_text(param.child_by_field_name('name'))}' has an "
                    f"unsupported type: {type_text} (only primitive int/long types, arrays thereof, string, or records)"
                )
            # Array parameters (e.g. int[]) are treated as a table --
            # C# does NOT know the actual length (the COBOL OCCURS
            # equivalent), so the caller must supply table_types ITSELF.
            # string parameters are mapped directly onto our existing
            # PicX/Z3-string infrastructure (like a COBOL PicX field).
        returns_node = method.child_by_field_name("returns")
        is_string_return = returns_node is not None and returns_node.type == "predefined_type" and _text(returns_node) == "string"
        if returns_node is not None and not is_string_return and not (
                returns_node.type == "predefined_type" and _text(returns_node) in _INT_TYPES):
            raise UnsupportedCSharpConstruct(
                f"Only a primitive int/long return type or string is supported, got: {_text(returns_node)}"
            )

        body = method.child_by_field_name("body")
        self.transpile_block(body.named_children)

    def transpile_block(self, statements):
        if not statements:
            self._emit("pass")
            return
        i = 0
        while i < len(statements):
            stmt = statements[i]
            nxt = statements[i + 1] if i + 1 < len(statements) else None
            if nxt is not None and nxt.type == "while_statement" and stmt.type == "local_declaration_statement":
                var_decl = stmt.named_children[0]
                declarators = [c for c in var_decl.named_children if c.type == "variable_declarator"]
                if len(declarators) == 1:
                    decl = declarators[0]
                    name_node = decl.child_by_field_name("name")
                    init_nodes = [c for c in decl.named_children if c != name_node]
                    if init_nodes and init_nodes[0].type == "integer_literal":
                        loop_var = _text(name_node)
                        start = int(_text(init_nodes[0]))
                        if self._try_emit_counted_while(loop_var, start, nxt):
                            i += 2
                            continue
            self.transpile_statement(stmt)
            i += 1

    def _try_emit_counted_while(self, loop_var, start, while_stmt):
        """Recognizes 'int i = START; while (i (< | <= | > | >=) <constant>)
        { ...; i++/i--; }' -- a countable loop, only syntactically
        written as while instead of for -- and translates it to 'for i in
        range(...)'. engine.py does NOT support unbounded while loops
        symbolically, so every while loop MUST match this one pattern
        or be rejected entirely. Returns False (not an error) when the
        pattern does not match."""
        cond = while_stmt.child_by_field_name("condition")
        if cond is None or cond.type != "binary_expression":
            return False
        cond_left = cond.child_by_field_name("left")
        cond_right = cond.child_by_field_name("right")
        cond_op = _text(cond.child_by_field_name("operator"))
        if not (cond_left.type == "identifier" and _text(cond_left) == loop_var
                and cond_right.type == "integer_literal" and cond_op in ("<", "<=", ">", ">=")):
            return False
        bound = int(_text(cond_right))

        body_node = while_stmt.child_by_field_name("body")
        body = body_node.named_children if body_node.type == "block" else [body_node]
        if not body:
            return False
        last = body[-1]
        if not (last.type == "expression_statement" and last.named_children
                and last.named_children[0].type == "postfix_unary_expression"):
            return False
        upd = last.named_children[0]
        upd_operand = upd.named_children[0]
        upd_op_node = [c for c in upd.children if c.type in ("++", "--")]
        if not (upd_operand.type == "identifier" and _text(upd_operand) == loop_var and upd_op_node):
            return False
        step = 1 if upd_op_node[0].type == "++" else -1

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
        self.transpile_block(body[:-1])  # the last statement (increment) is already in range()
        self.indent -= 1
        return True

    def _stmt_while_statement(self, stmt):
        # Only reached when NO matching initialization directly preceded
        # it (see transpile_block).
        raise UnsupportedCSharpConstruct(
            "while loop not supported -- only the pattern 'int i = START; while (i OP CONSTANT) "
            "{ ...; i++/i--; }' (immediately consecutive) is recognized as a bounded counting loop. "
            "engine.py cannot symbolically prove unbounded while loops."
        )

    def transpile_statement(self, stmt):
        handler = getattr(self, f"_stmt_{stmt.type}", None)
        if handler is None:
            raise UnsupportedCSharpConstruct(f"Unsupported C# statement: {stmt.type}")
        handler(stmt)

    # --- Local variable declaration --------------------------------------
    def _stmt_local_declaration_statement(self, stmt):
        var_decl = stmt.named_children[0]
        for declarator in var_decl.named_children[1:]:  # [0] is the type
            name = _text(declarator.child_by_field_name("name"))
            init_nodes = [c for c in declarator.named_children if c != declarator.child_by_field_name("name")]
            if init_nodes:
                val = self.transpile_expr(init_nodes[0])
                self._emit(f"{name} = {val}")
            # without an initializer: C# enforces "definite assignment"
            # before use, just as our engine does -- compatible.

    # --- Assignment as a standalone statement ---------------------------
    _COMPOUND_OPS = {"+=": "+", "-=": "-", "*=": "*", "/=": "//", "%=": "%"}

    def _stmt_expression_statement(self, stmt):
        expr = stmt.named_children[0]
        if expr.type == "assignment_expression":
            op = _text(expr.child_by_field_name("operator"))
            target = self.transpile_expr(expr.child_by_field_name("left"))
            val = self.transpile_expr(expr.child_by_field_name("right"))
            if op == "=":
                self._emit(f"{target} = {val}")
            elif op in self._COMPOUND_OPS:
                self._emit(f"{target} = ({target} {self._COMPOUND_OPS[op]} {val})")
            else:
                raise UnsupportedCSharpConstruct(f"Assignment operator not supported: '{op}'")
            return
        raise UnsupportedCSharpConstruct(f"Unsupported expression as statement: {expr.type}")

    # --- IF/ELSE -----------------------------------------------------------
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
            self.transpile_block(node.named_children)
        else:
            self.transpile_statement(node)

    # --- FOR loop (only constant bounds, as in java_bridge.py) ----------
    # --- SWITCH (analogous to COBOL EVALUATE / Java's switch) -------------------
    def _stmt_switch_statement(self, stmt):
        subject = self.transpile_expr(stmt.child_by_field_name("value"))
        switch_body = [c for c in stmt.children if c.type == "switch_body"][0]

        pending_values = []  # accumulated fallthrough labels with no body of their own
        first = True
        default_pending = False
        default_body = None
        for section in switch_body.named_children:
            is_default = any(c.type == "default" for c in section.children)
            label_nodes = [c for c in section.named_children if c.type == "constant_pattern"]
            body = [c for c in section.named_children if c.type not in ("constant_pattern",)]

            if is_default:
                default_pending = True
            elif label_nodes:
                pending_values.append(self.transpile_expr(label_nodes[0].named_children[0]))

            if not body:
                continue  # a pure fallthrough label with no body -- merge with the next section

            self._require_break_and_strip(body, section)
            if default_pending and not pending_values:
                default_body = body
            else:
                cond = " or ".join(f"({subject} == {v})" for v in pending_values)
                if default_pending:
                    # "default:" followed by case labels WITHOUT their own
                    # body, then a case WITH a body -- default and these
                    # values share the same code path. Rare, but handled
                    # correctly: default then counts as an EQUIVALENT
                    # condition (always true), which is correct as long as
                    # it is the only remaining case -- otherwise reject.
                    raise UnsupportedCSharpConstruct(
                        "SWITCH: 'default:' combined with case labels sharing the same "
                        "body is not supported (ambiguous)"
                    )
                self._emit(f"{'if' if first else 'elif'} {cond}:")
                first = False
                self.indent += 1
                self._emit_case_body(body)
                self.indent -= 1
            pending_values = []
            default_pending = False

        if default_body is not None:
            self._emit("else:")
            self.indent += 1
            self._emit_case_body(default_body)
            self.indent -= 1
        elif first:
            raise UnsupportedCSharpConstruct("SWITCH without any case/default")

    def _require_break_and_strip(self, body, section):
        """Checks that a case branch ends with 'break;' (NO real
        fall-through into the next branch -- different semantics than our
        If/Elif translation) and removes the break from the list to be
        translated (mutates body in place)."""
        if not body or body[-1].type != "break_statement":
            raise UnsupportedCSharpConstruct(
                f"SWITCH branch does not end with 'break;' -- real fall-through "
                f"into the next branch is not supported: {_text(section)[:60]!r}"
            )
        body.pop()

    def _emit_case_body(self, statements):
        if not statements:
            self._emit("pass")
            return
        for s in statements:
            self.transpile_statement(s)

    def _stmt_for_statement(self, stmt):
        init = stmt.child_by_field_name("initializer")
        cond = stmt.child_by_field_name("condition")
        update = stmt.child_by_field_name("update")

        if init is None or init.type != "variable_declaration":
            raise UnsupportedCSharpConstruct("FOR init must be exactly ONE variable declaration, e.g. 'int i = 0'")
        declarators = [c for c in init.named_children if c.type == "variable_declarator"]
        if len(declarators) != 1:
            raise UnsupportedCSharpConstruct("FOR init must declare exactly ONE variable")
        decl = declarators[0]
        loop_var = _text(decl.child_by_field_name("name"))
        init_vals = [c for c in decl.named_children if c != decl.child_by_field_name("name")]
        if not init_vals or init_vals[0].type != "integer_literal":
            raise UnsupportedCSharpConstruct("FOR start value must be a constant integer literal")
        start = int(_text(init_vals[0]))

        if cond is None or cond.type != "binary_expression":
            raise UnsupportedCSharpConstruct(f"FOR condition must be a simple comparison, e.g. '{loop_var} < N'")
        cond_left = cond.child_by_field_name("left")
        cond_right = cond.child_by_field_name("right")
        cond_op = _text(cond.child_by_field_name("operator"))
        if not (cond_left.type == "identifier" and _text(cond_left) == loop_var and cond_right.type == "integer_literal"
                and cond_op in ("<", "<=", ">", ">=")):
            raise UnsupportedCSharpConstruct(
                f"FOR condition must be '{loop_var} (< | <= | > | >=) <constant>', no data-dependent bound"
            )
        bound = int(_text(cond_right))

        if update is None or update.type != "postfix_unary_expression":
            raise UnsupportedCSharpConstruct("FOR update must be exactly ONE simple 'i++'/'i--'")
        upd_operand = update.named_children[0]
        upd_op_node = [c for c in update.children if c.type in ("++", "--")]
        if not (upd_operand.type == "identifier" and _text(upd_operand) == loop_var and upd_op_node):
            raise UnsupportedCSharpConstruct(f"FOR update must be '{loop_var}++' or '{loop_var}--'")
        step = 1 if upd_op_node[0].type == "++" else -1

        if step == 1:
            if cond_op not in ("<", "<="):
                raise UnsupportedCSharpConstruct(f"'{loop_var}++' needs '<' or '<=', not '{cond_op}'")
            stop = bound if cond_op == "<" else bound + 1
        else:
            if cond_op not in (">", ">="):
                raise UnsupportedCSharpConstruct(f"'{loop_var}--' needs '>' or '>=', not '{cond_op}'")
            stop = bound if cond_op == ">" else bound - 1

        self._emit(f"for {loop_var} in range({start}, {stop}, {step}):")
        self.indent += 1
        self._transpile_nested_block(stmt.child_by_field_name("body"))
        self.indent -= 1

    # --- RETURN --------------------------------------------------------
    def _stmt_return_statement(self, stmt):
        if not stmt.named_children:
            raise UnsupportedCSharpConstruct("'return;' without a value is not supported")
        val = self.transpile_expr(stmt.named_children[0])
        self._emit(f"return {val}")

    # --- TRY/CATCH -- deliberately narrowly scoped to ONE pattern (see
    # java_bridge.py -- the same rationale: our engine symbolically
    # evaluates pure, side-effect-free functions, real control-flow
    # unwinding does not structurally fit. Only division with a zero guard.
    _ARITHMETIC_EXCEPTION_TYPES = {"DivideByZeroException", "ArithmeticException", "Exception"}

    def _stmt_try_statement(self, stmt):
        finally_clauses = [c for c in stmt.named_children if c.type == "finally_clause"]
        if finally_clauses:
            raise UnsupportedCSharpConstruct("finally block is not supported")
        try_body = stmt.child_by_field_name("body")
        try_stmts = try_body.named_children
        if len(try_stmts) != 1 or try_stmts[0].type != "expression_statement":
            raise UnsupportedCSharpConstruct(
                "try block must contain EXACTLY ONE statement, an assignment with division "
                "('target = a / b;') -- anything more complex is deliberately not supported"
            )
        try_expr = try_stmts[0].named_children[0]
        if not (try_expr.type == "assignment_expression"
                and try_expr.child_by_field_name("left").type == "identifier"):
            raise UnsupportedCSharpConstruct("try block must contain a simple assignment")
        target = self.param_rename.get(_text(try_expr.child_by_field_name("left")), _text(try_expr.child_by_field_name("left")))
        right = try_expr.child_by_field_name("right")
        if not (right.type == "binary_expression" and _text(right.child_by_field_name("operator")) == "/"):
            raise UnsupportedCSharpConstruct("try block must contain EXACTLY ONE division assignment ('target = a / b;')")
        numerator = self.transpile_expr(right.child_by_field_name("left"))
        denominator = self.transpile_expr(right.child_by_field_name("right"))

        catch_clauses = [c for c in stmt.named_children if c.type == "catch_clause"]
        if len(catch_clauses) != 1:
            raise UnsupportedCSharpConstruct("Only EXACTLY ONE catch branch is supported")
        cc = catch_clauses[0]
        decl = [c for c in cc.named_children if c.type == "catch_declaration"]
        if decl:
            caught_type = _text(decl[0].child_by_field_name("type"))
            if caught_type not in self._ARITHMETIC_EXCEPTION_TYPES:
                raise UnsupportedCSharpConstruct(
                    f"Only arithmetic-related exception types are supported "
                    f"({sorted(self._ARITHMETIC_EXCEPTION_TYPES)}), got: {caught_type}"
                )
        catch_body = cc.child_by_field_name("body")
        catch_stmts = catch_body.named_children
        if len(catch_stmts) != 1 or catch_stmts[0].type != "expression_statement":
            raise UnsupportedCSharpConstruct(
                "catch block must contain EXACTLY ONE statement, an assignment to the SAME target"
            )
        catch_expr = catch_stmts[0].named_children[0]
        if not (catch_expr.type == "assignment_expression"
                and catch_expr.child_by_field_name("left").type == "identifier"
                and _text(catch_expr.child_by_field_name("left")) == _text(try_expr.child_by_field_name("left"))):
            raise UnsupportedCSharpConstruct("catch block must assign to the SAME target as the try block")
        fallback = self.transpile_expr(catch_expr.child_by_field_name("right"))

        self._emit(f"{target} = ({fallback} if {denominator} == 0 else ({numerator} // {denominator}))")

    # --- Expressions -----------------------------------------------------
    _BIN_OPS = {"+": "+", "-": "-", "*": "*", "/": "//", "%": "%",
                "==": "==", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">=",
                "&&": "and", "||": "or"}

    def transpile_expr(self, node):
        if node.type == "integer_literal":
            return _text(node).rstrip("lLuU")
        if node.type == "string_literal":
            return _text(node)  # C# keeps quotes like Python -- can be used as-is
        if node.type == "identifier":
            name = _text(node)
            return self.param_rename.get(name, name)
        if node.type == "member_access_expression":
            base = self.transpile_expr(node.child_by_field_name("expression"))
            member = _text(node.child_by_field_name("name"))
            member = self.field_rename.get(member, member)
            return f"{base}.{member}"
        if node.type == "element_access_expression":
            base = self.transpile_expr(node.child_by_field_name("expression"))
            subscript = node.child_by_field_name("subscript")
            args = [c for c in subscript.named_children if c.type == "argument"]
            if len(args) != 1:
                raise UnsupportedCSharpConstruct(
                    f"Only a single array index 'a[i]' is supported (no 'a[i,j]'): {_text(node)}"
                )
            index_py = self.transpile_expr(args[0].named_children[0])
            return f"{base}[{index_py}]"
        if node.type == "binary_expression":
            op = _text(node.child_by_field_name("operator"))
            if op not in self._BIN_OPS:
                raise UnsupportedCSharpConstruct(f"Operator not supported: {op}")
            left = self.transpile_expr(node.child_by_field_name("left"))
            right = self.transpile_expr(node.child_by_field_name("right"))
            return f"({left} {self._BIN_OPS[op]} {right})"
        if node.type == "parenthesized_expression":
            return f"({self.transpile_expr(node.named_children[0])})"
        if node.type == "prefix_unary_expression":
            op_node = [c for c in node.children if c.type == "-"]
            if not op_node:
                raise UnsupportedCSharpConstruct(f"Prefix operator not supported: {_text(node)}")
            return f"(-{self.transpile_expr(node.named_children[0])})"
        if node.type == "conditional_expression":
            cond = self.transpile_expr(node.child_by_field_name("condition"))
            consequence = self.transpile_expr(node.child_by_field_name("consequence"))
            alternative = self.transpile_expr(node.child_by_field_name("alternative"))
            return f"({consequence} if {cond} else {alternative})"
        raise UnsupportedCSharpConstruct(f"Unsupported expression type: {node.type}")


def find_method(csharp_source, method_name):
    """Finds the first method with the given name -- across ALL classes
    in the file (analogous to java_bridge.find_method)."""
    parser = Parser(_LANGUAGE)
    tree = parser.parse(csharp_source.encode("utf-8"))

    def walk(node):
        if node.type == "method_declaration" and _text(node.child_by_field_name("name")) == method_name:
            return node
        for child in node.children:
            found = walk(child)
            if found is not None:
                return found
        return None

    result = walk(tree.root_node)
    if result is None:
        raise UnsupportedCSharpConstruct(f"Method '{method_name}' not found")
    return result


def transpile_csharp_method(csharp_source, method_name, param_names=None, python_function_name=None, field_rename=None):
    """Translates a single C# method deterministically into Python
    source that engine.py can verify UNCHANGED. Raises
    UnsupportedCSharpConstruct with the exact error location for anything
    outside the supported subset. param_names: see java_bridge.py --
    engine.py requires exactly matching parameter names between
    legacy_fn and modern_fn. field_rename: dict of C# field name -> target
    name, e.g. {"Balance": "balance"} -- C#'s PascalCase convention for
    public fields otherwise does not match the record_types spec (which
    typically derives snake_case from COBOL field names)."""
    method = find_method(csharp_source, method_name)
    py_name = python_function_name or method_name
    params_node = method.child_by_field_name("parameters")
    csharp_param_names = [_text(p.child_by_field_name("name")) for p in params_node.named_children]
    if param_names is not None:
        if len(param_names) != len(csharp_param_names):
            raise UnsupportedCSharpConstruct(
                f"param_names has {len(param_names)} entries, the method has {len(csharp_param_names)} parameters"
            )
        rename = dict(zip(csharp_param_names, param_names))
        final_param_names = param_names
    else:
        rename = {}
        final_param_names = csharp_param_names

    bridge = CSharpToPythonBridge(param_rename=rename, field_rename=field_rename)
    bridge.transpile_method(method)
    body = "\n".join(bridge.lines) if bridge.lines else "    pass"
    return f"def {py_name}({', '.join(final_param_names)}):\n{body}\n"
