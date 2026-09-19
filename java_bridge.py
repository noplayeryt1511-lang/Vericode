# -*- coding: utf-8 -*-
"""
Java frontend for VeriCode: the first target language besides Python.

STRATEGIC RATIONALE (see competitor comparison): VeriCode does NOT
compete with tools like Easy COBOL Migrator/Ispirer/TSRI at translating
to Java/C#/Rust -- they are mature at that. VeriCode adds the proof
layer they are missing. For that to work, our engine must be able to
verify code that OTHER tools have already translated to Java --
not just our own Python translation.

ARCHITECTURE: exactly like cobol_transpile.py (COBOL -> our Python
subset), Java is translated here into the SAME Python subset, via
`javalang` (a pure Python parser, PyPI, no JVM needed -- the same
philosophy as with cobol-py). engine.py itself is NOT changed -- the
generated Python source is verified exactly like any other `modern_fn`.

SUPPORTED SUBSET (deliberately narrow, grows incrementally):
  - A single static method with primitive int/long parameters
    and return type
  - Local variable declarations (with or without an initializer)
  - Assignments, arithmetic operators (+ - * / %), comparisons,
    logical operators (&& || !)
  - if/else if/else (arbitrarily nested)
  - return

NOT supported (clear error message, no guessing): loops,
arrays, objects/classes with multiple methods, method calls, casts,
string types, exceptions.
"""

import javalang


class UnsupportedJavaConstruct(Exception):
    """A Java construct that this bridge does not (yet) cover --
    deliberately NOT guessed at or ignored."""
    pass


_INT_TYPES = {"int", "long", "short", "byte"}


class JavaToPythonBridge:
    def __init__(self, param_rename=None):
        self.lines = []
        self.indent = 1
        self.param_rename = param_rename or {}  # Java parameter name -> desired Python name

    def _emit(self, line):
        self.lines.append("    " * self.indent + line)

    def transpile_method(self, method):
        for param in method.parameters:
            is_primitive = isinstance(param.type, javalang.tree.BasicType) and param.type.name in _INT_TYPES
            is_string = isinstance(param.type, javalang.tree.ReferenceType) and param.type.name == "String"
            is_reference = isinstance(param.type, javalang.tree.ReferenceType) and param.type.name != "String"
            if not (is_primitive or is_string or is_reference):
                raise UnsupportedJavaConstruct(
                    f"Parameter '{param.name}' has an unsupported type: {param.type} "
                    f"(only primitive int/long/short/byte, arrays thereof, String, or reference types as records)"
                )
            # Array parameters (e.g. int[]) are structurally also a
            # BasicType (just with param.type.dimensions set), so they
            # are already covered by the is_primitive branch above.
            # Treated as a table -- Java does NOT know the actual length
            # (the COBOL OCCURS equivalent), so the caller must supply
            # table_types ITSELF, exactly like record_types for
            # reference-type parameters.
            # String parameters are mapped directly onto our existing
            # PicX/Z3-string infrastructure (like a COBOL PicX field)
            # -- NO record handling, since a String has no field access
            # via dot notation, but is a value as a whole.
            # Reference-type parameters (a class with public fields) are
            # treated as a record -- Java does NOT know the actual field
            # widths (PicField) (an "int" carries no COBOL PIC precision),
            # so the caller must supply record_types ITSELF, exactly as
            # for any other target language in this project.
        is_string_return = (isinstance(method.return_type, javalang.tree.ReferenceType)
                             and method.return_type.name == "String")
        if method.return_type is not None and not is_string_return and not (
                isinstance(method.return_type, javalang.tree.BasicType) and method.return_type.name in _INT_TYPES):
            raise UnsupportedJavaConstruct(
                f"Only a primitive int/long/short/byte return type or String is supported, got: {method.return_type}"
            )
        self.transpile_block(method.body)

    def transpile_block(self, statements):
        if not statements:
            self._emit("pass")
            return
        i = 0
        while i < len(statements):
            stmt = statements[i]
            nxt = statements[i + 1] if i + 1 < len(statements) else None
            if (isinstance(nxt, javalang.tree.WhileStatement)
                    and isinstance(stmt, javalang.tree.LocalVariableDeclaration)
                    and len(stmt.declarators) == 1
                    and isinstance(stmt.declarators[0].initializer, javalang.tree.Literal)):
                loop_var = stmt.declarators[0].name
                start = int(stmt.declarators[0].initializer.value.rstrip("lL"))
                if self._try_emit_counted_while(loop_var, start, nxt):
                    i += 2
                    continue
            self.transpile_statement(stmt)
            i += 1

    def _try_emit_counted_while(self, loop_var, start, while_stmt):
        """Recognizes the pattern 'int i = START; while (i (< | <= | > | >=)
        <constant>) { ...; i++ (or i--); }' -- a countable loop, only
        syntactically written as while instead of for -- and translates
        it to 'for i in range(...)', EXACTLY like our normal for loop.
        engine.py does NOT support unbounded while loops symbolically
        (see engine.py: ast.While is always rejected), so every
        while loop MUST match this one pattern or be rejected entirely
        -- no middle ground. Returns False (not an error!) when the
        pattern does not match, so the caller processes BOTH statements
        normally instead (and thus, where applicable, with a clear error)."""
        cond = while_stmt.condition
        if not (isinstance(cond, javalang.tree.BinaryOperation)
                and isinstance(cond.operandl, javalang.tree.MemberReference)
                and cond.operandl.member == loop_var
                and isinstance(cond.operandr, javalang.tree.Literal)
                and cond.operator in ("<", "<=", ">", ">=")):
            return False
        bound = int(cond.operandr.value.rstrip("lL"))

        body = while_stmt.body.statements if isinstance(while_stmt.body, javalang.tree.BlockStatement) else [while_stmt.body]
        if not body:
            return False
        last = body[-1]
        if not (isinstance(last, javalang.tree.StatementExpression)
                and isinstance(last.expression, javalang.tree.MemberReference)
                and last.expression.member == loop_var
                and last.expression.postfix_operators in (["++"], ["--"])):
            return False
        step = 1 if last.expression.postfix_operators == ["++"] else -1

        if step == 1:
            if cond.operator not in ("<", "<="):
                return False
            stop = bound if cond.operator == "<" else bound + 1
        else:
            if cond.operator not in (">", ">="):
                return False
            stop = bound if cond.operator == ">" else bound - 1

        self._emit(f"for {loop_var} in range({start}, {stop}, {step}):")
        self.indent += 1
        self.transpile_block(body[:-1])  # do NOT emit the last statement (the increment) again -- it's already in range()
        self.indent -= 1
        return True

    def _stmt_WhileStatement(self, stmt):
        # Only reached when NO matching initialization directly preceded
        # it (see transpile_block) -- without that, it cannot be safely
        # decided whether the loop is bounded at all.
        raise UnsupportedJavaConstruct(
            "while loop not supported -- only the pattern 'int i = START; while (i OP CONSTANT) "
            "{ ...; i++/i--; }' (immediately consecutive) is recognized as a bounded counting loop. "
            "engine.py cannot symbolically prove unbounded while loops."
        )

    def transpile_statement(self, stmt):
        type_name = type(stmt).__name__
        handler = getattr(self, f"_stmt_{type_name}", None)
        if handler is None:
            raise UnsupportedJavaConstruct(f"Unsupported Java statement: {type_name}")
        handler(stmt)

    # --- Local variable declaration ("int x;" or "int x = 5;") --------
    def _stmt_LocalVariableDeclaration(self, stmt):
        for decl in stmt.declarators:
            if decl.initializer is not None:
                val = self.transpile_expr(decl.initializer)
                self._emit(f"{decl.name} = {val}")
            # without an initializer: emit nothing -- Java enforces
            # "definite assignment" before use, and our engine requires
            # the same (see engine.py If-merge fix) -> compatible,
            # as long as the Java source itself compiles validly.

    # --- Assignment as a standalone statement ---------------------------
    _COMPOUND_OPS = {"+=": "+", "-=": "-", "*=": "*", "/=": "//", "%=": "%"}

    def _stmt_StatementExpression(self, stmt):
        expr = stmt.expression
        if isinstance(expr, javalang.tree.Assignment):
            target = self.transpile_expr(expr.expressionl)
            val = self.transpile_expr(expr.value)
            if expr.type == "=":
                self._emit(f"{target} = {val}")
            elif expr.type in self._COMPOUND_OPS:
                self._emit(f"{target} = ({target} {self._COMPOUND_OPS[expr.type]} {val})")
            else:
                raise UnsupportedJavaConstruct(f"Assignment operator not supported: '{expr.type}'")
            return
        raise UnsupportedJavaConstruct(f"Unsupported expression as statement: {type(expr).__name__}")

    # --- IF/ELSE -----------------------------------------------------------
    def _stmt_IfStatement(self, stmt):
        cond = self.transpile_expr(stmt.condition)
        self._emit(f"if {cond}:")
        self.indent += 1
        self._transpile_nested_block(stmt.then_statement)
        self.indent -= 1
        if stmt.else_statement is not None:
            if isinstance(stmt.else_statement, javalang.tree.IfStatement):
                # "else if" -- Java nests this as its own IfStatement
                # inside else_statement, but we want a clean "elif"
                # instead of an extra indentation level.
                self._emit_elif(stmt.else_statement)
            else:
                self._emit("else:")
                self.indent += 1
                self._transpile_nested_block(stmt.else_statement)
                self.indent -= 1

    def _emit_elif(self, stmt):
        cond = self.transpile_expr(stmt.condition)
        self._emit(f"elif {cond}:")
        self.indent += 1
        self._transpile_nested_block(stmt.then_statement)
        self.indent -= 1
        if stmt.else_statement is not None:
            if isinstance(stmt.else_statement, javalang.tree.IfStatement):
                self._emit_elif(stmt.else_statement)
            else:
                self._emit("else:")
                self.indent += 1
                self._transpile_nested_block(stmt.else_statement)
                self.indent -= 1

    def _transpile_nested_block(self, stmt):
        if isinstance(stmt, javalang.tree.BlockStatement):
            self.transpile_block(stmt.statements)
        else:
            self.transpile_statement(stmt)  # a single statement without { }

    # --- FOR loop (only the "for (int i=A; i<B; i++)" pattern with
    # CONSTANT bounds -- data-dependent bounds are just as impossible
    # to prove symbolically here as with COBOL PERFORM VARYING, see
    # cobol_transpile.py for the same restriction) -----------------------
    # --- SWITCH (analogous to COBOL EVALUATE) --------------------------------
    def _stmt_SwitchStatement(self, stmt):
        subject = self.transpile_expr(stmt.expression)
        first = True
        default_case = None
        for case in stmt.cases:
            body = list(case.statements)
            if not case.case:
                # "default:" -- handle separately, must be emitted LAST
                # (Python's 'else' comes at the end, regardless of where
                # 'default:' appeared in the Java source)
                default_case = body
                continue
            self._require_break_and_strip(body, case)
            values = [self.transpile_expr(v) for v in case.case]
            cond = " or ".join(f"({subject} == {v})" for v in values)
            self._emit(f"{'if' if first else 'elif'} {cond}:")
            first = False
            self.indent += 1
            self._emit_case_body(body)
            self.indent -= 1
        if default_case is not None:
            self._require_break_and_strip(default_case, None)
            self._emit("else:")
            self.indent += 1
            self._emit_case_body(default_case)
            self.indent -= 1
        elif first:
            raise UnsupportedJavaConstruct("SWITCH without any case/default")

    def _require_break_and_strip(self, body, case):
        """Checks that a case branch ends with 'break;' (NO real
        fall-through into the next branch -- that would have different
        semantics than our If/Elif translation) and removes the break
        itself from the statement list to be translated (mutates body in place)."""
        if not body or not isinstance(body[-1], javalang.tree.BreakStatement):
            if case is not None:
                values = ", ".join(str(getattr(v, "value", v)) for v in case.case)
                label = f"case {values}"
            else:
                label = "default"
            raise UnsupportedJavaConstruct(
                f"SWITCH branch ({label}) does not end with 'break;' -- real "
                f"fall-through into the next branch is not supported"
            )
        body.pop()

    def _emit_case_body(self, statements):
        if not statements:
            self._emit("pass")
            return
        for s in statements:
            self.transpile_statement(s)

    def _stmt_ForStatement(self, stmt):
        control = stmt.control
        if not isinstance(control, javalang.tree.ForControl):
            raise UnsupportedJavaConstruct("Only classic 'for (init; cond; update)' loops are supported (no for-each)")

        init = control.init
        if not (isinstance(init, javalang.tree.VariableDeclaration) and len(init.declarators) == 1):
            raise UnsupportedJavaConstruct("FOR init must be exactly ONE variable declaration, e.g. 'int i = 0'")
        decl = init.declarators[0]
        if not isinstance(decl.initializer, javalang.tree.Literal):
            raise UnsupportedJavaConstruct("FOR start value must be a constant literal (not a variable)")
        loop_var = decl.name
        start = int(decl.initializer.value.rstrip("lL"))

        cond = control.condition
        if not (isinstance(cond, javalang.tree.BinaryOperation)
                and isinstance(cond.operandl, javalang.tree.MemberReference)
                and cond.operandl.member == loop_var
                and isinstance(cond.operandr, javalang.tree.Literal)
                and cond.operator in ("<", "<=", ">", ">=")):
            raise UnsupportedJavaConstruct(
                f"FOR condition must be '{loop_var} (< | <= | > | >=) <constant>', "
                f"no compound or data-dependent bound"
            )
        bound = int(cond.operandr.value.rstrip("lL"))

        if len(control.update) != 1 or not isinstance(control.update[0], javalang.tree.MemberReference):
            raise UnsupportedJavaConstruct("FOR update must be exactly ONE simple 'i++'/'i--'")
        upd = control.update[0]
        if upd.member != loop_var or upd.postfix_operators not in (["++"], ["--"]):
            raise UnsupportedJavaConstruct(
                f"FOR update must be '{loop_var}++' or '{loop_var}--' (not 'i += N' or similar)"
            )
        step = 1 if upd.postfix_operators == ["++"] else -1

        if step == 1:
            if cond.operator not in ("<", "<="):
                raise UnsupportedJavaConstruct(f"'{loop_var}++' needs '<' or '<=' as the condition, not '{cond.operator}'")
            stop = bound if cond.operator == "<" else bound + 1
        else:
            if cond.operator not in (">", ">="):
                raise UnsupportedJavaConstruct(f"'{loop_var}--' needs '>' or '>=' as the condition, not '{cond.operator}'")
            stop = bound if cond.operator == ">" else bound - 1

        self._emit(f"for {loop_var} in range({start}, {stop}, {step}):")
        self.indent += 1
        self._transpile_nested_block(stmt.body)
        self.indent -= 1

    # --- RETURN --------------------------------------------------------
    def _stmt_ReturnStatement(self, stmt):
        if stmt.expression is None:
            raise UnsupportedJavaConstruct("'return;' without a value is not supported (function must return a value)")
        val = self.transpile_expr(stmt.expression)
        self._emit(f"return {val}")

    # --- TRY/CATCH -- deliberately narrowly scoped to ONE pattern --------------
    # Our engine symbolically evaluates pure, side-effect-free functions
    # -- REAL control-flow unwinding (exception unwinding across
    # multiple call levels) does not structurally fit this model.
    # SUPPORTED is therefore ONLY the by far most common real-world pattern:
    # 'try { target = a / b; } catch (ArithmeticException e) { target =
    # <fallback>; }' -- division with a zero guard, which is already by
    # definition a conditional expression (z3.If), not a real control-flow problem.
    # ANYTHING more complex (multiple statements, multiple catch branches,
    # nested try, exception types other than arithmetic-related ones)
    # is clearly rejected, not guessed at.
    _ARITHMETIC_EXCEPTION_TYPES = {"ArithmeticException", "RuntimeException", "Exception"}

    def _stmt_TryStatement(self, stmt):
        if stmt.resources or stmt.finally_block:
            raise UnsupportedJavaConstruct("try-with-resources or a finally block is not supported")
        if len(stmt.block) != 1 or not isinstance(stmt.block[0], javalang.tree.StatementExpression):
            raise UnsupportedJavaConstruct(
                "try block must contain EXACTLY ONE statement, an assignment with division "
                "('target = a / b;') -- anything more complex is deliberately not supported"
            )
        try_assign = stmt.block[0].expression
        if not (isinstance(try_assign, javalang.tree.Assignment)
                and isinstance(try_assign.expressionl, javalang.tree.MemberReference)
                and isinstance(try_assign.value, javalang.tree.BinaryOperation)
                and try_assign.value.operator == "/"):
            raise UnsupportedJavaConstruct(
                "try block must contain EXACTLY ONE division assignment ('target = a / b;')"
            )
        target = self.param_rename.get(try_assign.expressionl.member, try_assign.expressionl.member)
        numerator = self.transpile_expr(try_assign.value.operandl)
        denominator = self.transpile_expr(try_assign.value.operandr)

        if len(stmt.catches) != 1:
            raise UnsupportedJavaConstruct("Only EXACTLY ONE catch branch is supported")
        catch = stmt.catches[0]
        caught_types = set(catch.parameter.types)
        if not caught_types & self._ARITHMETIC_EXCEPTION_TYPES:
            raise UnsupportedJavaConstruct(
                f"Only arithmetic-related exception types are supported "
                f"({sorted(self._ARITHMETIC_EXCEPTION_TYPES)}), got: {sorted(caught_types)}"
            )
        if len(catch.block) != 1 or not isinstance(catch.block[0], javalang.tree.StatementExpression):
            raise UnsupportedJavaConstruct(
                "catch block must contain EXACTLY ONE statement, an assignment to the SAME target "
                "('target = <fallback>;')"
            )
        catch_assign = catch.block[0].expression
        if not (isinstance(catch_assign, javalang.tree.Assignment)
                and isinstance(catch_assign.expressionl, javalang.tree.MemberReference)
                and catch_assign.expressionl.member == try_assign.expressionl.member):
            raise UnsupportedJavaConstruct("catch block must assign to the SAME target as the try block")
        fallback = self.transpile_expr(catch_assign.value)

        # 'a / b' with a zero guard is by definition a conditional
        # expression -- not a new concept, just our existing ternary
        # pattern (z3.If in engine.py), already familiar from INSPECT.
        self._emit(f"{target} = ({fallback} if {denominator} == 0 else ({numerator} // {denominator}))")

    # --- Expressions -----------------------------------------------------
    _BIN_OPS = {"+": "+", "-": "-", "*": "*", "/": "//", "%": "%",
                "==": "==", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">=",
                "&&": "and", "||": "or"}

    def transpile_expr(self, node):
        if isinstance(node, javalang.tree.Literal):
            val = node.value
            if val is None:
                raise UnsupportedJavaConstruct("Literal without a value is not supported")
            return val.rstrip("lL")  # Java allows "100L" for long literals
        if isinstance(node, javalang.tree.MemberReference):
            if node.qualifier:
                # qualifier can be a CHAINED sequence (e.g. "p.addr"
                # for "p.addr.zip") -- only the FIRST segment is the
                # actual parameter/variable name and needs renaming;
                # the rest of the chain is left unchanged.
                segments = node.qualifier.split(".")
                segments[0] = self.param_rename.get(segments[0], segments[0])
                base = ".".join(segments)
                return f"{base}.{node.member}"
            base = self.param_rename.get(node.member, node.member)
            if node.selectors:
                if len(node.selectors) != 1 or not isinstance(node.selectors[0], javalang.tree.ArraySelector):
                    raise UnsupportedJavaConstruct(
                        f"Only a single array access 'a[i]' is supported (no 'a[i][j]', "
                        f"no method-call chaining): {node}"
                    )
                index_py = self.transpile_expr(node.selectors[0].index)
                return f"{base}[{index_py}]"
            return base
        if isinstance(node, javalang.tree.BinaryOperation):
            if node.operator not in self._BIN_OPS:
                raise UnsupportedJavaConstruct(f"Operator not supported: {node.operator}")
            left = self.transpile_expr(node.operandl)
            right = self.transpile_expr(node.operandr)
            return f"({left} {self._BIN_OPS[node.operator]} {right})"
        if isinstance(node, javalang.tree.Assignment):
            raise UnsupportedJavaConstruct("Assignment inside an expression (e.g. 'a = b = c') is not supported")
        if isinstance(node, javalang.tree.TernaryExpression):
            cond = self.transpile_expr(node.condition)
            if_true = self.transpile_expr(node.if_true)
            if_false = self.transpile_expr(node.if_false)
            return f"({if_true} if {cond} else {if_false})"
        raise UnsupportedJavaConstruct(f"Unsupported expression type: {type(node).__name__}")


def find_method(java_source, method_name):
    """Finds the first method with the given name -- across ALL classes
    in the file (multiple classes are allowed, e.g. a main class with
    the method plus a plain data class as the record parameter type,
    see the applyFee example)."""
    tree = javalang.parse.parse(java_source)
    for cls in tree.types:
        for member in cls.body:
            if isinstance(member, javalang.tree.MethodDeclaration) and member.name == method_name:
                return member
    raise UnsupportedJavaConstruct(f"Method '{method_name}' not found (searched: {[t.name for t in tree.types]})")


def transpile_java_method(java_source, method_name, param_names=None, python_function_name=None):
    """Translates a single Java method deterministically into Python
    source that engine.py can verify UNCHANGED. Raises
    UnsupportedJavaConstruct with the exact error location for anything
    outside the supported subset -- no partial translation.

    param_names: optional list of target names (same order as the
    Java parameters) -- engine.py requires EXACTLY matching parameter
    names between legacy_fn and modern_fn (see prove_equivalence), but
    Java uses camelCase (wsInc) while our COBOL reference uses snake_case
    (ws_inc). WITHOUT param_names, Java's own names are kept -- then
    the caller must ensure the names match."""
    method = find_method(java_source, method_name)
    py_name = python_function_name or method.name
    java_param_names = [p.name for p in method.parameters]
    if param_names is not None:
        if len(param_names) != len(java_param_names):
            raise UnsupportedJavaConstruct(
                f"param_names has {len(param_names)} entries, the method has "
                f"{len(java_param_names)} parameters"
            )
        rename = dict(zip(java_param_names, param_names))
        final_param_names = param_names
    else:
        rename = {}
        final_param_names = java_param_names

    bridge = JavaToPythonBridge(param_rename=rename)
    bridge.transpile_method(method)
    body = "\n".join(bridge.lines) if bridge.lines else "    pass"
    return f"def {py_name}({', '.join(final_param_names)}):\n{body}\n"
