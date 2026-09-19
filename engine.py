"""
VeriCode v2 — Tiered Verification Engine (Prototype)

Takes two Python functions (a stand-in for "legacy source" and
"LLM-migrated target code"), symbolically executes them over their AST,
and attempts:

  1. PROVEN            -> Z3 proves equivalence for ALL inputs (UNSAT of the negation)
  2. VERIFIED-BY-TESTING -> the code contains constructs we cannot prove
                            symbolically (unbounded loops, external calls) ->
                            differential fuzzing against real values
  3. FLAGGED            -> fuzzing finds a difference -> counterexample returned

Deliberately limited (like the "triage layer" in the real system):
  - Straight-line code & loops with a static range() -> symbolically unrollable -> Z3
  - Everything else (while, external I/O, recursive calls) -> differential testing
"""

import ast
import inspect
import random
import textwrap
from dataclasses import dataclass, field
from enum import Enum

import z3

from concolic import concolic_search


class Label(Enum):
    PROVEN = "PROVEN"
    VERIFIED_BY_TESTING = "VERIFIED-BY-TESTING"
    FLAGGED = "FLAGGED FOR MANUAL REVIEW"


@dataclass
class PicField:
    """Models a COBOL PIC clause such as PIC 9(5)V99 COMP-3: total_digits
    digits in total, decimal_digits of them after the decimal point.
    Values are kept as a scaled integer (x scale). Assignment to a
    variable typed this way automatically applies the silent COBOL field
    overflow (truncation of the upper digits) -- that is the core of
    Path 1.1.

    signed: PIC S9(...) -- a signed field. Defaults to False, since most
    financial fields (amounts, quantities) are unsigned in practice."""
    total_digits: int
    decimal_digits: int = 0
    signed: bool = False

    @property
    def scale(self):
        return 10 ** self.decimal_digits

    @property
    def modulus(self):
        return 10 ** self.total_digits

    def truncate(self, scaled_int_expr):
        """COBOL truncation on field overflow: keeps only the lowest
        total_digits digits of the MAGNITUDE -- the sign is preserved
        (sign-nibble semantics for signed COMP-3, stored separately from
        the data digits). For unsigned fields, plain modulo is correct.
        NOT for signed fields: SMT-LIB/Z3 Euclidean modulo always yields
        a non-negative result for negative values -- which would silently
        flip the sign on overflow. Hence the explicit separate handling
        of magnitude + sign here."""
        if not self.signed:
            return scaled_int_expr % self.modulus
        magnitude = z3.If(scaled_int_expr < 0, -scaled_int_expr, scaled_int_expr)
        truncated_magnitude = magnitude % self.modulus
        sign = z3.If(scaled_int_expr < 0, -1, 1)
        return sign * truncated_magnitude

    def default_bounds(self):
        """The valid value range implied by the PIC clause (scaled), e.g.
        PIC 9(5)V99 unsigned -> (0, 99999). Used to automatically derive
        input_bounds when a parameter is itself declared as a PIC field
        -- see resolve_input_bounds()."""
        if self.signed:
            return (-(self.modulus - 1), self.modulus - 1)
        return (0, self.modulus - 1)


@dataclass
class PicX:
    """Models a COBOL PIC X(n) clause: an alphanumeric fixed-length
    field. Values are carried as a Z3 string (z3.StringSort()), not a
    number.

    MOVE semantics on assignment to a PIC X field: left-justified,
    padded on the right with spaces if the source value is shorter,
    truncated on the right if it is longer -- ALWAYS exactly `length`
    characters in the result. This is the alphanumeric counterpart to
    field-width truncation for PicField."""
    length: int

    def normalize(self, z3_string_expr):
        """Concat with `length` spaces, then take the first `length`
        characters -> covers both padding AND truncation in one
        expression."""
        padded = z3.Concat(z3_string_expr, z3.StringVal(" " * self.length))
        return z3.SubString(padded, 0, self.length)


@dataclass
class TableField:
    """Models a COBOL OCCURS clause:
       05 MONTHLY-AMOUNT PIC 9(7)V99 OCCURS 12 TIMES.
    All elements of an OCCURS table have the same type (element). occurs
    is the declared element count (informational -- index bounds are NOT
    automatically enforced in this version, see the limitation in
    SymbolicEvaluator).

    Internally, the table is represented as a real Z3 array (z3.Array,
    IntSort -> Element), not as an enumeration of individual constants --
    this supports both constant AND symbolic indices (e.g. a loop
    variable), via z3.Select (read) and z3.Store (write).

    element: PicField or PicX (a scalar table) -- OR a dict
    {field_name: PicField|PicX} for a TABLE OF RECORDS (array-of-struct,
    e.g. "05 LINE-ITEM OCCURS 50 TIMES. 10 QUANTITY... 10 PRICE..."). In
    the dict case, a Z3 datatype sort with a constructor and accessor
    functions per field is built internally -- table[i].field_name then
    reads/writes via Select+Accessor resp. Select+reconstruction+Store.
    LIMITATION: only FLAT record specs are supported as a table element
    (no nested groups WITHIN a table element)."""
    element: object
    occurs: int


def _build_record_datatype(sort_name, spec, arg_type):
    """Builds a Z3 datatype sort for a record-spec dict
    {field_name: PicField|PicX|dict} -- the constructor is called "mk",
    and each field gets its own accessor function with the same name. A
    dict-valued field is turned RECURSIVELY into its own nested datatype
    sort (arbitrary depth -- so a table whose element itself contains
    another group with further groups works automatically).

    Returns (DatatypeSortRef, field_order, nested_specs):
      - field_order: fixed order of the constructor arguments (important
        for read-modify-write when writing a single field)
      - nested_specs: dict[field_name -> (nested_sort, nested_field_order,
        nested_specs)] for each dict-valued field -- recursive, so that
        an arbitrarily deep attribute access (table[i].a.b.c) can be resolved"""
    field_order = list(spec.keys())
    nested_specs = {}
    ctor_args = []
    for fname in field_order:
        value = spec[fname]
        if isinstance(value, dict):
            sub_sort, sub_order, sub_nested = _build_record_datatype(f"{sort_name}__{fname}", value, arg_type)
            nested_specs[fname] = (sub_sort, sub_order, sub_nested)
            ctor_args.append((fname, sub_sort))
        else:
            ctor_args.append((fname, z3.StringSort() if isinstance(value, PicX) else arg_type))
    dt = z3.Datatype(sort_name)
    dt.declare("mk", *ctor_args)
    dt = dt.create()
    return dt, field_order, nested_specs


@dataclass
class VerificationResult:
    label: Label
    detail: str
    counterexample: dict = None
    coverage: int = None
    proof_note: str = None
    index_warnings: list = None
    smt2: str = None  # optional SMT-LIB2 export of the proof obligation — see export_smt2=True


class UnsupportedConstruct(Exception):
    """Signals: this code path is not symbolically provable -> fall back to fuzzing."""
    pass


class SymbolicEvaluator:
    """A very limited symbolic execution of Python AST -> Z3 expressions.

    Supported: assignments, if/else, for-i-in-range(const), arithmetic,
    comparisons, return, as well as record/group field access via
    attributes (account.balance). All numeric values run through z3.Real
    OR through scaled z3.Int (arg_type=IntSort) for COMP-3 field
    semantics.

    field_types: dict[varname -> PicField]. Every variable (parameter,
    local variable, or the special key "return") with a PicField
    automatically gets the COBOL-typical field-width truncation applied
    on every assignment -- exactly the silent overflow behavior that
    plain real arithmetic can never catch.

    record_types: dict[paramname -> dict[subfieldname -> PicField | dict[...]]].
    Models a COBOL group field (01 ACCOUNT-RECORD. 05 BALANCE ... 05 FEE
    ...) as a parameter whose subfields are addressed in the code via dot
    notation (account.balance, account.fee). Supports MULTI-LEVEL
    nesting -- a subfield's value can itself be a dict again (a nested
    group, e.g. invoice.customer_info.customer_id) and is expanded
    recursively. Internally, EVERY LEAF subfield gets its own Z3 Const
    under the fully composed name ("param.group.subfield") -- the same
    field_types truncation logic therefore automatically applies to
    deeply nested record subfields too, without a separate code path.
    Limitation: the record parameter itself (without .subfield) must not
    be referenced directly in the function body -- only the (possibly
    multi-level) subfields.

    table_types: dict[paramname -> TableField]. Models a COBOL OCCURS
    table as a real Z3 array (not as an enumeration of individual
    constants) -- this supports both constant and symbolic indices (a
    loop variable from for-i-in-range), via table[i] in the code
    (z3.Select on read, z3.Store on write). LIMITATION: the array index
    always runs over IntSort, regardless of the instance's arg_type --
    tables are therefore only usefully usable with arg_type=IntSort()
    (which matches practically all COMP-3 financial cases). NO automatic
    index-bounds constraints are generated (occurs is purely
    informational), and table parameters do NOT feed into the automatic
    input_bounds derivation.
    """

    def __init__(self, params, arg_type=z3.RealSort(), field_types=None,
                 record_types=None, table_types=None):
        self.arg_type = arg_type
        self.record_types = record_types or {}
        self.table_types = table_types or {}
        self.field_types = dict(field_types or {})

        # Recursively expand record_types (ARBITRARILY deeply nested) --
        # explicit field_types entries take precedence. BEFORE env is
        # built, since the sort selection below (_sort_for) already needs
        # this fully available.
        record_leaf_keys = {}  # param -> [fully expanded leaf keys]
        for p, subfields in self.record_types.items():
            leaves = []
            _flatten_record_spec(p, subfields, self.field_types, leaves)
            record_leaf_keys[p] = leaves

        self.env = {}
        self.table_record_sorts = {}  # param -> (DatatypeSortRef, field_order, spec, nested_specs) for tables of records
        for p in params:
            if p in self.table_types:
                tf = self.table_types[p]
                if isinstance(tf.element, dict):
                    record_sort, field_order, nested_specs = _build_record_datatype(f"{p}__record", tf.element, self.arg_type)
                    self.table_record_sorts[p] = (record_sort, field_order, tf.element, nested_specs)
                    self.env[p] = z3.Array(p, z3.IntSort(), record_sort)
                else:
                    elem_sort = z3.StringSort() if isinstance(tf.element, PicX) else self.arg_type
                    self.env[p] = z3.Array(p, z3.IntSort(), elem_sort)
            elif p in self.record_types:
                for key in record_leaf_keys[p]:
                    self.env[key] = z3.Const(key, self._sort_for(key))
            else:
                self.env[p] = z3.Const(p, self._sort_for(p))

        self.returned = None
        self.path_condition = z3.BoolVal(True)
        self.table_accesses = []  # [(table_name, idx_z3_expr, cond)] — for index-bounds checking
        self._current_cond = z3.BoolVal(True)

        # Parameters that are themselves a PIC field already come in as a
        # valid field value (input constraints handle that via the
        # solver) -- here, truncation is applied only on assignments
        # within the function body.

    def _apply_table_field(self, table_name, val):
        tf = self.table_types.get(table_name)
        if tf is None:
            return val
        return tf.element.normalize(val) if isinstance(tf.element, PicX) else tf.element.truncate(val)

    def _sort_for(self, key):
        """Z3 sort for a field: StringSort if it is typed as PicX,
        otherwise the numeric arg_type of the evaluator instance."""
        pic = self.field_types.get(key)
        if isinstance(pic, PicX):
            return z3.StringSort()
        return self.arg_type

    def _apply_field(self, name, val):
        pf = self.field_types.get(name)
        if pf is None:
            return val
        if isinstance(pf, PicX):
            return pf.normalize(val)
        return pf.truncate(val)

    def run(self, func):
        src = textwrap.dedent(inspect.getsource(func))
        tree = ast.parse(src)
        fn_def = tree.body[0]
        # A type-correct placeholder for 'no return on this path yet' --
        # this MUST be merged via z3.If from the very start (no special
        # case of "the first return wins unconditionally"), otherwise a
        # return statement EARLY in the source would be incorrectly
        # treated as unconditional -- see the has_returned handling above.
        return_field = self.field_types.get("return")
        if isinstance(return_field, PicX):
            self.returned = z3.StringVal("")
        else:
            self.returned = z3.RealVal(0) if self.arg_type == z3.RealSort() else z3.IntVal(0)
        self.has_returned = z3.BoolVal(False)
        self._any_return_seen = False
        self._exec_block(fn_def.body, z3.BoolVal(True))
        if not self._any_return_seen:
            raise UnsupportedConstruct("No return found on any path")
        return self.returned

    def _exec_block(self, stmts, cond):
        for stmt in stmts:
            self._exec_stmt(stmt, cond)

    def _attribute_chain_key(self, node):
        """Resolves an ARBITRARILY deep attribute chain (a.b.c.d) to its
        fully composed env key, e.g. invoice.customer_info.customer_id.
        Returns None if node is not a plain name/attribute chain (e.g. a
        function call as the base)."""
        parts = []
        cur = node
        while isinstance(cur, ast.Attribute):
            parts.append(cur.attr)
            cur = cur.value
        if isinstance(cur, ast.Name):
            parts.append(cur.id)
            return ".".join(reversed(parts))
        return None

    def _assign_target_key(self, target):
        """Resolves an assignment target to its env key: a normal
        variable -> its name; a record subfield (account.balance, also
        arbitrarily deeply nested like invoice.customer_info.customer_id)
        -> the composed key."""
        if isinstance(target, ast.Name):
            return target.id
        if isinstance(target, ast.Attribute):
            key = self._attribute_chain_key(target)
            if key is not None:
                return key
        raise UnsupportedConstruct(f"Unsupported assignment target: {ast.dump(target)}")

    def _exec_stmt(self, stmt, cond):
        self._current_cond = cond
        # An earlier 'return' statement on THIS path must block any
        # further execution -- otherwise a return statement LATER in the
        # source (but actually unreachable) would overwrite the earlier,
        # already "finished" path. See self.has_returned in run()/
        # ast.Return below -- this is a real bug, found independently of
        # the SEARCH work (an early 'return' in an if branch is a very
        # common Python pattern).
        cond = z3.And(cond, z3.Not(self.has_returned))
        if isinstance(stmt, ast.Assign):
            target_node = stmt.targets[0]
            table_chain = self._resolve_table_attr_chain(target_node) if isinstance(target_node, ast.Attribute) else None
            if table_chain is not None:
                # table[i].a.b.c = value -- a nested read-modify-write via
                # the datatype constructors at EVERY level: read the
                # current struct, carry over all fields except the
                # changed one (at every intermediate level) unchanged,
                # rebuild, write back.
                table_name, idx_node, attrs = table_chain
                levels = self._table_chain_levels(table_name, attrs)
                idx = self._eval(idx_node)
                self.table_accesses.append((table_name, idx, cond))
                val = self._eval(stmt.value)
                leaf_spec = levels[-1][2].get(attrs[-1])
                if leaf_spec is not None and not isinstance(leaf_spec, dict):
                    val = leaf_spec.normalize(val) if isinstance(leaf_spec, PicX) else leaf_spec.truncate(val)
                cur_array = self.env[table_name]
                cur_struct = z3.Select(cur_array, idx)
                new_struct = self._rebuild_nested_write(cur_struct, levels, attrs, val)
                new_array = z3.Store(cur_array, idx, new_struct)
                self.env[table_name] = z3.If(cond, new_array, cur_array)
            elif isinstance(target_node, ast.Subscript) and isinstance(target_node.value, ast.Name):
                table_name = target_node.value.id
                idx = self._eval(target_node.slice)
                self.table_accesses.append((table_name, idx, cond))
                val = self._eval(stmt.value)
                val = self._apply_table_field(table_name, val)
                cur_array = self.env[table_name]
                new_array = z3.Store(cur_array, idx, val)
                self.env[table_name] = z3.If(cond, new_array, cur_array)
            else:
                val = self._eval(stmt.value)
                target = self._assign_target_key(target_node)
                val = self._apply_field(target, val)
                self.env[target] = z3.If(cond, val, self.env.get(target, val))

        elif isinstance(stmt, ast.AugAssign):
            if isinstance(stmt.target, ast.Subscript) and isinstance(stmt.target.value, ast.Name):
                table_name = stmt.target.value.id
                idx = self._eval(stmt.target.slice)
                self.table_accesses.append((table_name, idx, cond))
                cur_array = self.env[table_name]
                cur = z3.Select(cur_array, idx)
                rhs = self._eval(stmt.value)
                new_val = self._binop(stmt.op, cur, rhs)
                new_val = self._apply_table_field(table_name, new_val)
                new_array = z3.Store(cur_array, idx, new_val)
                self.env[table_name] = z3.If(cond, new_array, cur_array)
            else:
                target = self._assign_target_key(stmt.target)
                cur = self.env[target]
                rhs = self._eval(stmt.value)
                new_val = self._binop(stmt.op, cur, rhs)
                new_val = self._apply_field(target, new_val)
                self.env[target] = z3.If(cond, new_val, cur)

        elif isinstance(stmt, ast.If):
            test = self._eval(stmt.test)
            then_cond = z3.And(cond, test)
            else_cond = z3.And(cond, z3.Not(test))
            snapshot = dict(self.env)
            self._exec_block(stmt.body, then_cond)
            then_env = dict(self.env)
            self.env = dict(snapshot)
            self._exec_block(stmt.orelse, else_cond)
            else_env = dict(self.env)
            merged = {}
            for k in set(then_env) | set(else_env):
                tv = then_env.get(k, snapshot.get(k))
                ev = else_env.get(k, snapshot.get(k))
                if tv is None or ev is None:
                    # A variable is never assigned on AT LEAST ONE code
                    # path (e.g. an IF/ELIF chain with no closing ELSE,
                    # and the variable also did not previously exist) --
                    # a z3.If() with None would crash cryptically with an
                    # internal Z3 parser error. Instead, state CLEARLY
                    # what is missing rather than silently guessing or
                    # crashing incomprehensibly.
                    raise UnsupportedConstruct(
                        f"Variable '{k}' is not defined on at least one code path "
                        f"(e.g. an IF/ELIF chain with no closing ELSE, combined with "
                        f"no prior initialization) -- cannot be symbolically merged."
                    )
                merged[k] = z3.If(test, tv, ev)
            self.env = merged

        elif isinstance(stmt, ast.For):
            # Supported: for i in range(<const>), range(<const>, <const>),
            # range(<const>, <const>, <const>) -> unrolled (all arguments
            # must be constant, no symbolic bounds).
            if not (isinstance(stmt.iter, ast.Call)
                    and isinstance(stmt.iter.func, ast.Name)
                    and stmt.iter.func.id == "range"
                    and 1 <= len(stmt.iter.args) <= 3
                    and all(isinstance(a, ast.Constant) for a in stmt.iter.args)):
                raise UnsupportedConstruct("Only bounded 'range(const[, const[, const]])' loops are supported symbolically")
            range_args = [a.value for a in stmt.iter.args]
            loop_var = stmt.target.id
            for i in range(*range_args):
                self.env[loop_var] = z3.RealVal(i) if self.arg_type == z3.RealSort() else z3.IntVal(i)
                self._exec_block(stmt.body, cond)

        elif isinstance(stmt, ast.While):
            raise UnsupportedConstruct("Unbounded while loop cannot be proven symbolically")

        elif isinstance(stmt, ast.Return):
            val = self._eval(stmt.value)
            val = self._apply_field("return", val)
            self.returned = z3.If(cond, val, self.returned)
            self.has_returned = z3.Or(self.has_returned, cond)
            self._any_return_seen = True

        elif isinstance(stmt, ast.Expr):
            if isinstance(stmt.value, ast.Call):
                raise UnsupportedConstruct("External function call is not modeled symbolically")

        else:
            raise UnsupportedConstruct(f"Unsupported construct: {type(stmt).__name__}")

    def _binop(self, op, l, r):
        is_string = hasattr(l, "sort") and l.sort() == z3.StringSort()
        if isinstance(op, ast.Add):
            if is_string:
                return z3.Concat(l, r)  # COBOL STRING concatenation
            return l + r
        if is_string:
            raise UnsupportedConstruct(f"Operator {type(op).__name__} is not supported on PIC X fields (only concatenation '+' and comparison)")
        if isinstance(op, ast.Sub):
            return l - r
        if isinstance(op, ast.Mult):
            return l * r
        if isinstance(op, ast.Div):
            return l / r
        if isinstance(op, ast.FloorDiv):
            if self.arg_type == z3.IntSort():
                return l / r  # z3 Int "/" == SMT-LIB integer division (COBOL-like)
            raise UnsupportedConstruct("Integer floor division is only supported in IntSort mode (COMP-3)")
        if isinstance(op, ast.Mod):
            if self.arg_type == z3.IntSort():
                return l % r  # z3 Int "%" == SMT-LIB mod -- needed only once REDEFINES support required it
            raise UnsupportedConstruct("Modulo is only supported in IntSort mode (COMP-3)")
        if isinstance(op, (ast.BitAnd, ast.BitOr, ast.BitXor, ast.LShift, ast.RShift)):
            # Bitwise operators -- COBOL has no notion of these, but C and
            # other systems languages use them commonly (found via the C
            # bridge proof of concept). Z3's Int sort has NO native bit
            # operations -- going via a fixed bit width (32 bits, matching
            # C's 'int') through Int2BV/BV2Int is the standard approach.
            # Deliberately interpreted as UNSIGNED (BV2Int with
            # is_signed=False) -- for pure bit-pattern operations (masks,
            # flags) this is the appropriate interpretation for this use
            # case; a signed (arithmetic) right shift would be a
            # deliberately uncovered extension.
            width = 32
            l_bv = z3.Int2BV(l, width)
            r_bv = z3.Int2BV(r, width)
            if isinstance(op, ast.BitAnd):
                result_bv = l_bv & r_bv
            elif isinstance(op, ast.BitOr):
                result_bv = l_bv | r_bv
            elif isinstance(op, ast.BitXor):
                result_bv = l_bv ^ r_bv
            elif isinstance(op, ast.LShift):
                result_bv = l_bv << r_bv
            else:
                result_bv = z3.LShR(l_bv, r_bv)  # logical (not arithmetic) right shift
            return z3.BV2Int(result_bv, is_signed=False)
        raise UnsupportedConstruct(f"Operator not supported: {type(op).__name__}")

    def _resolve_table_attr_chain(self, node):
        """Recognizes an (arbitrarily deep) chain 'table[i].a.b.c...' --
        at the very bottom a subscript on a known table variable, above
        it any number of attribute accesses. Returns (table_name,
        idx_ast_node, [attr1, attr2, ...]), or None if the pattern does
        not match (e.g. an ordinary record access without a table)."""
        attrs = []
        cur = node
        while isinstance(cur, ast.Attribute):
            attrs.append(cur.attr)
            cur = cur.value
        if not (isinstance(cur, ast.Subscript) and isinstance(cur.value, ast.Name)):
            return None
        table_name = cur.value.id
        if table_name not in self.table_record_sorts or not attrs:
            return None
        attrs.reverse()
        return table_name, cur.slice, attrs

    def _table_chain_levels(self, table_name, attrs):
        """Builds the list of (Z3 sort, field order, original spec) for
        EVERY nesting level traversed to resolve attrs -- levels[0] is
        the outermost (table-element) level, each further level
        corresponds to a nested group."""
        record_sort, field_order, spec, nested_specs = self.table_record_sorts[table_name]
        levels = [(record_sort, field_order, spec)]
        cur_spec, cur_nested = spec, nested_specs
        for attr in attrs[:-1]:  # the last attribute is the leaf field, needs no further level
            if attr not in cur_nested:
                raise UnsupportedConstruct(
                    f"Field '{attr}' in table record '{table_name}' is not a nested "
                    f"group (cannot be resolved further, e.g. '{attr}.x')"
                )
            sub_sort, sub_order, sub_nested = cur_nested[attr]
            sub_spec = cur_spec[attr]
            levels.append((sub_sort, sub_order, sub_spec))
            cur_spec, cur_nested = sub_spec, sub_nested
        return levels

    def _rebuild_nested_write(self, cur_struct, levels, attrs, new_leaf_val):
        """Recursively builds a new nested struct in which ONLY the leaf
        field (the last element in attrs) is changed -- all other fields
        are carried over unchanged from the old struct at EVERY level
        (a nested read-modify-write)."""
        sort, field_order, _spec = levels[0]
        attr = attrs[0]
        if attr not in field_order:
            raise UnsupportedConstruct(f"Unknown field '{attr}' in record sort {sort}")
        if len(attrs) == 1:
            new_field_val = new_leaf_val
        else:
            sub_struct = getattr(sort, attr)(cur_struct)
            new_field_val = self._rebuild_nested_write(sub_struct, levels[1:], attrs[1:], new_leaf_val)
        new_values = [
            new_field_val if fname == attr else getattr(sort, fname)(cur_struct)
            for fname in field_order
        ]
        return sort.mk(*new_values)

    def _eval(self, node):
        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                # MUST come before the str/int check: Python's bool is a
                # subclass of int, and without this case True/False would
                # be incorrectly converted to IntVal(1)/IntVal(0) instead
                # of a real z3.BoolVal -- a previously latent bug that
                # only became visible once SEARCH (a COBOL statement, see
                # cobol_transpile.py) was supported, because before that
                # a plain boolean flag variable was never combined with a
                # 'not'/boolean context.
                return z3.BoolVal(node.value)
            if isinstance(node.value, str):
                return z3.StringVal(node.value)
            return z3.RealVal(node.value) if self.arg_type == z3.RealSort() else z3.IntVal(node.value)
        if isinstance(node, ast.BoolOp):
            # and/or -- this was previously NOT supported (a genuine gap
            # found via external COBOL code): any COMPUTE condition with
            # AND/OR (e.g. generated from cobol_transpile.py) previously
            # failed on the symbolic proof path and silently fell back to
            # fuzzing (VERIFIED-BY-TESTING instead of PROVEN/FLAGGED).
            # Evaluate the values individually and recursively, then
            # combine with z3.And/z3.Or (short-circuit evaluation is
            # irrelevant here, since all values are symbolic and
            # side-effect-free anyway).
            values = [self._eval(v) for v in node.values]
            if isinstance(node.op, ast.And):
                return z3.And(*values)
            if isinstance(node.op, ast.Or):
                return z3.Or(*values)
            raise UnsupportedConstruct(f"Boolean operator not supported: {type(node.op).__name__}")
        if isinstance(node, ast.IfExp):
            # Ternary expression "X if COND else Y" -- generally useful,
            # needed specifically for INSPECT TALLYING/REPLACING
            # (positional character checking, see cobol_transpile.py).
            test = self._eval(node.test)
            body = self._eval(node.body)
            orelse = self._eval(node.orelse)
            return z3.If(test, body, orelse)
        if isinstance(node, ast.Name):
            return self.env[node.id]
        if isinstance(node, ast.Attribute):
            # table[i].a.b.c... -- MUST be checked before the generic
            # attribute resolution, since .value here traces back
            # (recursively) to a Subscript, not a plain name/attribute
            # chain.
            chain = self._resolve_table_attr_chain(node)
            if chain is not None:
                table_name, idx_node, attrs = chain
                levels = self._table_chain_levels(table_name, attrs)
                idx = self._eval(idx_node)
                self.table_accesses.append((table_name, idx, self._current_cond))
                val = z3.Select(self.env[table_name], idx)
                for level, attr in zip(levels, attrs):
                    sort, field_order, _spec = level
                    if attr not in field_order:
                        raise UnsupportedConstruct(f"Unknown field '{attr}' in table record {table_name}")
                    val = getattr(sort, attr)(val)
                return val
            key = self._attribute_chain_key(node)
            if key is None or key not in self.env:
                raise UnsupportedConstruct(f"Unknown record subfield: {ast.dump(node)}")
            return self.env[key]
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
            table_name = node.value.id
            if table_name not in self.env:
                raise UnsupportedConstruct(f"Unknown table: {table_name}")
            idx = self._eval(node.slice)
            self.table_accesses.append((table_name, idx, self._current_cond))
            return z3.Select(self.env[table_name], idx)
        if isinstance(node, ast.BinOp):
            return self._binop(node.op, self._eval(node.left), self._eval(node.right))
        if isinstance(node, ast.Compare):
            l = self._eval(node.left)
            op = node.ops[0]
            r = self._eval(node.comparators[0])
            is_string = hasattr(l, "sort") and l.sort() == z3.StringSort()
            if isinstance(op, ast.Eq):
                return l == r
            if isinstance(op, ast.NotEq):
                return l != r
            if is_string:
                raise UnsupportedConstruct(f"Comparison operator {type(op).__name__} is not supported on PIC X fields (only ==, !=)")
            if isinstance(op, ast.Lt):
                return l < r
            if isinstance(op, ast.LtE):
                return l <= r
            if isinstance(op, ast.Gt):
                return l > r
            if isinstance(op, ast.GtE):
                return l >= r
            raise UnsupportedConstruct(f"Comparison operator not supported: {type(op).__name__}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "round":
            # Simplified rounding as a stand-in for COMP-3 decimal rounding
            val = self._eval(node.args[0])
            ndigits = node.args[1].value if len(node.args) > 1 else 0
            scale = 10 ** ndigits
            return z3.ToReal(z3.ToInt(val * scale + z3.RealVal("0.5"))) / scale
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in (
                "unstring_before", "unstring_after"):
            # A stand-in for COBOL UNSTRING ... DELIMITED BY ... INTO A B
            # (exactly TWO targets, ONE delimiter) -- via Z3
            # IndexOf/SubString. If NOTHING is found by the delimiter
            # (idx == -1), the ENTIRE source string ends up in the first
            # target, the second stays empty -- the same semantics as a
            # real COBOL UNSTRING with no match.
            source_val = self._eval(node.args[0])
            delim_val = self._eval(node.args[1])
            idx = z3.IndexOf(source_val, delim_val, z3.IntVal(0))
            not_found = idx == -1
            if node.func.id == "unstring_before":
                return z3.If(not_found, source_val, z3.SubString(source_val, 0, idx))
            after_start = idx + z3.Length(delim_val)
            after_len = z3.Length(source_val) - after_start
            return z3.If(not_found, z3.StringVal(""), z3.SubString(source_val, after_start, after_len))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "char_at":
            # A stand-in for COBOL INSPECT TALLYING/REPLACING (positional
            # single-character access, see cobol_transpile.py -- our
            # fields have a known fixed length, so at transpile time all
            # positions are "unrolled" there, instead of needing a
            # generic loop/slice syntax that we otherwise don't support).
            source_val = self._eval(node.args[0])
            idx_val = self._eval(node.args[1])
            return z3.SubString(source_val, idx_val, 1)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("max", "min"):
            # A stand-in for COBOL "FUNCTION MAX(...)"/"FUNCTION MIN(...)"
            # (see cobol_expr.py) -- a pairwise fold via z3.If, since Z3
            # has no built-in variadic max/min for Int/Real.
            values = [self._eval(a) for a in node.args]
            if not values:
                raise UnsupportedConstruct(f"{node.func.id}() with no arguments")
            result = values[0]
            for v in values[1:]:
                if node.func.id == "max":
                    result = z3.If(v > result, v, result)
                else:
                    result = z3.If(v < result, v, result)
            return result
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "is_numeric_string":
            # A stand-in for COBOL 'IS [NOT] NUMERIC' on PicX fields (see
            # cobol_expr.py) -- a real character-by-character check via
            # Z3 regex membership, not just a placeholder. For PicField
            # operands, the condition is instead trivially TRUE/FALSE
            # (our model allows only numeric content there anyway) --
            # this is already decided in cobol_expr.py, this function is
            # only called for PicX.
            s_val = self._eval(node.args[0])
            return z3.InRe(s_val, z3.Plus(z3.Range("0", "9")))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -self._eval(node.operand)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            # Also previously missing -- generated among other things by
            # cobol_transpile.py for "PERFORM ... UNTIL <condition>"
            # (-> "while not (...)") as well as for COBOL NOT conditions.
            return z3.Not(self._eval(node.operand))
        raise UnsupportedConstruct(f"Expression not supported: {type(node).__name__}")


def _sort_for_key(key, field_types, arg_type):
    """Z3 sort for a key outside the evaluator instance (for
    params_consts in prove_equivalence): StringSort for PicX, otherwise arg_type."""
    pic = field_types.get(key)
    return z3.StringSort() if isinstance(pic, PicX) else arg_type


def get_params(func):
    return list(inspect.signature(func).parameters.keys())


def _flatten_record_spec(prefix, spec, field_types_out, leaf_keys_out):
    """Recursively expands a (possibly multi-level nested) record_types
    specification into fully composed leaf keys
    ("param.group.subfield") -> PicField/PicX, written into
    field_types_out (via setdefault, so explicit overrides win), and
    collects all generated keys in leaf_keys_out (a list, filled in
    place)."""
    for name, value in spec.items():
        key = f"{prefix}.{name}"
        if isinstance(value, dict):
            _flatten_record_spec(key, value, field_types_out, leaf_keys_out)
        else:
            field_types_out.setdefault(key, value)
            leaf_keys_out.append(key)


def _flatten_field_types(fn):
    """Combines the function attribute .field_types with the subfield
    types recursively expanded from .record_types (param.group.subfield
    -> PicField, arbitrarily deeply nested). .field_types wins on overlap
    (explicit overrides)."""
    field_types = dict(getattr(fn, "field_types", {}))
    record_types = getattr(fn, "record_types", {})
    for p, subfields in record_types.items():
        _flatten_record_spec(p, subfields, field_types, [])
    return field_types


def _expand_param_keys(params, legacy_fn, modern_fn):
    """For every function parameter: if it is declared as a record (in
    Legacy OR Modern), its (possibly multi-level nested) leaf keys
    ("param.subfield" or "param.group.subfield") are used instead of the
    bare parameter name -- these are the actual Z3 constants that the
    SymbolicEvaluator computes with internally (see SymbolicEvaluator).

    Table parameters (the record_types counterpart for OCCURS, see
    TableField) are deliberately NOT expanded -- they are Z3 arrays, not
    constants, and in this version do not feed into
    params_consts/input_bounds."""
    legacy_records = getattr(legacy_fn, "record_types", {})
    modern_records = getattr(modern_fn, "record_types", {})
    legacy_tables = getattr(legacy_fn, "table_types", {})
    modern_tables = getattr(modern_fn, "table_types", {})
    keys = []
    for p in params:
        if p in legacy_tables or p in modern_tables:
            continue  # tables: no params_consts entry in this version
        leaves = set()
        if p in legacy_records:
            _flatten_record_spec(p, legacy_records[p], {}, (tmp := []))
            leaves.update(tmp)
        if p in modern_records:
            _flatten_record_spec(p, modern_records[p], {}, (tmp := []))
            leaves.update(tmp)
        if leaves:
            keys.extend(sorted(leaves))
        else:
            keys.append(p)
    return keys


def range_constraints(params_consts, bounds):
    """A shorthand for input constraints: bounds = {"paramname": (lo, hi), ...}
    (or "paramname.subfield" for record subfields). Builds a Z3
    conjunction from this. Keys with no entry in `bounds` remain
    unconstrained (caution: Z3 then searches the full, possibly
    unrealistic range again)."""
    conj = [z3.And(params_consts[name] >= lo, params_consts[name] <= hi)
            for name, (lo, hi) in bounds.items()]
    return z3.And(*conj) if conj else z3.BoolVal(True)


def resolve_input_bounds(keys, legacy_fn, modern_fn, explicit_bounds=None):
    """Automatically derives input_bounds from the PIC field declarations
    (direct parameters AND record subfields -- a key can be "param" or
    "param.subfield"), and supplements/overrides that with explicit
    bounds.

    Rules:
      - explicit bounds always win (explicit_bounds[key] overrides auto)
      - if a key has different PIC declarations in legacy_fn AND
        modern_fn, the NARROWER one (the intersection) is used AND a
        warning is generated -- a field-width discrepancy between the
        legacy and target system is itself a potential migration bug,
        not a detail to be silently resolved
      - keys with no PIC declaration at all remain unconstrained (as before)
    """
    explicit_bounds = explicit_bounds or {}
    legacy_field_types = _flatten_field_types(legacy_fn)
    modern_field_types = _flatten_field_types(modern_fn)

    auto_bounds = {}
    warnings = []
    for key in keys:
        if key in explicit_bounds:
            continue
        candidates = [ft[key] for ft in (legacy_field_types, modern_field_types)
                      if key in ft and not isinstance(ft[key], PicX)]
        if not candidates:
            continue
        bounds_list = [c.default_bounds() for c in candidates]
        if len(set(bounds_list)) > 1:
            warnings.append(
                f"Field '{key}': legacy and modern field widths differ "
                f"{bounds_list} -> using the narrowest bound (which can itself be a migration bug)"
            )
        lo = max(b[0] for b in bounds_list)
        hi = min(b[1] for b in bounds_list)
        auto_bounds[key] = (lo, hi)

    merged = {**auto_bounds, **explicit_bounds}
    return merged, warnings


def _check_table_index_bounds(evaluator, table_types, label, params_consts, domain_constraints):
    """Checks, for every recorded table access (Select/Store), whether an
    index OUTSIDE the declared OCCURS range [0, occurs) is possible --
    under the same input constraints as the main equivalence proof. This
    is a SEPARATE check from equivalence itself: a program can be
    exactly equivalent to its original and still access outside the
    declared table bounds (undefined behavior / memory overwrite in real
    COBOL, depending on the compiler)."""
    warnings = []
    seen = set()
    for table_name, idx_expr, cond in evaluator.table_accesses:
        tf = table_types.get(table_name)
        if tf is None:
            continue
        sig = (table_name, str(idx_expr))
        if sig in seen:
            continue
        seen.add(sig)
        solver = z3.Solver()
        solver.add(*domain_constraints)
        solver.add(cond)  # this access must lie on an actually reachable path
        solver.add(z3.Or(idx_expr < 0, idx_expr >= tf.occurs))
        if solver.check() == z3.sat:
            model = solver.model()
            witness = {str(d): model[d] for d in model.decls() if str(d) in params_consts}
            idx_val = model.evaluate(idx_expr, model_completion=True)
            warnings.append(
                f"[{label}] Table '{table_name}' (OCCURS {tf.occurs}): index {idx_val} "
                f"possible outside [0, {tf.occurs}) at {witness}"
            )
    return warnings


def prove_equivalence(legacy_fn, modern_fn, arg_type=z3.RealSort(),
                       input_bounds=None, input_constraints=None, export_smt2=False):
    """Attempts to prove equivalence for ALL inputs (Tier 1: PROVEN).

    field_types are optionally read via the function attribute
    `.field_types` (dict[varname -> PicField]) -- this keeps verify()'s
    signature unchanged, so existing callers (test_scenarios.py) keep
    working unchanged.

    record_types (optional, a function attribute): dict[paramname -> dict[subfield -> PicField]]
    for COBOL group fields/records -- the parameter is addressed in the
    code via dot notation (account.balance). LIMITATION: record support
    currently only works for the symbolic proof path (PROVEN/FLAGGED),
    NOT for the concolic/fuzzing fallback for unprovable code -- a
    record parameter would currently cause an error there.

    input_bounds: {"paramname": (lo, hi), ...} or {"paramname.subfield": (lo, hi), ...}
        for record subfields -- explicit value ranges. For fields that
        are themselves a PIC field, bounds are AUTOMATICALLY derived
        from the PIC clause if nothing explicit is given here.
    input_constraints: an optional Callable(params_consts_dict) -> z3.BoolExpr
        for more complex constraints beyond simple bounds (e.g.
        relationships between several parameters).
    export_smt2: if True, the complete proof obligation (all solver
        assertions) is included in the return value (.smt2) as SMT-LIB2
        text -- this lets an independent checker verify the proof with
        ANY SMT solver (Z3, CVC5, ...), without having to trust our
        Python code. UNSAT (our "PROVEN") resp. SAT (our "FLAGGED") must
        then match exactly -- otherwise WE have a bug, not the checker.
    """
    params = get_params(legacy_fn)
    assert params == get_params(modern_fn), "Signatures must match"
    effective_keys = _expand_param_keys(params, legacy_fn, modern_fn)

    legacy_field_types = _flatten_field_types(legacy_fn)
    modern_field_types = _flatten_field_types(modern_fn)
    legacy_record_types = getattr(legacy_fn, "record_types", {})
    modern_record_types = getattr(modern_fn, "record_types", {})
    legacy_table_types = getattr(legacy_fn, "table_types", {})
    modern_table_types = getattr(modern_fn, "table_types", {})

    combined_field_types = {**legacy_field_types, **modern_field_types}
    params_consts = {k: z3.Const(k, _sort_for_key(k, combined_field_types, arg_type))
                      for k in effective_keys}

    ev_legacy = SymbolicEvaluator(params, arg_type, field_types=legacy_field_types,
                                   record_types=legacy_record_types, table_types=legacy_table_types)
    out_legacy = ev_legacy.run(legacy_fn)

    ev_modern = SymbolicEvaluator(params, arg_type, field_types=modern_field_types,
                                   record_types=modern_record_types, table_types=modern_table_types)
    out_modern = ev_modern.run(modern_fn)

    solver = z3.Solver()
    solver.add(out_legacy != out_modern)  # search for an input where they DIFFER

    merged_bounds, bound_warnings = resolve_input_bounds(effective_keys, legacy_fn, modern_fn, input_bounds)
    if merged_bounds:
        solver.add(range_constraints(params_consts, merged_bounds))
        auto_note = " (auto-derived from PIC fields, unless explicitly set)"
        domain_note = f"within the constraints {merged_bounds}{auto_note}"
    else:
        domain_note = "over the full mathematical value range (no input constraints set/derivable)"
    if input_constraints:
        solver.add(input_constraints(params_consts))
        domain_note += " + user-defined constraints"
    if bound_warnings:
        domain_note += " | WARNING: " + "; ".join(bound_warnings)

    result = solver.check()
    smt2_text = solver.to_smt2() if export_smt2 else None

    domain_constraints = [range_constraints(params_consts, merged_bounds)] if merged_bounds else []
    if input_constraints:
        domain_constraints.append(input_constraints(params_consts))
    index_warnings = (
        _check_table_index_bounds(ev_legacy, legacy_table_types, "Legacy", params_consts, domain_constraints)
        + _check_table_index_bounds(ev_modern, modern_table_types, "Modern", params_consts, domain_constraints)
    )

    if result == z3.unsat:
        return VerificationResult(
            label=Label.PROVEN,
            detail=f"Z3 proved: no input exists ({domain_note}) for which the outputs differ.",
            proof_note="UNSAT of the negation == equivalence for all inputs in the modeled domain",
            index_warnings=index_warnings or None,
            smt2=smt2_text,
        )
    else:
        model = solver.model()
        cx = {str(d): model[d] for d in model.decls() if str(d) in effective_keys}
        return VerificationResult(
            label=Label.FLAGGED,
            detail=f"Z3 found a concrete counterexample ({domain_note}) where Legacy != Migrated.",
            counterexample=cx,
            index_warnings=index_warnings or None,
            smt2=smt2_text,
        )


def _wrap_concrete_counterexample(cx, arg_type):
    """Wraps raw Python values (int/str) as Z3 constants (IntVal/RealVal/
    StringVal), so that EVERY consumer of VerificationResult.counterexample
    (e.g. sandbox.py, which expects .as_long()/.as_string() everywhere)
    sees a UNIFORM format -- regardless of whether the counterexample
    came from the symbolic proof, from random fuzzing, or from the
    concolic search. Without this, sandbox.py crashes with an
    AttributeError as soon as a FLAGGED result comes from the fallback
    tier instead of from prove_equivalence() (a real bug, found when
    wiring up the concolic engine)."""
    wrapped = {}
    for k, v in cx.items():
        if isinstance(v, bool):
            wrapped[k] = v
        elif isinstance(v, str):
            wrapped[k] = z3.StringVal(v)
        elif isinstance(v, int):
            wrapped[k] = z3.RealVal(v) if arg_type == z3.RealSort() else z3.IntVal(v)
        else:
            wrapped[k] = v  # already a Z3 object or an unknown type -> pass through unchanged
    return wrapped


def differential_fuzz(legacy_fn, modern_fn, n_samples=200_000, sampler=None, arg_type=z3.IntSort()):
    """Tier 2/3: when a symbolic proof is not possible -> massive testing."""
    if sampler is None:
        sampler = lambda: (random.randint(-10_000, 10_000),)

    checked = 0
    for _ in range(n_samples):
        args = sampler()
        try:
            lv = legacy_fn(*args)
            mv = modern_fn(*args)
        except Exception as e:
            continue
        checked += 1
        if lv != mv:
            return VerificationResult(
                label=Label.FLAGGED,
                detail=f"Differential fuzzing found a difference after {checked} test cases.",
                counterexample=_wrap_concrete_counterexample(
                    dict(zip(get_params(legacy_fn), args)), arg_type),
                coverage=checked,
            )
    return VerificationResult(
        label=Label.VERIFIED_BY_TESTING,
        detail=f"No difference found across {checked} generated test cases. "
               f"No mathematical proof -- residual risk remains.",
        coverage=checked,
    )


def verify(legacy_fn, modern_fn, arg_type=z3.RealSort(), fuzz_samples=200_000,
           sampler=None, input_bounds=None, input_constraints=None,
           fallback="concolic", concolic_iterations=300, export_smt2=False):
    """Triage layer: first tries PROVEN, and for unprovable constructs
    automatically falls back to a fallback tier -- exactly the behavior
    from the VeriCode v2 concept.

    fallback: "concolic" (default) -- branch negation via concolic.py,
        specifically finds rare bugs that plain random fuzzing typically
        misses (empirically confirmed: a bug present at EXACTLY one of
        50,000 possible values was missed by 5000 random samples, but
        found by concolic search in 4 iterations). Needs arg_type=IntSort()
        -- with RealSort() it automatically falls back to "random" (with
        a note in the detail text, never a silent fallback).
        "random" -- the older, simple random fuzzer (differential_fuzz).
        "both" -- concolic search first (fast, targeted), and on failure
        additionally random fuzzing (broader but untargeted) for extra
        coverage.
    concolic_iterations: iteration budget for the concolic fallback
        (separate from fuzz_samples, since concolic iterations are more
        expensive per step).
    export_smt2: see prove_equivalence() -- only supported on the
        symbolic proof path (PROVEN/FLAGGED via Z3), NOT for
        fuzzing/concolic results (which have no SMT proof obligation,
        only a concrete counterexample or a coverage statement).

    If no explicit sampler is passed, the fuzzing sampler is built from
    the same bounds (possibly auto-derived from PIC fields) as the
    symbolic proof -- so that all tiers are guaranteed to test the same
    value range and do not accidentally diverge."""
    params = get_params(legacy_fn)
    merged_bounds, _ = resolve_input_bounds(params, legacy_fn, modern_fn, input_bounds)
    if sampler is None:
        sampler = lambda: tuple(
            random.randint(*merged_bounds[p]) if p in merged_bounds else random.randint(-10_000, 10_000)
            for p in params
        )
    try:
        return prove_equivalence(legacy_fn, modern_fn, arg_type,
                                  input_bounds=input_bounds, input_constraints=input_constraints,
                                  export_smt2=export_smt2)
    except UnsupportedConstruct as e:
        if getattr(legacy_fn, "record_types", None) or getattr(modern_fn, "record_types", None):
            raise NotImplementedError(
                f"Record types (.record_types) are not yet supported by the "
                f"concolic/fuzzing fallback -- only by the symbolic proof path. "
                f"Original reason for the fallback: {e}"
            ) from e

        effective_fallback = fallback
        fallback_note = ""
        if fallback in ("concolic", "both") and arg_type != z3.IntSort():
            effective_fallback = "random" if fallback == "concolic" else "both-degraded-to-random"
            fallback_note = " [Concolic search skipped: arg_type != IntSort(), automatically fell back to random fuzzing]"

        if effective_fallback in ("concolic", "both", "both-degraded-to-random") and effective_fallback != "random":
            concolic_bounds = {p: merged_bounds.get(p, (-10_000, 10_000)) for p in params}
            c_res = concolic_search(legacy_fn, modern_fn, max_iterations=concolic_iterations, bound=concolic_bounds)
            if c_res.found_diff:
                return VerificationResult(
                    label=Label.FLAGGED,
                    detail=f"[Fallback: {e}] Concolic Search: {c_res.note}{fallback_note}",
                    counterexample=_wrap_concrete_counterexample(c_res.counterexample, arg_type),
                    coverage=c_res.paths_explored,
                )
            if fallback != "both":
                return VerificationResult(
                    label=Label.VERIFIED_BY_TESTING,
                    detail=f"[Fallback: {e}] Concolic Search: {c_res.note}{fallback_note}",
                    coverage=c_res.paths_explored,
                )
            # fallback == "both" and concolic search found nothing -> additionally run random fuzzing

        fuzz_result = differential_fuzz(legacy_fn, modern_fn, fuzz_samples, sampler, arg_type=arg_type)
        fuzz_result.detail = f"[Fallback: {e}]{fallback_note} {fuzz_result.detail}"
        return fuzz_result
