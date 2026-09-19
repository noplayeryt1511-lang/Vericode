# -*- coding: utf-8 -*-
"""
Path 1, "COBOL parser" component: automatic extraction of PIC field metadata
from real COBOL source code, via the PyPI package `cobol-py` (a pure-Python
port of the proleap-cobol-parser pipeline, ANTLR4-based -- no Java/Maven needed).

WHY THIS MATTERS: previously, the PicField/PicX/TableField objects for legacy_fn
were written by hand from the COBOL text -- that was the "manual parser
substitute" from the original gap analysis. This module automates exactly that
step: PIC strings like "S9(7)V99" or "X(10)" are translated directly from the
parsed AST/ASG into our own PicField/PicX objects.

LIMITATION (stated plainly): this only covers the DATA DIVISION (fields +
their types + OCCURS), NOT the PROCEDURE DIVISION (the actual logic/
calculations). Translating the calculation logic remains the responsibility
of the LLM in the patch loop -- this module only improves the quality of the
input information (exact field widths instead of "the LLM reads the COBOL
columns itself"); it does not replace the patch loop.
"""

import re

from cobol_py import CobolParserRunner, CobolParserParams, CobolSourceFormatEnum
from cobol_transpile import UnsupportedCobolConstruct


def _analyze_cobol(cobol_source, params):
    """Wrapped call to CobolParserRunner().analyze() -- catches internal
    crashes of the cobol-py library itself (not our own code) and turns
    them into a clean, expected rejection instead of letting a raw
    AttributeError/TypeError etc. leak through. Known limitation: a
    FILE-SECTION 'VALUE OF' clause crashes cobol-py's own internal
    analysis (AttributeError in cobol_py.asg.data) before our code ever
    gets involved -- a library boundary, not a missing feature on our
    part, but a clean error instead of a crash is still our
    responsibility."""
    try:
        return CobolParserRunner().analyze(cobol_source, params)
    except (AttributeError, TypeError, KeyError, IndexError) as e:
        raise UnsupportedCobolConstruct(
            f"COBOL program could not be analyzed by the underlying cobol-py "
            f"library (internal error: {type(e).__name__}: {e}) -- commonly seen with "
            f"rare ENVIRONMENT/FILE-SECTION clauses (e.g. VALUE OF, COLLATING SEQUENCE), "
            f"which would not be supported anyway outside our file I/O exclusion scope"
        ) from e

from engine import PicField, PicX, TableField


def _build_parser_params(source_format, copy_book_dirs=None):
    """Builds the CobolParserParams for an analyze() call, including
    COPY-book resolution when directories are supplied. Extensions WITHOUT
    a leading dot (cobol-py convention: 'CPY', not '.CPY').
    ignore_missing_copy=True when directories are supplied -- a COPY book
    that is NOT found then results in a commented-out line instead of a
    hard failure of the ENTIRE file (see the cobol-py source: the
    "COPY-NOT-FOUND" comment) -- consistent with our principle of not
    letting a single unresolvable part crash the whole extraction.
    WITHOUT copy_book_dirs, behavior is unchanged (hard error on COPY,
    as before -- no silent dropping of code)."""
    if copy_book_dirs:
        from pathlib import Path
        return CobolParserParams(
            format=source_format,
            copy_book_directories=[Path(d) for d in copy_book_dirs],
            copy_book_extensions=["CPY", "cpy", "CBL", "cbl"],
            ignore_missing_copy=True,
        )
    return CobolParserParams(format=source_format)


def parse_pic_string(pic_str, signed=False):
    """Parses a COBOL PIC string (e.g. '9(5)V99', 'S9(7)V99', 'XX', 'X(10)')
    into a PicField (numeric) or PicX (alphanumeric) object.

    Supported: 9(n) repetition, individual 9s, V (decimal point), X(n) for
    alphanumeric fields, S prefix for signed (can also be passed separately,
    since some ASG variants report the sign separately from the
    picture_string). NOT supported: edited-PIC characters (Z, $, comma,
    etc.) -- these are purely display formatting for DISPLAY output and are
    not relevant to the core calculation, so they are deliberately not
    implemented."""
    s = pic_str.strip()
    if s.startswith("S"):
        signed = True
        s = s[1:]

    tokens = re.findall(r"([9XV])(\(\d+\))?", s)
    if not tokens:
        raise ValueError(f"PIC string not recognized (possibly an edited PIC?): {pic_str!r}")

    if any(t[0] == "X" for t in tokens):
        length = sum(int(rep[1:-1]) if rep else 1 for char, rep in tokens if char == "X")
        return PicX(length=length)

    integer_digits = 0
    decimal_digits = 0
    seen_v = False
    for char, rep in tokens:
        count = int(rep[1:-1]) if rep else 1
        if char == "V":
            seen_v = True
        elif char == "9":
            if seen_v:
                decimal_digits += count
            else:
                integer_digits += count
    return PicField(total_digits=integer_digits + decimal_digits,
                     decimal_digits=decimal_digits, signed=signed)


def _extract_occurs_count(occurs_clause):
    text = occurs_clause.ctx.getText()
    m = re.search(r"OCCURS(\d+)", text)
    if not m:
        raise ValueError(f"OCCURS count not recognized in: {text!r}")
    return int(m.group(1))


def _gather_data_description_entries(pu):
    """Collects data items from the WORKING-STORAGE AND LINKAGE SECTIONs
    combined -- subprograms (PROCEDURE DIVISION USING ...) often have ONLY
    a LINKAGE SECTION and NO WORKING-STORAGE SECTION at all (in that case
    working_storage_section is simply None, not an error case). Both
    sections are treated the same way, since our own parameter model does
    not distinguish where a field came from."""
    dd = pu.data_division
    entries = []
    if dd.working_storage_section is not None:
        entries.extend(dd.working_storage_section.data_description_entries)
    if dd.linkage_section is not None:
        entries.extend(dd.linkage_section.data_description_entries)
    return entries


def extract_data_items(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Analyzes a COBOL program and returns a flat list of all data items
    from the WORKING-STORAGE SECTION, each as a dict:
    {name, cobol_name, level, field (PicField|PicX|None), table (TableField|None)}

    name: COBOL name normalized with hyphens converted to underscores and
    lowercased (e.g. WS-WEIGHT-KG -> ws_weight_kg) -- a REASONABLE
    suggestion for a Python identifier, but NO GUARANTEE that the LLM
    picks exactly this name (see the module docstring).
    Also covers LINKAGE SECTION fields (subprogram parameters).
    copy_book_dirs: optional list of directories in which COPY books are
    looked up (see _build_parser_params)."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit
    entries_src = _gather_data_description_entries(pu)

    items = []
    for entry in entries_src:
        if entry.name is None:
            # FILLER field (unnamed padding/layout entry) -- by COBOL
            # convention never referenceable by name, so it is
            # deliberately skipped here instead of inventing a placeholder
            # name.
            continue
        pic = entry.picture_clause if hasattr(entry, "picture_clause") else None
        try:
            field = parse_pic_string(pic.picture_string) if pic else None
        except ValueError:
            # PIC pattern outside our supported subset (e.g. an edited PIC
            # like "A(3)", "Z,ZZ9") -- skip this ONE field instead of
            # letting the extraction of the ENTIRE file fail because of it
            # (the remaining fields stay usable).
            field = None
        table = None
        occurs_clauses = getattr(entry, "occurs_clauses", None)
        if occurs_clauses and field is not None:
            occurs = _extract_occurs_count(occurs_clauses[0])
            table = TableField(element=field, occurs=occurs)
        py_name = entry.name.lower().replace("-", "_")
        items.append({
            "name": py_name, "cobol_name": entry.name,
            "level": entry.level_number, "field": field, "table": table,
        })
    return items


def extract_record_and_table_types(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Detects group fields (records, nested to ANY depth) and OCCURS
    tables automatically and builds the record_types/table_types/field_types
    dicts expected by run_patch_loop()/convert_and_verify(). Uses the
    parent-child relationship already resolved by cobol-py
    (parent_data_description_entry_group) instead of interpreting level
    numbers itself.

    LIMITATION (stated plainly, no silent mishandling): multi-level
    nested groups are now fully resolved (engine.py has supported this
    since this version) -- ONLY tables of GROUP elements (array-of-struct,
    e.g. "05 LINE-ITEM OCCURS 50 TIMES. 10 QUANTITY...
    10 PRICE...") remain unresolved, because Z3 arrays can only use
    scalars/strings as the element sort, not records -- that is the
    still-open, fundamentally different extension step (would need Z3
    datatype sorts).
    copy_book_dirs: see extract_data_items()."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit
    entries_src = _gather_data_description_entries(pu)

    children_by_parent = {}
    top_level = []
    for entry in entries_src:
        if entry.name is None or not hasattr(entry, "picture_clause"):
            # FILLER (no name) OR an 88-level condition name (has no
            # picture_clause attribute at all, structurally a different
            # ASG type) -- neither can be extracted as a standalone field,
            # so skip it instead of crashing.
            continue
        parent = entry.parent_data_description_entry_group
        if parent is None:
            top_level.append(entry)
        else:
            children_by_parent.setdefault(parent.name, []).append(entry)

    field_types, record_types, table_types = {}, {}, {}
    unresolved = []

    def py(name):
        return name.lower().replace("-", "_")

    def build_group_spec(entry, path):
        """Recursively builds a (possibly nested) record_types spec for a
        group. Returns (spec_dict, ok) -- ok=False if an OCCURS group
        (array-of-struct, not yet supported) appears anywhere in the
        nesting."""
        spec = {}
        ok = True
        for child in children_by_parent.get(entry.name, []):
            child_path = f"{path}.{py(child.name)}"
            if child.occurs_clauses:
                unresolved.append((child.name, f"OCCURS inside a group ({child_path}) "
                                    f"-- table of records/fields in a nested group, "
                                    f"not yet supported by engine.py"))
                ok = False
                continue
            if child.picture_clause is not None:
                try:
                    spec[py(child.name)] = parse_pic_string(child.picture_clause.picture_string)
                except ValueError as e:
                    unresolved.append((child.name, f"PIC pattern not supported ({child_path}): {e}"))
                    ok = False
            else:
                grandchildren = children_by_parent.get(child.name, [])
                if not grandchildren:
                    continue  # empty intermediate group -> ignore
                sub_spec, sub_ok = build_group_spec(child, child_path)
                if sub_ok:
                    spec[py(child.name)] = sub_spec
                ok = ok and sub_ok
        return spec, ok

    for entry in top_level:
        name = py(entry.name)
        children = children_by_parent.get(entry.name, [])

        if entry.picture_clause:
            try:
                field = parse_pic_string(entry.picture_clause.picture_string)
            except ValueError as e:
                unresolved.append((entry.name, f"PIC pattern not supported: {e}"))
                continue
            if entry.occurs_clauses:
                table_types[name] = TableField(element=field, occurs=_extract_occurs_count(entry.occurs_clauses[0]))
            else:
                field_types[name] = field
            continue

        if not children:
            continue  # group without PIC and without children -> nothing to extract

        # Common COBOL pattern: a pure wrapper group with no OCCURS of its
        # own, with EXACTLY ONE child that itself carries OCCURS (e.g.
        # "01 LINE-ITEMS. 05 LINE-ITEM OCCURS 10 TIMES. 10 QUANTITY...
        # 10 PRICE..."). The outer group is "resolved away" here -- the
        # Python parameter name stays that of the outer group (line_items),
        # but it becomes directly the table whose elements consist of the
        # children of the inner OCCURS entry. Only FLAT elements are
        # supported (see below).
        if not entry.occurs_clauses and len(children) == 1 and children[0].occurs_clauses:
            occurs_child = children[0]
            grandchildren = children_by_parent.get(occurs_child.name, [])
            flat_spec = {}
            flat_ok = bool(grandchildren)
            for gc in grandchildren:
                if gc.picture_clause is None or gc.occurs_clauses:
                    unresolved.append((occurs_child.name, f"Table element '{gc.name}' is itself a "
                                        f"group or has OCCURS -- only FLAT records are supported as table elements"))
                    flat_ok = False
                    continue
                try:
                    flat_spec[py(gc.name)] = parse_pic_string(gc.picture_clause.picture_string)
                except ValueError as e:
                    unresolved.append((gc.name, f"PIC pattern not supported: {e}"))
                    flat_ok = False
            if flat_ok:
                table_types[name] = TableField(element=flat_spec, occurs=_extract_occurs_count(occurs_child.occurs_clauses[0]))
            continue

        if entry.occurs_clauses:
            # Rarer case: the outer group ITSELF carries the OCCURS
            # (instead of an inner wrapper child as above).
            flat_spec = {}
            flat_ok = True
            for child in children:
                if child.picture_clause is None or child.occurs_clauses:
                    unresolved.append((entry.name, f"Table element '{child.name}' is itself a group "
                                        f"or has OCCURS -- only FLAT records are supported as table elements"))
                    flat_ok = False
                    continue
                try:
                    flat_spec[py(child.name)] = parse_pic_string(child.picture_clause.picture_string)
                except ValueError as e:
                    unresolved.append((child.name, f"PIC pattern not supported: {e}"))
                    flat_ok = False
            if flat_ok and flat_spec:
                table_types[name] = TableField(element=flat_spec, occurs=_extract_occurs_count(entry.occurs_clauses[0]))
            continue

        if entry.occurs_clauses:
            unresolved.append((entry.name, "OCCURS group (table of records) -- not yet supported by engine.py"))
            continue

        spec, ok = build_group_spec(entry, name)
        if ok and spec:
            record_types[name] = spec

    return {"field_types": field_types, "record_types": record_types,
            "table_types": table_types, "unresolved": unresolved}


def extract_condition_names(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Collects ALL 88-level condition names in the program into a dict
    {COBOL_NAME_UPPERCASE -> "(PARENT_FIELD = VALUE)"} as a ready-made
    COBOL comparison-clause string. Needed for 'IF <condition-name>' and
    'EVALUATE TRUE / WHEN <condition-name>' -- the expression parser does
    not know about condition names, but it can process the generated
    comparison syntax unchanged (see
    cobol_transpile.py:_substitute_condition_names). Only a single VALUE
    is supported, no THRU range/multiple value (in that case the name is
    simply NOT added to the map -- usage then leads to a clear error
    later instead of a silent misresolution)."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit
    entries = _gather_data_description_entries(pu)

    mapping = {}
    for entry in entries:
        if type(entry).__name__ != "DataDescriptionEntryCondition":
            continue
        parent = getattr(entry, "parent_data_description_entry_group", None)
        value_clause = getattr(entry, "value_clause", None)
        if parent is None or value_clause is None:
            continue
        value_text = value_clause.ctx.start.getInputStream().getText(
            value_clause.ctx.start.start, value_clause.ctx.stop.stop
        )
        m = re.match(r"^VALUE\s+(.+)$", value_text.strip(), re.IGNORECASE | re.DOTALL)
        if not m:
            continue
        value_expr_text = m.group(1).strip()
        if re.search(r"\bTHRU\b", value_expr_text, re.IGNORECASE) or "," in value_expr_text:
            continue  # THRU range/multiple value -- deliberately NOT included
        mapping[entry.name.upper()] = f"({parent.name} = {value_expr_text})"
    return mapping


def extract_redefines_map(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Collects REDEFINES relationships into a dict {python_field_name ->
    Python expression} that derives the field READ-ONLY from the base field.

    DELIBERATELY NARROWLY SCOPED -- only exactly ONE pattern is supported
    (by far the most common real-world one: a numeric field decomposed
    into subfields, e.g. date YYYYMMDD -> YY/MM/DD):
      - Base field: a single PicField with decimal_digits=0 (a pure
        integer digit sequence, no V in the PIC clause)
      - Redefining field: a GROUP made up entirely of PicField subfields,
        EACH with decimal_digits=0, whose widths sum to EXACTLY the total
        width of the base field (no overflow, no gap)

    READ-ONLY: write access to a redefining field is NOT supported (would
    need read-modify-write on individual digit positions of the base
    field, considerably more complex) -- cobol_transpile.py explicitly
    rejects this when the caller tries to write there.

    Anything outside this one pattern (PicX redefinition, redefinition by
    a single scalar field instead of a group, partial coverage) is NOT
    added to the map -- usage then leads to a clear error instead of a
    silent misresolution."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit
    entries = _gather_data_description_entries(pu)
    by_cobol_name = {e.name: e for e in entries if getattr(e, "name", None)}

    mapping = {}
    for entry in entries:
        redefines_clause = getattr(entry, "redefines_clause", None)
        if redefines_clause is None:
            continue
        base_name = redefines_clause.redefines_call.name
        base_entry = by_cobol_name.get(base_name)
        if base_entry is None:
            continue
        base_pic = getattr(base_entry, "picture_clause", None)
        if base_pic is None:
            continue  # base is itself a group -- not supported
        try:
            base_field = parse_pic_string(base_pic.picture_string)
        except ValueError:
            continue
        if not isinstance(base_field, PicField) or base_field.decimal_digits != 0:
            continue  # only pure integer base fields are supported
        base_total_digits = base_field.total_digits
        base_py = base_name.lower().replace("-", "_")

        # Find the subfields of the redefining group (direct children,
        # in declaration order -- IMPORTANT for the position calculation)
        children = [e for e in entries
                    if getattr(e, "parent_data_description_entry_group", None) is entry]
        if not children:
            continue  # does not redefine as a group -- not supported (see docstring)

        sub_specs = []
        ok = True
        for child in children:
            child_pic = getattr(child, "picture_clause", None)
            if child_pic is None:
                ok = False
                break
            try:
                child_field = parse_pic_string(child_pic.picture_string)
            except ValueError:
                ok = False
                break
            if not isinstance(child_field, PicField) or child_field.decimal_digits != 0:
                ok = False
                break
            sub_specs.append((child.name, child_field.total_digits))
        if not ok:
            continue
        if sum(w for _, w in sub_specs) != base_total_digits:
            continue  # widths do not match exactly -- not supported

        offset = 0
        for child_name, width in sub_specs:
            right_shift = base_total_digits - (offset + width)
            child_py = child_name.lower().replace("-", "_")
            mapping[child_py] = f"(({base_py} // {10 ** right_shift}) % {10 ** width})"
            offset += width
    return mapping
