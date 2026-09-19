# -*- coding: utf-8 -*-
"""
Sandbox for executing LLM-generated code in run_patch_loop().

IMPORTANT CLARIFICATION (no sugarcoating): this is NOT a complete security
sandbox against a deliberately malicious payload. Python cannot be
watertight-confined within Python itself (dynamic attributes, __import__,
C extensions, etc.). What this sandbox ACTUALLY provides:

  - A subprocess (os.fork), so that a crash/hang does not take down the
    parent process (and with it the whole patch loop / rest of the
    application).
  - A hard timeout (infinite loops in LLM code get killed instead of
    running forever).
  - CPU and memory limits via resource.setrlimit (memory bombs and
    runaway computation get aborted instead of burdening the host).

This covers the REALISTIC threat model for this use case (an LLM
occasionally produces broken/infinite code, not: an attacker deliberately
trying to break out of the sandbox). For genuine third-party code of
unknown origin you would additionally need OS-level isolation (gVisor,
Firecracker, a container with no network/file access) - that is
deliberately NOT provided here.
"""

import linecache
import multiprocessing as mp
import resource

import z3

from engine import verify, PicX

SANDBOX_CPU_SECONDS = 5
SANDBOX_MEMORY_BYTES = 512 * 1024 * 1024  # 512 MB
SANDBOX_TIMEOUT_SECONDS = 8  # wall-clock timeout, > CPU limit as a safety net

# KNOWN LIMITATION (empirically confirmed, not just theoretical): in
# containerized environments with an additional cgroup memory limit, the
# Linux OOM killer often fires with SIGKILL BEFORE RLIMIT_AS itself can
# trigger a regular MemoryError that Python could catch. SIGKILL cannot be
# caught at all. This is not a safety issue (the main process stays
# protected, and the failure is still correctly detected via exitcode<0 -
# see sandboxed_verify), but the resulting error message is then the
# generic "child_crashed_no_result" instead of the more informative
# "memory_limit_exceeded".


def _apply_resource_limits():
    """Best-effort - some limits are unavailable on certain platforms
    (e.g. RLIMIT_AS on some macOS versions); errors are deliberately
    swallowed rather than crashing the sandbox itself."""
    for limit, value in (
        (resource.RLIMIT_CPU, (SANDBOX_CPU_SECONDS, SANDBOX_CPU_SECONDS)),
        (resource.RLIMIT_AS, (SANDBOX_MEMORY_BYTES, SANDBOX_MEMORY_BYTES)),
        (resource.RLIMIT_NOFILE, (32, 32)),
    ):
        try:
            resource.setrlimit(limit, value)
        except (ValueError, OSError):
            pass


def _child_worker(result_queue, legacy_fn, modern_source, function_name,
                   field_types, arg_type, legacy_params, verify_kwargs,
                   record_types=None, table_types=None):
    _apply_resource_limits()
    try:
        namespace = {}
        filename = "<sandboxed modern>"
        linecache.cache[filename] = (
            len(modern_source), None, modern_source.splitlines(keepends=True), filename
        )
        exec(compile(modern_source, filename, "exec"), namespace)
        if function_name not in namespace:
            result_queue.put({"error": f"Function '{function_name}' not found in generated code"})
            return
        modern_fn = namespace[function_name]
        if field_types:
            modern_fn.field_types = dict(field_types)
        if record_types:
            modern_fn.record_types = dict(record_types)
        if table_types:
            modern_fn.table_types = dict(table_types)

        res = verify(legacy_fn, modern_fn, arg_type=arg_type, **verify_kwargs)

        cx_plain = {}
        legacy_out = modern_out = None
        if res.counterexample:
            cx_plain = {k: (v.as_long() if hasattr(v, "as_long") else v.as_string())
                        for k, v in res.counterexample.items()}
            legacy_return_field = getattr(legacy_fn, "field_types", {}).get("return")
            modern_return_field = getattr(modern_fn, "field_types", {}).get("return")
            # For record/table parameters, cx_plain is not enough as a flat
            # argument list (keys like "account.balance" instead of
            # "account") -> only compute legacy_out/modern_out for purely
            # scalar cases.
            if all(p in cx_plain for p in legacy_params):
                args = [cx_plain[p] for p in legacy_params]
                legacy_out_raw = legacy_fn(*args)      # still runs IN THE SAME subprocess -> safe
                modern_out_raw = modern_fn(*args)      # same here
                legacy_out = _concrete_apply_field_child(legacy_return_field, legacy_out_raw)
                modern_out = _concrete_apply_field_child(modern_return_field, modern_out_raw)

        result_queue.put({
            "label": res.label.value,
            "detail": res.detail,
            "counterexample": cx_plain,
            "legacy_out": legacy_out,
            "modern_out": modern_out,
        })
    except MemoryError:
        result_queue.put({"error": "memory_limit_exceeded"})
    except Exception as e:
        result_queue.put({"error": f"{type(e).__name__}: {e}"})


def _concrete_apply_field_child(pic, raw_value):
    if pic is None:
        return raw_value
    if isinstance(pic, PicX):
        return z3.simplify(pic.normalize(z3.StringVal(raw_value))).as_string()
    return z3.simplify(pic.truncate(z3.IntVal(raw_value))).as_long()


def sandboxed_verify(legacy_fn, modern_source, function_name, field_types,
                      arg_type, legacy_params, verify_kwargs=None,
                      timeout_seconds=SANDBOX_TIMEOUT_SECONDS,
                      record_types=None, table_types=None):
    """Runs compilation, execution AND verification of LLM-generated code in
    an isolated subprocess (fork - no pickling needed, legacy_fn/arg_type/
    etc. are inherited via copy-on-write).

    record_types/table_types: if given, applied 1:1 to modern_fn (same as
    field_types). This assumes the LLM addresses records/tables under
    exactly the expected attribute/parameter names - that must be
    explicitly specified in the translation prompt.

    Return value: a dict with either the verify() result fields (label,
    detail, counterexample, legacy_out, modern_out) OR an "error" key
    (timeout | memory_limit_exceeded | exception text | crash)."""
    ctx = mp.get_context("fork")
    result_queue = ctx.Queue()
    process = ctx.Process(
        target=_child_worker,
        args=(result_queue, legacy_fn, modern_source, function_name,
              field_types, arg_type, legacy_params, verify_kwargs or {},
              record_types, table_types),
    )
    process.start()
    process.join(timeout_seconds)

    if process.is_alive():
        process.terminate()
        process.join(1)
        if process.is_alive():
            process.kill()
            process.join()
        return {"error": "timeout", "timeout_seconds": timeout_seconds}

    if not result_queue.empty():
        return result_queue.get()

    return {"error": f"child_crashed_no_result (exitcode={process.exitcode})"}
