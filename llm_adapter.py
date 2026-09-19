# -*- coding: utf-8 -*-
"""
Real LLM adapter for run_patch_loop(): replaces the simulated mock_llm_fix
from test_patch_loop.py with a real call to api.anthropic.com.

Usage:
    from llm_adapter import anthropic_fix_fn
    result = run_patch_loop(..., llm_fix_fn=anthropic_fix_fn)

The API key is read EXCLUSIVELY from the ANTHROPIC_API_KEY environment
variable - never as a literal in the code or as a function parameter, so
that it can never end up anywhere (chat, logs, version control).

NOTE: no ANTHROPIC_API_KEY is set in the current sandbox environment ->
this module is written and structurally testable (see test_llm_adapter.py,
which mocks the network layer), but has NOT been tested live against the
real API. The first real run must happen in an environment with the key set.
"""

import json
import os
import re
import urllib.error
import urllib.request


ANTHROPIC_API_URL = "https://api.anthropic.com/v1/messages"
ANTHROPIC_VERSION = "2023-06-01"
DEFAULT_MODEL = "claude-haiku-4-5-20251001"  # cheapest current model - more
# than sufficient for pure code-fix tasks (given one counterexample, fix one
# function); no reason to pay for a more expensive model here.


class LLMCallError(Exception):
    """Dedicated exception class so run_patch_loop() can clearly distinguish
    API errors from other error types (sandbox errors, solver errors)."""
    pass


def call_anthropic(prompt, model=DEFAULT_MODEL, max_tokens=1024, api_key=None, timeout=30):
    """Raw API call, returns the text content of the response (string).
    Raises LLMCallError on every failure (missing key, network error,
    non-200 status, unexpected response format) - deliberately NO silent
    fallback, since a verification tool must not keep running on the basis
    of a request that failed unnoticed."""
    api_key = api_key or os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        raise LLMCallError(
            "No API key found. Set the ANTHROPIC_API_KEY environment variable."
        )

    body = json.dumps({
        "model": model,
        "max_tokens": max_tokens,
        "messages": [{"role": "user", "content": prompt}],
    }).encode("utf-8")

    request = urllib.request.Request(
        ANTHROPIC_API_URL,
        data=body,
        method="POST",
        headers={
            "x-api-key": api_key,
            "anthropic-version": ANTHROPIC_VERSION,
            "content-type": "application/json",
        },
    )

    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        error_body = e.read().decode("utf-8", errors="replace")
        raise LLMCallError(f"HTTP {e.code} from the Anthropic API: {error_body}") from e
    except urllib.error.URLError as e:
        raise LLMCallError(f"Network error calling the Anthropic API: {e.reason}") from e
    except TimeoutError as e:
        raise LLMCallError(f"Timeout after {timeout}s calling the Anthropic API") from e

    try:
        text_blocks = [block["text"] for block in payload["content"] if block.get("type") == "text"]
    except (KeyError, TypeError) as e:
        raise LLMCallError(f"Unexpected response format: {payload}") from e

    if not text_blocks:
        raise LLMCallError(f"No text response contained in the response: {payload}")

    return "\n".join(text_blocks)


def extract_code(response_text):
    """Extracts Python code from an LLM response. Despite an explicit prompt
    instruction ("return ONLY the code"), LLMs experience shows they still
    often wrap code in Markdown fences - this is robust against that: it
    pulls the content of a ```python ... ``` or ``` ... ``` block if
    present, otherwise the raw response is returned unchanged (covers the
    case where the model actually follows the instruction)."""
    fenced = re.search(r"```(?:python)?\s*\n(.*?)```", response_text, re.DOTALL)
    if fenced:
        return fenced.group(1).strip() + "\n"
    return response_text.strip() + "\n"


def anthropic_fix_fn(prompt, attempt, model=DEFAULT_MODEL):
    """The actual llm_fix_fn implementation for run_patch_loop()."""
    raw = call_anthropic(prompt, model=model)
    return extract_code(raw)
