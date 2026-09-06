#!/usr/bin/env bash

# Canonical encoder for pfci-segment-evidence-v1. A literal "null" argument is
# the only null representation. Values cross the process boundary over stdin so
# evidence size is not constrained by the operating system's per-argument limit.
segment_evidence_emit() {
  if [[ "$#" -ne 15 ]]; then
    printf '%s\n' 'segment_evidence_emit requires exactly 15 fields' >&2
    return 2
  fi

  printf '%s\0' "$@" | python3 -c '
import json
import sys

payload = sys.stdin.buffer.read().split(b"\0")
if not payload or payload[-1] != b"":
    raise ValueError("segment evidence stdin is not NUL terminated")
values = [value.decode("utf-8", errors="strict") for value in payload[:-1]]
if len(values) != 15:
    raise ValueError("segment evidence requires exactly 15 fields")
(
    schema_version,
    segment,
    event,
    merge_commit,
    tree,
    base,
    source_head,
    raw_rc,
    outcome,
    report_input_address,
    report_sha256,
    judge_source_address,
    scribe_source_address,
    selected_test_ids,
    ordered_check_ids,
) = values


def nullable(value):
    return None if value == "null" else value


def string_array(value):
    if value == "null":
        return None
    decoded = json.loads(value)
    if not isinstance(decoded, list) or any(not isinstance(item, str) for item in decoded):
        raise ValueError("segment evidence arrays must contain only strings")
    return decoded


evidence = {
    "schema_version": schema_version,
    "segment": segment,
    "event": nullable(event),
    "merge_commit": nullable(merge_commit),
    "tree": nullable(tree),
    "base": nullable(base),
    "source_head": nullable(source_head),
    "raw_rc": int(raw_rc),
    "outcome": outcome,
    "report_input_address": nullable(report_input_address),
    "report_sha256": nullable(report_sha256),
    "judge_source_address": nullable(judge_source_address),
    "scribe_source_address": nullable(scribe_source_address),
    "selected_test_ids": string_array(selected_test_ids),
    "ordered_check_ids": string_array(ordered_check_ids),
}
sys.stdout.write(json.dumps(evidence, ensure_ascii=True, separators=(",", ":")) + "\n")
'
}

segment_evidence_array_append() {
  if [[ "$#" -ne 2 ]]; then
    printf '%s\n' 'segment_evidence_array_append requires an array and a value' >&2
    return 2
  fi

  printf '%s\0' "$@" | python3 -c '
import json
import sys

payload = sys.stdin.buffer.read().split(b"\0")
if len(payload) != 3 or payload[-1] != b"":
    raise ValueError("array append stdin must contain exactly two fields")
encoded, value = (item.decode("utf-8", errors="strict") for item in payload[:-1])
values = json.loads(encoded)
if not isinstance(values, list) or any(not isinstance(item, str) for item in values):
    raise ValueError("segment evidence arrays must contain only strings")
values.append(value)
sys.stdout.write(json.dumps(values, ensure_ascii=True, separators=(",", ":")))
'
}
