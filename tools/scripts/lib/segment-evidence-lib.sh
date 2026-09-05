#!/usr/bin/env bash

# Canonical encoder for pfci-segment-evidence-v1. A literal "null" argument is
# the only null representation; JSON arrays arrive as JSON and are re-encoded.
segment_evidence_emit() {
  if [[ "$#" -ne 15 ]]; then
    printf '%s\n' 'segment_evidence_emit requires exactly 15 fields' >&2
    return 2
  fi

  python3 - "$@" <<'PY'
import json
import sys

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
) = sys.argv[1:]


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
    "event": event,
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
PY
}
