#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C
CACHED=""
FRESH=""
OUTPUT=""
MODULES_FILE=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --cached) CACHED="$2"; shift 2 ;;
    --fresh) FRESH="$2"; shift 2 ;;
    --output) OUTPUT="$2"; shift 2 ;;
    --cached-modules-file) MODULES_FILE="$2"; shift 2 ;;
    *) echo "lean-report-merge: unknown argument '$1'" >&2; exit 2 ;;
  esac
done
[[ -f "$CACHED" && -f "$FRESH" && -n "$OUTPUT" ]] \
  || { echo "usage: lean-report-merge.sh --cached FILE --fresh FILE --output FILE" >&2; exit 2; }

python3 - "$CACHED" "$FRESH" "$OUTPUT" "$MODULES_FILE" <<'PY'
import json
import pathlib
import sys

cached, fresh, output = map(pathlib.Path, sys.argv[1:4])
selected = None if not sys.argv[4] else set(pathlib.Path(sys.argv[4]).read_text().splitlines())
documents = [json.loads(cached.read_text()), json.loads(fresh.read_text())]
if any(document.get("schema") != "stratalint-raw-lean-report-v1" for document in documents):
    raise SystemExit("lean-report-merge: report schema mismatch")
modules = {}
for index, document in enumerate(documents):
    for entry in document.get("modules", []):
        name = entry.get("module")
        if index == 0 and selected is not None and name not in selected:
            continue
        if not isinstance(name, str) or name in modules:
            raise SystemExit(f"lean-report-merge: invalid or duplicate module: {name}")
        modules[name] = entry
result = {"modules": [modules[name] for name in sorted(modules)],
          "schema": "stratalint-raw-lean-report-v1"}
output.write_text(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(", ", ": ")) + "\n")
PY
