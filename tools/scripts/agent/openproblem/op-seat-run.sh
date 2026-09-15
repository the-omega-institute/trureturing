#!/bin/bash
# op-seat-run.sh <seat-name>
#
# Run one codex-cli seat to completion and leave its verdict in the seat directory.
#
# Layout, under $OP_SEAT_ROOT (default ~/omega-op/seats):
#   <seat>/prompt.txt    the brief, fed on stdin
#   <seat>/schema.json   the result envelope schema
#   <seat>/cwd.txt       the worktree to run in; defaults to $OP_WORKTREE_DEFAULT
#   <seat>/result.json   written by codex itself
#   <seat>/run.log       stdout and stderr, plus SEAT_START / SEAT_EXIT / SEAT_END
#   <seat>/DONE          sentinel, touched on every exit path
#
# Four invocation details are load-bearing and each was learned from a failed run:
#
#   --skip-git-repo-check  omitting it exits 1 with no result and the only message is
#                          "Not inside a trusted directory", which reads like a hard problem.
#   prompt on stdin        a large brief passed as a positional argument is mangled by the
#                          shell: $, backticks, angle brackets and newlines do not survive.
#   -o result.json         the verdict must be an artefact codex writes itself. Asking the
#                          model to write it with shell commands makes it optional, and it
#                          gets skipped; stdout is not admissible as evidence of completion.
#   approval_policy/sandbox  exec has no -a flag, so the policy goes through -c, and
#                          workspace-write with disk-full-read-access lets the seat read the
#                          whole tree while writing only where it should.
#
# The schema is checked before launch. OpenAI structured output runs strict, so every object
# with additionalProperties false must list all of its properties in required; one missing key
# fails the whole run with invalid_json_schema, exit 1, and no result. Catching that here costs
# milliseconds and saves a seat lifetime.
set -u
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$HOME/.dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
export LC_ALL=C

SEAT_ROOT="${OP_SEAT_ROOT:-$HOME/omega-op/seats}"
WORKTREE_DEFAULT="${OP_WORKTREE_DEFAULT:-$HOME/omega-op/wt-op1}"

N="${1:?seat name}"
D="$SEAT_ROOT/$N"
[ -f "$D/prompt.txt" ] || { echo "NO_PROMPT $D/prompt.txt" >&2; exit 9; }
[ -f "$D/schema.json" ] || { echo "NO_SCHEMA $D/schema.json" >&2; exit 9; }
[ -s "$D/prompt.txt" ] || { echo "EMPTY_PROMPT $D/prompt.txt" >&2; exit 9; }

python3 - "$D/schema.json" <<'PY' || exit 8
import json, sys

path = sys.argv[1]
try:
    schema = json.load(open(path, encoding="utf-8"))
except Exception as exc:
    print(f"SCHEMA_UNPARSEABLE {path}: {exc}", file=sys.stderr)
    raise SystemExit(1)

problems = []

def walk(node, where):
    if isinstance(node, list):
        for i, item in enumerate(node):
            walk(item, f"{where}[{i}]")
        return
    if not isinstance(node, dict):
        return
    if node.get("type") == "object" and node.get("additionalProperties") is False:
        props = set(node.get("properties", {}))
        required = set(node.get("required", []))
        missing = props - required
        if missing:
            problems.append(f"{where}: required omits {sorted(missing)}")
    for key, value in node.items():
        walk(value, f"{where}.{key}")

walk(schema, "$")
if problems:
    print("SCHEMA_NOT_STRICT — OpenAI structured output would reject this:", file=sys.stderr)
    for p in problems:
        print("  " + p, file=sys.stderr)
    print("Express an optional field as required plus nullable, not by omitting it from required.",
          file=sys.stderr)
    raise SystemExit(1)
PY

CWD=$(cat "$D/cwd.txt" 2>/dev/null || echo "$WORKTREE_DEFAULT")
[ -d "$CWD" ] || { echo "NO_WORKTREE $CWD" >&2; exit 9; }

# Seats build, so a seat on a worktree of a second clone silently grows a second cache.
bash "$(dirname "$0")/op-require-base.sh" "$CWD" "${OP_BASE_GIT:-$HOME/Desktop/omega/trureturing/.git}" \
  || { echo "SEAT_FOREIGN_CLONE $CWD" >&2; exit 7; }

rm -f "$D/result.json" "$D/DONE"
cd "$CWD" || exit 9
echo "SEAT_START=$(date +%T) CWD=$CWD HEAD=$(git rev-parse --short HEAD 2>/dev/null)" > "$D/run.log"

codex exec --skip-git-repo-check \
  -c 'approval_policy="never"' \
  -c 'sandbox_permissions=["disk-full-read-access"]' \
  -s workspace-write \
  --output-schema "$D/schema.json" \
  -o "$D/result.json" \
  < "$D/prompt.txt" >> "$D/run.log" 2>&1
echo "SEAT_EXIT=$?" >> "$D/run.log"
echo "SEAT_END=$(date +%T)" >> "$D/run.log"
touch "$D/DONE"
