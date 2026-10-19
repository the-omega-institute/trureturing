#!/bin/bash
# Portable brief orchestration. See the openproblem README for inputs.
set -euo pipefail
BRIEF_ENTRY_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
if [ "${1:-}" = --selftest ]; then
  python3 "$BRIEF_ENTRY_DIR/selftest.py" "${BASH_SOURCE[0]}"
  python3 "$BRIEF_ENTRY_DIR/../chains/selftest.py" stageb-go
  exit $?
fi
dispatch=0
if [ "${1:-}" = --dispatch ]; then dispatch=1; shift; fi
. "$BRIEF_ENTRY_DIR/common.sh"
[ "$#" = 3 ] || op_fail 10 USAGE "stageb_prep.sh: expected 3 arguments"
S=$OP_SCRATCH
L=$1; NYX=$2; MF=$3
op_name "$L"
case "$NYX" in architecture|quality) ;; *) op_fail 13 INVALID_INPUT 'seat must be architecture or quality';; esac
case "${REGEN:-1}" in 0|1) ;; *) op_fail 13 INVALID_INPUT 'REGEN must be 0 or 1';; esac
op_file "$S/lanes/$L.json"
WT=$(python3 - "$S/lanes/$L.json" "$OP_MAIN" <<'PY'
from common import entry, fail, lane_spec
from pathlib import Path
def main(argv):
    data = lane_spec(argv[1])
    path = Path(data['worktree'])
    path = (path if path.is_absolute() else Path(argv[2]) / path).resolve()
    if not path.is_dir():
        fail(11, 'worktree missing: ' + str(path))
    print(path)
raise SystemExit(entry(main, minimum=2, maximum=2))
PY
)
for b in lean-report-block.md scoped-doors-block.md ci-gate-block.md dossier-sections-block.md frozen-state-contract-block.md sync-before-emit-block.md one-builder-commit-block.md reuse-sweep-block.md; do op_file "$(op_block "$b")"; done
if [ -n "${ORCH_NOTE:-}" ]; then op_file "$ORCH_NOTE"; fi
cd "$OP_MAIN" || exit 3
if [ "${REGEN:-1}" = 1 ]; then bash "$OP_BRIEF_DIR/stages.sh" "$L" "$NYX" || exit 3; fi
R=$(op_latest_result "$MF")
[ "$R" != NO_RESULT ] || op_fail 11 INPUT_MISSING "mirror result $MF"
python3 "$OP_OPENPROBLEM_DIR/fill_mirror_fixes.py" "$S" "$L" "$R" || exit 3
f="$S/briefs/impl-op-w1-$L.stageB.filled.md"
grep -q 'One lean-report producer per machine' "$f" || { printf '\n' >> "$f"; cat "$(op_block lean-report-block.md)" >> "$f"; }
grep -q 'Report kinds at the freeze doors' "$f" || { printf '\n' >> "$f"; cat "$(op_block scoped-doors-block.md)" >> "$f"; }
grep -q 'No local full gate; the required CI check is the gate' "$f" || { printf '\n' >> "$f"; cat "$(op_block ci-gate-block.md)" >> "$f"; }
grep -q 'Problems dossier sections (binding)' "$f" || cat "$(op_block dossier-sections-block.md)" >> "$f"
grep -q 'Frozen ledger contract (binding' "$f" || cat "$(op_block frozen-state-contract-block.md)" >> "$f"
grep -q 'Sync with dev before the first emit' "$f" || cat "$(op_block sync-before-emit-block.md)" >> "$f"
grep -q 'One builder commit for the door output (binding' "$f" || cat "$(op_block one-builder-commit-block.md)" >> "$f"
V=$(python3 -c 'import json,sys;d=json.load(open(sys.argv[1]));c=d.get("conclusion",d);print(c.get("verdict"))' "$R")
python3 - "$S/lanes/$L.json" "$f" <<'PYT'
from common import Context
import sys,json
d=json.load(open(sys.argv[1]))
open(sys.argv[2],'a').write('\n## Lane target (binding in Stage B: every dossier, Triage, Library and placement requirement below must be delivered; a later mirror-check fix or orchestrator note overrides it where they conflict)\n\n'+d['target_md'].strip()+'\n')
PYT
grep -q "Reuse sweep before the door" "$f" || cat "$(op_block reuse-sweep-block.md)" >> "$f"
if [ -n "${ORCH_NOTE:-}" ] && [ -f "$ORCH_NOTE" ]; then printf '\n## Orchestrator notes (they override a mirror-check fix where the two conflict)\n' >> "$f"; cat "$ORCH_NOTE" >> "$f"; fi
JF=${JF_FLIGHT:-}
if [ -n "$JF" ]; then
  JR=$(op_latest_result "$JF")
  [ "$JR" != NO_RESULT ] || op_fail 11 INPUT_MISSING "judgement result $JF"
  [ -n "$JR" ] && python3 - "$JR" "$f" <<'PYJ'
from common import Context
import sys,json
c=json.load(open(sys.argv[1])).get('conclusion',{})
bf=c.get('blocking_findings') or []
out=['','## Judgement-form fixes (pre-freeze §3.2 seat)','Verdict: %s. Apply these before the doors; a declaration judged bind-only must be inlined as a `have` (or removed) and every `proof_shape` in the second comment block and the PR body must match the judgement:' % c.get('verdict')]
for i,x in enumerate(bf,1): out.append('%d. %s' % (i, json.dumps(x,ensure_ascii=False)))
if not bf: out.append('(no blocking findings)')
open(sys.argv[2],'a').write('\n'.join(out)+'\n')
PYJ
fi
printf '\n## Pre-freeze review identity\nThe mirror-check seat for this lane is codex-cli flight `%s` (verdict %s; any blocking findings are listed under "Mirror-check fixes" and must all be applied before the doors). Use this id in the PR body sentence (a).\n' "$MF" "$V" >> "$f"
python3 "$OP_BRIEF_DIR/fix_door_base.py" "$S/briefs/impl-op-w1-$L.stageB.filled.md"
if [ "$dispatch" = 1 ]; then
  bash "$OP_OPENPROBLEM_DIR/pipeline/seat-wait.sh" "${OP_NAME_PREFIX}implb-$L-r1" "$f" "$WT" implementation 0
fi
