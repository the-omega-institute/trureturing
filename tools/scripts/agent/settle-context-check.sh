#!/bin/bash
# Pre-flight for a settle batch: ask the REAL oracle (atom-context) about EVERY row and
# report all failures at once, instead of letting the door halt on the first one.
#
# atom-context re-atomizes the source volume on each call and looks for the atom among the
# segments the CURRENT text yields (its output carries `index=i/N`). A paragraph can still be
# present in the volume byte-for-byte and yet no longer be one of those segments, so counting
# bytes is NOT this judgement — measured counterexample 2026-09-16, atom ca0bc6da03.
#
# usage: settle-context-check.sh <lane-root> <plan.json> [--allow-missing]
# exit 0 = every row usable; 1 = at least one row unusable (all of them printed)
set -uo pipefail
LANE="$1"; PLAN="$2"; ALLOW="${3:-}"
BIN="$LANE/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint"
[ -x "$BIN" ] || { echo "SETTLE_CONTEXT_CHECK_NO_BINARY $BIN (run one make target in the lane first)"; exit 2; }
cd "$LANE" || exit 2
bad=0; n=0; skipped=0
while IFS= read -r a; do
  if [ ! -f "Meta/Digestion/atoms/sha256/$a" ]; then
    if [ "$ALLOW" = "--allow-missing" ]; then skipped=$((skipped+1)); continue; fi
    echo "SETTLE_UNUSABLE atom_id=$a reason=no-blob"; bad=$((bad+1)); continue
  fi
  n=$((n+1))
  out=$("$BIN" atom-context --atom-id "$a" 2>&1)
  if printf '%s' "$out" | grep -q '^ATOM_CONTEXT atom_id='; then
    if printf '%s' "$out" | grep -q 'occurrences='; then
      echo "SETTLE_UNUSABLE atom_id=$a reason=multi-occurrence"; bad=$((bad+1))
    fi
  else
    r=$(printf '%s' "$out" | grep -oE 'ATOM_CONTEXT_INVALID [A-Z_]+' | head -1)
    echo "SETTLE_UNUSABLE atom_id=$a reason=${r:-unknown}"; bad=$((bad+1))
  fi
done < <(python3 -c "import json,sys;[print(r['atom_id']) for r in json.load(open(sys.argv[1]))['settle']]" "$PLAN")
echo "SETTLE_CONTEXT_CHECK checked=$n skipped_missing=$skipped unusable=$bad"
[ "$bad" -eq 0 ]
