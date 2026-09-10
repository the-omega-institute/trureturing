#!/usr/bin/env bash
# op-proof-edges.sh — kernel-derived direct proof/type dependency edges (consumer → prerequisite) among a module's
# non-auxiliary constants, plus per-constant axiom sets and a closed-numeric-certificate flag, from the elaborated
# environment. usage: op-proof-edges.sh WORKTREE MODULE_DOTTED OUT_JSON(absolute)   sentinel: EDGES_OK edges=<n> kernel_nonauxiliary_constants=<n> | EDGES_FAIL
# The second count is what the kernel enumerated, NOT the authored public surface; the
# rendered table filters to authored declarations and is legitimately smaller. A review
# seat read the old `public=` label as an inconsistency against that table.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
W="${1:?worktree}"; MOD="${2:?module dotted}"; OUT="${3:?out json (absolute)}"; SP="$(cd "$(dirname "$0")" && pwd)"
cd "$W" || { echo "EDGES_FAIL no-worktree"; exit 3; }
eval "$(sed -n '/^export PATH=/p' "$ROOT"/tools/scripts/local-harness-gate.sh)"
[ -d .lake/build ] || { echo "EDGES_FAIL cold tree (no .lake/build)"; exit 3; }
WORK="${WORK:-${TMPDIR:-/tmp}/deposit-evidence}"; mkdir -p "$WORK"
F="$WORK/proof-edges-$(echo "$MOD" | tr '.' '_').lean"; sed -e "s#__IMPORT__#$MOD#" -e "s#__MODULE__#$MOD#" "$SP/proof-edges-template.lean" > "$F"
LOG="${F%.lean}.log"; lake env lean "$F" > "$LOG" 2>&1; rc=$?
grep -q 'EDGE ' "$LOG" || { echo "EDGES_FAIL lean rc=$rc (no EDGE lines); log=$LOG"; grep -n 'error' "$LOG" | head -3; exit 4; }
python3 - "$LOG" "$OUT" "$MOD" <<'PY'
import sys,json,re
log,out,mod=sys.argv[1:4]; edges={}; kinds={}; numeric={}; axioms={}; external={}
for line in open(log):
    m=re.search(r'EDGE (.+?) :: (\w+) :: (.*?) :: NUM=(true|false) :: AX=(.*?) :: EXT=(.*)$',line.rstrip('\n'))
    if not m: continue
    name,kind,ds,num,ax,ext=m.groups()
    edges[name]=[d.strip() for d in ds.split(',') if d.strip()]; kinds[name]=kind
    numeric[name]=(num=='true'); axioms[name]=[a.strip() for a in ax.split(',') if a.strip()]; external[name]=[e.strip() for e in ext.split(',') if e.strip()]
d={'module':mod,'source':'kernel environment (Expr.getUsedConstants on value+type, aux constants expanded)','direction':'consumer -> prerequisite',
   'edges':dict({'direction':'consumer->prerequisite'},**edges),'kinds':kinds,'numeric_certificate':numeric,'axioms':axioms,'external_deps':external,
   'public_declarations':[{'name':n,'kind':k} for n,k in kinds.items() if '(private)' not in n]}
json.dump(d,open(out,'w'),ensure_ascii=False,indent=1); print('EDGES_OK edges=%d kernel_nonauxiliary_constants=%d'%(len(edges),len(d['public_declarations'])))
PY
