#!/bin/bash
# 器律⑨: caller-side collection of a terminal deposit-lane flight (read-only on the worktree).
# usage: collect_lane.sh FLIGHT_ID WORKTREE [ATTEMPT]   (TMPDIR-derived runner dir: ${TMPDIR:-/private/tmp}/consensus-rnd/sshx/FLIGHT/attempt-N)
# sentinel: COLLECT_OK; nonzero exit = artifacts missing (not a verdict on the lane).
set -uo pipefail
[ $# -ge 2 ] || { echo "COLLECT_USAGE: collect_lane.sh FLIGHT_ID WORKTREE [ATTEMPT]" >&2; exit 64; }
L=$1; WT=$2; N=${3:-1}; A="${TMPDIR:-/private/tmp}/consensus-rnd/sshx/$L/attempt-$N"
[ -f "$A/status.json" ] || { echo "COLLECT_NO_STATUS=$A" >&2; exit 65; }
[ -d "$WT/.git" ] || [ -f "$WT/.git" ] || { echo "COLLECT_BAD_WORKTREE=$WT" >&2; exit 66; }
echo "=== status"; grep -E '"(status|reason_code|carrier_exit|duration_seconds)"' "$A/status.json" | tr -d '\n ' ; echo; echo "sentinel=$([ -f "$A/completion.sentinel" ] && echo present || echo ABSENT)"
if [ -f "$A/result.json" ]; then echo "=== envelope"; python3 -X utf8 - "$A/result.json" <<'PY'
import json,sys
c=json.load(open(sys.argv[1],encoding='utf-8'))['conclusion']
print('lane',c.get('lane'),'branch',c.get('branch'),'base',c.get('base'),'pr',json.dumps(c.get('pr'))[:200])
print('lean',c.get('full_lean_build_exit'),'scribe',c.get('scribe_selftest_exit'),'mt',c.get('merge_tree_conflict_count'),'preflight',c.get('preflight_exits'),'door_closed',c.get('door_closed'))
for a in c.get('atoms',[]):
    print(' ',a.get('atom_id','')[:28], a.get('outcome'), a.get('ejection_class') or '', (a.get('gid') or '')[:110], 'bind' if a.get('bind_only') else '')
    if a.get('outcome')!='deposited': print('    ',(a.get('mathlib_trail') or a.get('notes') or '')[:240])
    cm=a.get('clause_matrix'); tc=a.get('tautology_check'); print('     clause_matrix rows:', len(cm) if isinstance(cm,list) else cm, '| tautology_check:', json.dumps(tc)[:160] if tc else None)
print('routing_check:', json.dumps(c.get('routing_check'),ensure_ascii=False)[:300])
print('ksd:', json.dumps([a.get('known_source_defects') for a in c.get('atoms',[])],ensure_ascii=False)[:400])
PY
else echo "=== envelope ABSENT"; fi
echo "=== tree"; git -C "$WT" status --porcelain | head -5; echo "branch: $(git -C "$WT" rev-parse --abbrev-ref HEAD)"; MB=$(git -C "$WT" merge-base origin/dev HEAD 2>/dev/null || echo ''); [ -n "$MB" ] && git -C "$WT" log --oneline "$MB..HEAD" | cut -c1-110
if [ -n "$MB" ]; then
  echo "=== non-added paths vs merge-base"; git -C "$WT" diff --name-status "$MB..HEAD" | grep -v '^A' | cut -c1-140
  echo "=== out-of-scope paths"; git -C "$WT" diff --name-only "$MB..HEAD" | grep -v -E '^(D5|Blueprint|Golden|Meta/Digestion|Evidence)/' | cut -c1-140
  echo "=== receipts"; for p in $(git -C "$WT" diff --name-only --diff-filter=A "$MB..HEAD" | grep '^Meta/Digestion/formalizations/'); do git -C "$WT" cat-file -e "origin/dev:$p" 2>/dev/null && echo "COLLISION $p"; done; echo "receipts added: $(git -C "$WT" diff --name-only --diff-filter=A "$MB..HEAD" | grep -c '^Meta/Digestion/formalizations/')"
  echo "=== buckets"; for d in $(git -C "$WT" diff --name-only --diff-filter=A "$MB..HEAD" | grep '^D5/.*\.lean$' | xargs -n1 dirname 2>/dev/null | sort -u); do echo "$d dev=$(git -C "$WT" ls-tree origin/dev --name-only "$d/" | grep -c '\.lean$') +branch=$(git -C "$WT" diff --name-only --diff-filter=A "$MB..HEAD" | grep -c "^$d/[^/]*\.lean$")"; done
  echo "=== merge-tree"; git -C "$WT" merge-tree --write-tree origin/dev HEAD >/dev/null 2>&1 && echo clean || echo CONFLICT
fi
echo "=== PR"; env -u GH_TOKEN -u GITHUB_TOKEN gh pr list --repo the-omega-institute/trureturing --head "$(git -C "$WT" rev-parse --abbrev-ref HEAD)" --state all --json number,state,isDraft,autoMergeRequest,mergeStateStatus --jq '.[]|"\(.number) \(.state) draft=\(.isDraft) auto=\(.autoMergeRequest!=null) \(.mergeStateStatus)"'
echo COLLECT_OK
