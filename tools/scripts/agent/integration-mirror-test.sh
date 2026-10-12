#!/bin/bash
# Behavior tests use real Git in linked fixture worktrees and stub GitHub.
# CI lifetimes advance a logical clock through the native watcher stub.
# Usage: bash tools/scripts/agent/integration-mirror-test.sh
set -euo pipefail

SUBJECT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/integration-mirror.sh"
[[ -f "$SUBJECT" ]] || { echo "missing $SUBJECT" >&2; exit 2; }
for tool in git jq; do command -v "$tool" >/dev/null || { echo "$tool is required" >&2; exit 2; }; done
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
failures=0 passed=0

export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
git init -q --bare "$WORK/origin.git"
git init -q -b dev "$WORK/src"
git -C "$WORK/src" commit -q --allow-empty -m base
git -C "$WORK/src" push -q "$WORK/origin.git" dev dev:integration-x
git -C "$WORK/origin.git" symbolic-ref HEAD refs/heads/dev
git clone -q "$WORK/origin.git" "$WORK/main"
git -C "$WORK/main" worktree add -q --detach "$WORK/lane" origin/dev
TIP="$(git -C "$WORK/lane" rev-parse HEAD)"

mkdir -p "$WORK/bin" "$WORK/issues"
cat > "$WORK/bin/gh" <<'EOF'
#!/bin/bash
case "$1 ${2:-}" in
  "auth status") exit 0 ;;
  "repo view") echo o/r; exit 0 ;;
esac
[[ "$1" == api ]] || { echo "unexpected gh call: $*" >&2; exit 90; }
case "$2" in
  repos/o/r/branches/dev) printf '%s\n' "$GH_DEV_JSON" ;;
  repos/o/r/branches/integration-x) printf '%s\n' "$GH_INTEGRATION_JSON" ;;
  repos/o/r/issues/*)
    n="${2##*/}"
    if [[ -f "$GH_ISSUES/$n" ]]; then cat "$GH_ISSUES/$n"
    elif [[ -f "$GH_ISSUES/$n.transport" ]]; then echo "HTTP 502" >&2; exit 1
    else echo '{"message":"Not Found","status":"404"}'; exit 1
    fi ;;
  *) echo "unexpected gh api path: $2" >&2; exit 90 ;;
esac
EOF
chmod +x "$WORK/bin/gh"
echo '{"number":5,"state":"open","title":"declares the check change"}' > "$WORK/issues/5"
echo '{"number":7,"state":"closed","title":"finished change"}' > "$WORK/issues/7"
: > "$WORK/issues/8.transport"
echo '{"number":90,"state":"open","title":"another object"}' > "$WORK/issues/9"

protection() {
  jq -cn --args '{protected:true,protection:{required_status_checks:{contexts:$ARGS.positional,checks:[]}}}' "$@"
}
OLD="$(protection 'push / engineering' 'push / current' delta)"
NEW="$(protection current 'tests-cli / unit')"

# run_mirror INTEGRATION_JSON [extra arguments...]; sets RC and LOG.
run_mirror() {
  local integration_json="$1"; shift
  RC=0
  LOG="$(cd "$WORK/lane" && env -i HOME="$HOME" PATH="$WORK/bin:$PATH" TMPDIR="$WORK" \
    GH_DEV_JSON="$OLD" GH_INTEGRATION_JSON="$integration_json" GH_ISSUES="$WORK/issues" \
    bash "$SUBJECT" --integration integration-x --since "$TIP" --dry-run "$@" 2>&1)" || RC=$?
}

# check NAME EXIT [FRAGMENT...]: the run exited EXIT and its log contains every FRAGMENT.
check() {
  local name="$1" want="$2" fragment; shift 2
  if [[ $RC -ne $want ]]; then
    echo "FAIL $name: exit $RC, want $want; log: $LOG"; failures=$((failures + 1)); return
  fi
  for fragment in "$@"; do
    if [[ "$LOG" != *"$fragment"* ]]; then
      echo "FAIL $name: log lacks '$fragment'; log: $LOG"; failures=$((failures + 1)); return
    fi
  done
  echo "PASS $name"; passed=$((passed + 1))
}

run_mirror "$OLD"; check equal-sets 0 'MIRROR_RESULT mirrored=0 pending=0 exit=0'
run_mirror "$OLD" --required-checks-under-test '#5'; check equal-sets-with-reference 0 'MIRROR_RESULT mirrored=0 pending=0 exit=0'
run_mirror "$NEW"; check differ-without-reference 64 'same checks as dev'
run_mirror "$NEW" --required-checks-under-test '#5'; check differ-open-reference 0 \
  "required checks under test (#5 open): dev=$(jq -c '.protection.required_status_checks.contexts | unique' <<<"$OLD") integration=$(jq -c '.protection.required_status_checks.contexts | unique' <<<"$NEW")" \
  'MIRROR_RESULT mirrored=0 pending=0 exit=0'
run_mirror "$NEW" --required-checks-under-test '#6'; check differ-missing-reference 64 'cannot read #6'
run_mirror "$NEW" --required-checks-under-test '#7'; check differ-closed-reference 64 '#7 is closed'
run_mirror "$NEW" --required-checks-under-test '#8'; check differ-unreadable-reference 64 'cannot read #8'
run_mirror "$NEW" --required-checks-under-test '#9'; check differ-mismatched-reference 64 'not an issue or PR'
run_mirror "$NEW" --required-checks-under-test '5'; check malformed-reference 64 'must be an issue or PR reference'
run_mirror "$(protection)" --required-checks-under-test '#5'; check empty-integration-set 64 'nonempty required-check set'


# Each lifecycle case has an independent remote and JSONL state.
PROTOCOL="$(dirname "$SUBJECT")/../worktree/worktree_protocol.py"
git -C "$WORK/src" switch -q -c feature
printf 'target\n' >"$WORK/src/target"
git -C "$WORK/src" add target
git -C "$WORK/src" commit -qm feature
git -C "$WORK/src" switch -q dev
git -C "$WORK/src" merge -q --no-ff -m 'Merge pull request #11 from o/feature' feature
LANDING=$(git -C "$WORK/src" rev-parse HEAD)

cat >"$WORK/bin/gh" <<'EOF'
#!/usr/bin/env python3
import json, os, subprocess, sys
from pathlib import Path
a = sys.argv[1:]
f = Path(os.environ['GH_FIXTURE'])
mode = os.environ['GH_CASE']
with (f / 'calls').open('a') as log:
    log.write(json.dumps(a) + '\n')
def emit(value):
    print(json.dumps(value))
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
def tick(value):
    (f / 'clock').write_text(str(value))
clock = int((f / 'clock').read_text()) if (f / 'clock').exists() else 0
head = git('ls-remote', 'origin', 'refs/heads/mirror/integration-x/11').split()
head = head[0] if head else ''
if a[:2] == ['auth', 'status']: pass
elif a[:2] == ['repo', 'view']: print('o/r')
elif a[0] == 'api':
    path = a[1]
    if '/branches/' in path:
        emit(dict(protected=True, protection=dict(required_status_checks=dict(contexts=['required']))))
    elif '/commits/' in path and path.endswith('/pulls'):
        sha = path.split('/')[-2]
        emit(json.loads((f / 'associations.json').read_text()).get(sha, []))
    elif '/pulls/' in path:
        record = json.loads((f / 'prs.json').read_text()).get(path.split('/')[-1])
        if record is None: print('Not Found', file=sys.stderr); sys.exit(1)
        emit(record)
    else: raise SystemExit('unexpected api: ' + repr(a))
elif a[:2] == ['pr', 'list']:
    state = 'MERGED' if mode == 'reuse-merged' else 'OPEN'
    if mode in ('reuse-open', 'reuse-merged') or (f / 'created').exists():
        emit([dict(number=91, state=state, headRefOid=head,
                   mergedAt='2030-01-01T00:00:00Z' if state == 'MERGED' else None,
                   mergeCommit=dict(oid=head))])
    else: emit([])
elif a[:2] == ['pr', 'create']:
    (f / 'created').touch()
    git('push', 'origin', head + ':refs/pull/91/head')
    print('https://example.invalid/o/r/pull/91')
elif a[:2] == ['pr', 'checks']:
    if '--watch' in a:
        if mode in ('late', 'transport') and clock < 36000:
            print('no checks reported', file=sys.stderr); sys.exit(1)
        sys.exit(0)
    if mode == 'malformed': print('not json'); sys.exit(1)
    if mode == 'wrong-shape': emit({'checks': []}); sys.exit(1)
    if mode == 'multiple-json': emit([]); emit([]); sys.exit(1)
    if mode == 'missing' or mode in ('late', 'transport') and clock < 36000:
        emit([]); sys.exit(1)
    bucket = {'fail': 'fail', 'cancel': 'cancel', 'pending-terminal': 'pending'}.get(mode, 'pass')
    emit([dict(name='required', bucket=bucket, state=bucket.upper())])
    sys.exit(8 if bucket == 'pending' else 1 if bucket in ('fail', 'cancel') else 0)
elif a[:2] == ['run', 'list']:
    assert '--commit' in a and a[a.index('--commit') + 1] == head, a
    assert '--event' in a and a[a.index('--event') + 1] == 'pull_request', a
    emit([dict(databaseId=701, headSha=head, event='pull_request', status='completed' if clock >= 36000 or mode not in ('late', 'transport') else 'in_progress', pull_requests=[])])
elif a[:2] == ['run', 'watch']:
    assert a[2] == '701', a
    if mode == 'transport' and not (f / 'transport-failed').exists():
        (f / 'transport-failed').touch()
        print('HTTP 503', file=sys.stderr); sys.exit(1)
    tick(36000)
elif a[:2] == ['pr', 'merge']:
    (f / 'merged').touch()
    git('push', 'origin', head + ':refs/heads/integration-x')
elif a[:3] == ['pr', 'view', '11']:
    emit(dict(title='target', url='https://example.invalid/o/r/pull/11'))
elif a[:3] == ['pr', 'view', '91']:
    emit(dict(state='MERGED', mergedAt='2030-01-01T00:00:00Z'))
else: raise SystemExit('unexpected gh: ' + repr(a))
EOF
cat >"$WORK/bin/sleep" <<'EOF'
#!/usr/bin/env python3
import os, sys
from pathlib import Path
f = Path(os.environ['GH_FIXTURE']) / 'clock'
f.write_text(str((int(f.read_text()) if f.exists() else 0) + int(sys.argv[1])))
EOF
chmod +x "$WORK/bin/gh" "$WORK/bin/sleep"

new_case() {
  CASE="$WORK/$1"
  mkdir -p "$CASE/tmp"
  git clone -q --bare "$WORK/src" "$CASE/origin.git"
  git -C "$CASE/origin.git" update-ref refs/heads/integration-x "$TIP"
  git clone -q "$CASE/origin.git" "$CASE/main"
  git -C "$CASE/main" worktree add -q --detach "$CASE/lane" origin/dev
  jq -cn --arg sha "$LANDING" '{($sha):[{number:11}]}' >"$CASE/associations.json"
  jq -cn --arg sha "$LANDING" '{"11":{number:11,merged:true,base:{ref:"dev",repo:{full_name:"o/r"}},merge_commit_sha:$sha}}' >"$CASE/prs.json"
}
lifecycle() {
  local mode=$1; shift
  RC=0
  LOG="$(cd "$CASE/lane" && env PATH="$WORK/bin:$PATH" TMPDIR="$CASE/tmp" \
    GH_FIXTURE="$CASE" GH_CASE="$mode" bash "$SUBJECT" --integration integration-x \
    --state "$CASE/state.jsonl" "$@" 2>&1)" || RC=$?
}
assert_case() {
  local name=$1; shift
  if "$@" >/dev/null; then echo "PASS $name"; passed=$((passed + 1))
  else echo "FAIL $name"; failures=$((failures + 1)); fi
}
for mode in late transport malformed wrong-shape multiple-json fail cancel missing pending-terminal; do
  new_case "$mode"
  want=69 status=incomplete
  case "$mode" in late|transport) want=0 status=merged ;; fail|cancel) want=66 status=red ;; esac
  lifecycle "$mode" --since "$TIP"
  check "lifecycle-$mode" "$want" "exit=$want"
  assert_case "valid-state-$mode" jq -se --arg status "$status" --arg sha "$LANDING" \
    'length == 1 and all(.[]; .status == $status and .merge == $sha and (.verdicts | type == "array"))' "$CASE/state.jsonl"
  if [[ $want != 0 ]]; then assert_case "no-merge-$mode" test ! -e "$CASE/merged"; fi
  if [[ $mode == late ]]; then
    assert_case late-native-lifetime jq -se 'any(.[]; .[0:2] == ["run","watch"])' "$CASE/calls"
    assert_case late-beyond-reentry-window test "$(cat "$CASE/clock")" -ge 36000
  fi
done

for failure in fail malformed; do
  new_case "resume-$failure"
  if [[ $failure == fail ]]; then first_status=red first_rc=66
  else first_status=incomplete first_rc=69; fi
  lifecycle "$failure" --since "$TIP"; check "resume-first-$failure" "$first_rc"
  lifecycle pass; check "resume-retries-$failure" 0 'MIRROR_RESULT mirrored=1 pending=0 exit=0'
  lifecycle pass; check "resume-skips-completed-$failure" 0 'MIRROR_RESULT mirrored=0 pending=0 exit=0'
  assert_case "resume-single-pr-$failure" jq -se '[.[] | select(.[0:2] == ["pr","create"])] | length == 1' "$CASE/calls"
  assert_case "resume-state-$failure" jq -se --arg sha "$LANDING" --arg status "$first_status" \
    'map(.status) == [$status,"merged"] and all(.[]; .merge == $sha)' "$CASE/state.jsonl"
done

for mode in reuse-branch reuse-open reuse-merged; do
  new_case "$mode"
  python3 -B "$PROTOCOL" --source "$CASE/lane" prepare-mirror --path "$CASE/prepared" \
    --branch mirror/integration-x/11 --base "$TIP" --merge "$LANDING" \
    --message 'mirror: #11 Merge pull request #11 from o/feature' >"$CASE/prepared.json"
  HEAD_BEFORE=$(jq -r .commit "$CASE/prepared.json")
  python3 -B "$PROTOCOL" --source "$CASE/lane" remove --path "$CASE/prepared" >/dev/null
  git -C "$CASE/origin.git" update-ref refs/pull/91/head "$HEAD_BEFORE"
  if [[ $mode == reuse-merged ]]; then git -C "$CASE/origin.git" update-ref refs/heads/integration-x "$HEAD_BEFORE"; fi
  lifecycle "$mode" --since "$TIP"; check "$mode" 0
  assert_case "$mode-keeps-head" test "$HEAD_BEFORE" = "$(git -C "$CASE/origin.git" rev-parse refs/heads/mirror/integration-x/11)"
  if [[ $mode != reuse-branch ]]; then
    assert_case "$mode-no-create" jq -se 'all(.[]; .[0:2] != ["pr","create"])' "$CASE/calls"
  fi
done

new_case reject-two-parent
OLD_HEAD=$(git -C "$CASE/lane" commit-tree "$LANDING^{tree}" -p "$TIP" -p "$LANDING" \
  -m 'mirror: #11 Merge pull request #11 from o/feature')
git -C "$CASE/lane" push -q origin "$OLD_HEAD:refs/heads/mirror/integration-x/11"
lifecycle pass --since "$TIP"
check reject-two-parent 69 'mirror_requires_single_parent'
assert_case reject-two-parent-preserves-head test "$OLD_HEAD" = "$(git -C "$CASE/origin.git" rev-parse refs/heads/mirror/integration-x/11)"
assert_case reject-two-parent-no-pr test ! -e "$CASE/created"

# Squash subjects supply candidates when the association endpoint is empty.
git -C "$WORK/src" switch -q dev
printf 'squash\n' >"$WORK/src/squash"
git -C "$WORK/src" add squash
git -C "$WORK/src" commit -qm 'squashed fix for #404 (#12)'
SQUASH=$(git -C "$WORK/src" rev-parse HEAD)
git -C "$WORK/src" switch -q -c custom
printf 'custom\n' >"$WORK/src/custom"
git -C "$WORK/src" add custom
git -C "$WORK/src" commit -qm custom
git -C "$WORK/src" switch -q dev
git -C "$WORK/src" merge -q --no-ff -m 'Custom integration subject' custom
CUSTOM=$(git -C "$WORK/src" rev-parse HEAD)
new_case identification
jq --arg sha "$CUSTOM" '. + {($sha):[{number:13},{number:99}]}' "$CASE/associations.json" >"$CASE/next.json"
mv "$CASE/next.json" "$CASE/associations.json"
jq --arg squash "$SQUASH" --arg custom "$CUSTOM" '. + {
  "12":{number:12,merged:true,base:{ref:"dev",repo:{full_name:"o/r"}},merge_commit_sha:$squash},
  "13":{number:13,merged:true,base:{ref:"dev",repo:{full_name:"o/r"}},merge_commit_sha:$custom},
  "99":{number:99,merged:true,base:{ref:"other",repo:{full_name:"o/r"}},merge_commit_sha:$custom}}' \
  "$CASE/prs.json" >"$CASE/next.json"
mv "$CASE/next.json" "$CASE/prs.json"
lifecycle pass --since "$TIP" --dry-run
check identification-all-first-parent 0 'PLAN order=1 original_pr=11' 'PLAN order=2 original_pr=12' 'PLAN order=3 original_pr=13' 'pending=3'
assert_case dry-run-no-publish test ! -e "$CASE/created"
for invalid in unmerged wrong-base wrong-commit wrong-repository ambiguous; do
  cp "$CASE/prs.json" "$CASE/saved.json"
  case "$invalid" in
    unmerged) filter='."13".merged = false' ;;
    wrong-base) filter='."13".base.ref = "other"' ;;
    wrong-commit) filter='."13".merge_commit_sha = "0000000000000000000000000000000000000000"' ;;
    wrong-repository) filter='."13".base.repo.full_name = "other/repo"' ;;
    ambiguous) filter='."99".base.ref = "dev"' ;;
  esac
  jq "$filter" "$CASE/saved.json" >"$CASE/prs.json"
  lifecycle pass --since "$TIP"
  check "identification-$invalid" 64 "$CUSTOM"
  assert_case "$invalid-no-publication" test -z "$(git -C "$CASE/origin.git" for-each-ref refs/heads/mirror/)"
  mv "$CASE/saved.json" "$CASE/prs.json"
done
git -C "$WORK/src" commit -q --allow-empty -m 'no associated PR'
UNIDENTIFIED=$(git -C "$WORK/src" rev-parse HEAD)
new_case unidentified
lifecycle pass --since "$CUSTOM"
check unidentified-first-parent 64 "$UNIDENTIFIED"
assert_case unidentified-no-publication test ! -e "$CASE/created"

echo "INTEGRATION_MIRROR_TEST passed=$passed failed=$failures"
[[ $failures -eq 0 ]]
