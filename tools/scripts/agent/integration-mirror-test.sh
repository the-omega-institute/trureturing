#!/bin/bash
# Behavior tests for the required-check guard of integration-mirror.sh. Each
# case runs the script with --dry-run in a linked worktree of a synthetic
# repository whose origin is a local bare repository; a gh stub first on PATH
# serves branch protection and issue JSON.
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

echo "INTEGRATION_MIRROR_TEST passed=$passed failed=$failures"
[[ $failures -eq 0 ]]
