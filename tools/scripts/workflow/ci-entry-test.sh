#!/bin/bash
# Behavior tests for ci-entry.sh. Each case copies the script into a fresh
# synthetic repository, runs it with a fixed event environment, and checks the
# exit code, the hit value written to GITHUB_OUTPUT and the remote cleanup.
# Failure cases put a git wrapper first on PATH that fails one cleanup call.
# Usage: bash tools/scripts/workflow/ci-entry-test.sh
set -euo pipefail

SUBJECT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/ci-entry.sh"
[[ -f "$SUBJECT" ]] || { echo "missing $SUBJECT" >&2; exit 2; }
REAL_GIT="$(command -v git)" || { echo "git is required" >&2; exit 2; }
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
failures=0 passed=0

fail() { echo "FAIL $case_name: $*"; failures=$((failures + 1)); }

# Synthetic repository: BEFORE adds docs/readme.md, AFTER changes tools/a.txt;
# PR_HEAD branches from BEFORE and changes tools/b.txt; MERGE = BEFORE + PR_HEAD.
new_repo() {
  local repo="$WORK/$1"
  mkdir -p "$repo/tools/scripts/workflow" "$repo/docs"
  cp "$SUBJECT" "$repo/tools/scripts/workflow/ci-entry.sh"
  (
    cd "$repo"
    export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
    "$REAL_GIT" init -q -b main
    "$REAL_GIT" add -A && "$REAL_GIT" commit -qm base
    echo readme > docs/readme.md
    "$REAL_GIT" add -A && "$REAL_GIT" commit -qm before
    BEFORE="$("$REAL_GIT" rev-parse HEAD)"
    echo a > tools/a.txt
    "$REAL_GIT" add -A && "$REAL_GIT" commit -qm after
    AFTER="$("$REAL_GIT" rev-parse HEAD)"
    "$REAL_GIT" branch -q pr "$BEFORE"
    "$REAL_GIT" symbolic-ref HEAD refs/heads/pr
    "$REAL_GIT" reset -q --hard "$BEFORE"
    echo b > tools/b.txt
    "$REAL_GIT" add -A && "$REAL_GIT" commit -qm pr
    PR_HEAD="$("$REAL_GIT" rev-parse HEAD)"
    tree="$("$REAL_GIT" write-tree)"
    MERGE="$("$REAL_GIT" commit-tree "$tree" -p "$BEFORE" -p "$PR_HEAD" -m merge)"
    "$REAL_GIT" remote add origin "https://example.invalid/repo.git"
    "$REAL_GIT" update-ref refs/remotes/origin/dev "$BEFORE"
    # A remote-tracking ref without a configured remote survives `git remote remove`.
    "$REAL_GIT" update-ref refs/remotes/stale/dev "$BEFORE"
    printf '%s %s %s %s\n' "$BEFORE" "$AFTER" "$PR_HEAD" "$MERGE" > "$WORK/$1.ids"
  )
  read -r BEFORE AFTER PR_HEAD MERGE < "$WORK/$1.ids"
  REPO="$repo"
}

# Detach HEAD at a commit without a checkout verb.
at_commit() { "$REAL_GIT" -C "$REPO" update-ref --no-deref HEAD "$1"; "$REAL_GIT" -C "$REPO" reset -q --hard "$1"; }

# make_wrapper NAME STEP: a git wrapper that fails exactly the cleanup call named by STEP.
make_wrapper() {
  local dir="$WORK/bin-$1"
  mkdir -p "$dir"
  cat > "$dir/git" <<EOF
#!/bin/bash
case "$2" in
  remote-list) [[ \$# -eq 1 && "\$1" == remote ]] && { echo injected >&2; exit 73; } ;;
  remote-remove) [[ "\$1" == remote && "\${2:-}" == remove ]] && { echo injected >&2; exit 73; } ;;
  ref-list) [[ "\$1" == for-each-ref ]] && { echo injected >&2; exit 73; } ;;
  ref-delete) [[ "\$1" == update-ref && "\${2:-}" == -d ]] && { echo injected >&2; exit 73; } ;;
esac
exec "$REAL_GIT" "\$@"
EOF
  chmod +x "$dir/git"
  WRAPPER_PATH="$dir:$PATH"
}

# run_entry EVENT SHA PATHS [extra env assignments...]; sets RC, OUT (GITHUB_OUTPUT) and LOG.
run_entry() {
  local event="$1" sha="$2" paths="$3"; shift 3
  local output="$WORK/output-$case_name"
  local paths_env=()
  [[ "$paths" == __unset__ ]] || paths_env+=("CI_HIT_PATHS=$paths")
  : > "$output"
  RC=0
  LOG="$(env -i HOME="$HOME" PATH="${RUN_PATH:-$PATH}" GITHUB_EVENT_NAME="$event" GITHUB_SHA="$sha" \
    GITHUB_OUTPUT="$output" ${paths_env[@]+"${paths_env[@]}"} "$@" \
    bash "$REPO/tools/scripts/workflow/ci-entry.sh" 2>&1)" || RC=$?
  OUT="$(cat "$output")"
}

expect_hit() {
  local want="$1"
  [[ $RC -eq 0 ]] || { fail "exit $RC, want 0; log: $LOG"; return; }
  [[ "$OUT" == "hit=$want" ]] || { fail "GITHUB_OUTPUT '$OUT', want hit=$want"; return; }
  [[ -z "$("$REAL_GIT" -C "$REPO" remote)" ]] || { fail "remote left behind"; return; }
  [[ -z "$("$REAL_GIT" -C "$REPO" for-each-ref refs/remotes)" ]] || { fail "remote ref left behind"; return; }
  passed=$((passed + 1)); echo "PASS $case_name"
}

expect_error() {
  [[ $RC -eq 2 ]] || { fail "exit $RC, want 2; log: $LOG"; return; }
  [[ -z "$OUT" ]] || { fail "GITHUB_OUTPUT '$OUT', want empty"; return; }
  [[ "$LOG" != *"CI_HIT hit="* ]] || { fail "reported a hit result: $LOG"; return; }
  passed=$((passed + 1)); echo "PASS $case_name"
}

case_name=push-hit; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" 'tools/*' CI_PUSH_BEFORE="$BEFORE"; expect_hit true

case_name=push-miss; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" 'docs/*' CI_PUSH_BEFORE="$BEFORE"; expect_hit false

case_name=push-excluded; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" $'*\n!tools/a.txt' CI_PUSH_BEFORE="$BEFORE"; expect_hit false

case_name=paths-unset; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" __unset__ CI_PUSH_BEFORE="$BEFORE"; expect_error

case_name=new-branch-empty-paths; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" '' CI_PUSH_BEFORE=0000000000000000000000000000000000000000; expect_error

case_name=push-new-branch; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" 'docs/*' CI_PUSH_BEFORE=0000000000000000000000000000000000000000; expect_hit true

case_name=pr-hit; new_repo "$case_name"; at_commit "$MERGE"
run_entry pull_request "$MERGE" 'tools/b.txt' CI_PR_HEAD="$PR_HEAD"; expect_hit true

case_name=pr-miss; new_repo "$case_name"; at_commit "$MERGE"
run_entry pull_request "$MERGE" 'tools/a.txt' CI_PR_HEAD="$PR_HEAD"; expect_hit false

case_name=pr-head-mismatch; new_repo "$case_name"; at_commit "$MERGE"
run_entry pull_request "$MERGE" 'tools/*' CI_PR_HEAD="$BEFORE"; expect_error

case_name=sha-mismatch; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$BEFORE" 'tools/*' CI_PUSH_BEFORE="$BEFORE"; expect_error

case_name=empty-whitelist; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" $'\n# comment\n' CI_PUSH_BEFORE="$BEFORE"; expect_error

case_name=exclusions-only; new_repo "$case_name"; at_commit "$AFTER"
run_entry push "$AFTER" '!tools/*' CI_PUSH_BEFORE="$BEFORE"; expect_error

# CI_CHANGED_PATHS_FILE receives the NUL-separated changed paths whenever a base exists.
expect_paths() {
  local want="$1" file="$2"
  [[ $RC -eq 0 ]] || { fail "exit $RC, want 0; log: $LOG"; return; }
  [[ -f "$file" ]] || { fail "no changed-paths file"; return; }
  [[ "$(tail -c 1 "$file" | od -An -tx1 | tr -d ' \n')" == 00 ]] || { fail "changed paths are not NUL-terminated"; return; }
  local got; got="$(tr '\0' '\n' < "$file")"
  [[ "$got" == "$want" ]] || { fail "changed paths '$got', want '$want'"; return; }
  passed=$((passed + 1)); echo "PASS $case_name"
}

case_name=push-paths; new_repo "$case_name"; at_commit "$AFTER"; out="$WORK/paths-$case_name"
run_entry push "$AFTER" 'docs/*' CI_PUSH_BEFORE="$BEFORE" CI_CHANGED_PATHS_FILE="$out"; expect_paths tools/a.txt "$out"

case_name=pr-paths; new_repo "$case_name"; at_commit "$MERGE"; out="$WORK/paths-$case_name"
run_entry pull_request "$MERGE" 'tools/*' CI_PR_HEAD="$PR_HEAD" CI_CHANGED_PATHS_FILE="$out"; expect_paths tools/b.txt "$out"

case_name=new-branch-no-paths; new_repo "$case_name"; at_commit "$AFTER"; out="$WORK/paths-$case_name"
printf 'stale\0' > "$out"
run_entry push "$AFTER" 'docs/*' CI_PUSH_BEFORE=0000000000000000000000000000000000000000 CI_CHANGED_PATHS_FILE="$out"
if [[ $RC -ne 0 ]]; then fail "exit $RC, want 0; log: $LOG"
elif [[ -e "$out" ]]; then fail "changed-paths file left without a base"
else passed=$((passed + 1)); echo "PASS $case_name"; fi

for step in remote-list remote-remove ref-list ref-delete; do
  for polarity in hit miss; do
    case_name="cleanup-$step-$polarity"; new_repo "$case_name"; at_commit "$AFTER"
    make_wrapper "$case_name" "$step"
    paths='tools/*'; [[ $polarity == miss ]] && paths='docs/*'
    RUN_PATH="$WRAPPER_PATH" run_entry push "$AFTER" "$paths" CI_PUSH_BEFORE="$BEFORE"
    expect_error
  done
done

echo "CI_ENTRY_TEST passed=$passed failed=$failures"
[[ $failures -eq 0 ]]
