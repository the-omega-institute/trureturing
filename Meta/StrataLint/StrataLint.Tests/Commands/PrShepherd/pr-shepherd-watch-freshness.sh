#!/usr/bin/env bash
set -uo pipefail
export LC_ALL=C

REPOSITORY_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../../.." && pwd -P)"
SCRIPT_UNDER_TEST="$REPOSITORY_ROOT/Meta/StrataLint/scripts/pr-shepherd.sh"
root="$(mktemp -d -t pr-shepherd-watch-freshness.XXXXXX)" || exit 1
trap 'rm -rf "$root"' EXIT
checkout="$root/checkout"
remote="$root/origin.git"
mkdir -p "$root/bin" "$root/home" "$root/state" "$root/cache" \
  "$checkout/Meta/StrataLint/scripts"
script="$checkout/Meta/StrataLint/scripts/pr-shepherd.sh"
log="$root/pr-shepherd.log"
output="$root/output"
calls="$root/gh.calls"
marker="$root/script-updated"
root_marker="$root/reloaded-root"
command cp -R "$(dirname "$SCRIPT_UNDER_TEST")/." "$(dirname "$script")"
lease_implementation="$(command sed -n \
  '/^clear_watch_reclaim()/,/^watch_lease_belongs_to_current_process()/p' \
  "$SCRIPT_UNDER_TEST")"
command grep -q 'ln "$WATCH_LOCK_CANDIDATE" "$lock"' <<< "$lease_implementation" \
  || { printf 'new lease owner is not installed atomically\n' >&2; exit 1; }
command grep -q 'update-ref' <<< "$lease_implementation" \
  || { printf 'dead lease reclamation lacks a crash-recoverable CAS claim\n' >&2; exit 1; }
command grep -q 'repository="$PIDFILE.reclaim.git"' <<< "$lease_implementation" \
  || { printf 'reclaim CAS store is not scoped to the canonical state path\n' >&2; exit 1; }
! command grep -q 'ln .*lock.reclaim' <<< "$lease_implementation" \
  || { printf 'reclaim mutex can survive its dead claimant\n' >&2; exit 1; }
! command grep -q 'mkdir "$lock"' <<< "$lease_implementation" \
  || { printf 'lease initialization can leave an empty directory\n' >&2; exit 1; }
! command grep -q 'mv "$lock" "$stale"' <<< "$lease_implementation" \
  || { printf 'dead lease reclamation can rename a replacement lease\n' >&2; exit 1; }
cleanup_implementation="$(command sed -n \
  '/^cleanup_watch()/,/^watch()/p' "$SCRIPT_UNDER_TEST")"
! command grep -q 'rm -f "$PIDFILE.lock/owner"' <<< "$cleanup_implementation" \
  || { printf 'watch cleanup deletes the recoverable owner record\n' >&2; exit 1; }
! command grep -q 'rmdir "$PIDFILE.lock"' <<< "$cleanup_implementation" \
  || { printf 'watch cleanup dismantles the recoverable lease directory\n' >&2; exit 1; }
command git -C "$checkout" init --initial-branch=dev >/dev/null
command git -C "$checkout" config user.name "PR Watch Fixture"
command git -C "$checkout" config user.email "pr-watch@example.invalid"
command git -C "$checkout" add Meta/StrataLint/scripts
command git -C "$checkout" commit -m initial >/dev/null
command git init --bare "$remote" >/dev/null
command git -C "$checkout" remote add origin "$remote"
command git -C "$checkout" push -u origin dev >/dev/null 2>&1

cat > "$root/bin/ps" <<'SH'
#!/usr/bin/env bash
case "$*" in
  *lstart=*) printf 'Mon Aug  3 07:37:54 2026\n' ;;
  *) exit 2 ;;
esac
SH
cat > "$root/bin/gh" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$PR_WATCH_TEST_CALLS"
case "$*" in
  *rate_limit*) printf '500\n' ;;
  *statusCheckRollup*)
    if [[ ! -e "$PR_WATCH_TEST_MARKER" ]]; then
      printf '%s\n' \
        'printf "%s\n" "$ROOT" > "$PR_WATCH_TEST_ROOT_MARKER"' \
        >> "$PR_WATCH_TEST_SCRIPT"
      /usr/bin/git -C "$PR_WATCH_TEST_CHECKOUT" \
        add Meta/StrataLint/scripts/pr-shepherd.sh
      /usr/bin/git -C "$PR_WATCH_TEST_CHECKOUT" \
        commit -m cycle-2-replacement >/dev/null
      /usr/bin/git -C "$PR_WATCH_TEST_CHECKOUT" push origin dev >/dev/null 2>&1
      : > "$PR_WATCH_TEST_MARKER"
    fi
    ;;
  *autoMergeRequest*) printf '0\n' ;;
  *) exit 2 ;;
esac
SH
chmod +x "$root/bin/ps" "$root/bin/gh"

run_watch() {
  HOME="$root/home" \
  PATH="$root/bin:/usr/bin:/bin" \
  PR_SHEPHERD_LOG="$log" \
  PR_SHEPHERD_PID="$root/pr-watch.state" \
  PR_SHEPHERD_STATE="$root/state" \
  PR_SHEPHERD_CACHE="$root/cache" \
  PR_WATCH_TEST_CALLS="$calls" \
  PR_WATCH_TEST_CHECKOUT="$checkout" \
  PR_WATCH_TEST_MARKER="$marker" \
  PR_WATCH_TEST_ROOT_MARKER="$root_marker" \
  PR_WATCH_TEST_SCRIPT="$script" \
    /bin/bash "$script" watch "$@"
}

printf '\n# uncommitted helper must block immutable reload\n' \
  >> "$checkout/Meta/StrataLint/scripts/shepherd/pr-shepherd-actions.sh"
if run_watch 0 1 >"$root/untracked-helper-output" 2>&1; then
  printf 'watch sourced an untracked helper module\n' >&2
  exit 1
fi
command grep -q 'does not match tracked HEAD' "$log" \
  || { printf 'watch did not diagnose the untracked helper module\n' >&2; exit 1; }
rm -f "$root/pr-watch.state" "$root/pr-watch.state.lock"
command git -C "$checkout" restore \
  Meta/StrataLint/scripts/shepherd/pr-shepherd-actions.sh

printf '\n# uncommitted ledger helper must block immutable reload\n' \
  >> "$checkout/Meta/StrataLint/scripts/shepherd/pr-shepherd-ledger.sh"
if run_watch 0 1 >"$root/untracked-ledger-output" 2>&1; then
  printf 'watch sourced an untracked ledger helper module\n' >&2
  exit 1
fi
command grep -q 'does not match tracked HEAD' "$log" \
  || { printf 'watch did not diagnose the untracked ledger helper module\n' >&2; exit 1; }
rm -f "$root/pr-watch.state" "$root/pr-watch.state.lock"
command git -C "$checkout" restore \
  Meta/StrataLint/scripts/shepherd/pr-shepherd-ledger.sh

run_watch 0 2 >"$output" 2>&1 \
  || { command sed -n '1,120p' "$output" >&2; exit 1; }

blobs="$root/loaded-blobs"
command sed -n 's/.*loaded_script_blob=\([0-9a-f]\{40\}\).*/\1/p' "$log" > "$blobs"
blob_count="$(command wc -l < "$blobs" | command tr -d '[:space:]')"
first_blob="$(command sed -n '1p' "$blobs")"
second_blob="$(command sed -n '2p' "$blobs")"
[[ "$blob_count" -eq 2 ]] \
  || { printf 'expected two machine-checkable cycle blobs, got %s\n' "$blob_count" >&2; exit 1; }
[[ "$first_blob" != "$second_blob" ]] \
  || {
    printf 'cycle 2 reused the stale script blob %s\n' "$first_blob" >&2
    command sed -n '1,120p' "$calls" >&2
    command sed -n '1,120p' "$log" >&2
    exit 1
  }
command grep -q \
  "WATCH SCRIPT CHANGED previous_blob=$first_blob current_blob=$second_blob" \
  "$log" \
  || { printf 'watch did not report script convergence\n' >&2; exit 1; }
expected_root="$(cd "$checkout" && pwd -P)"
actual_root="$(command sed -n '1p' "$root_marker")"
[[ "$actual_root" == "$expected_root" ]] \
  || { printf 'reload changed repository root: expected=%s actual=%s\n' \
    "$expected_root" "${actual_root:-missing}" >&2; exit 1; }

rm -f "$root/pr-watch.state.lock"
printf '4242' > "$root/pr-watch.state"
if run_watch 0 1 >"$root/legacy-output" 2>&1; then
  printf 'watch overwrote state without a verified ownership lease\n' >&2
  exit 1
fi
[[ "$(<"$root/pr-watch.state")" == "4242" ]] \
  || { printf 'watch mutated unleased legacy state\n' >&2; exit 1; }
command grep -q 'state exists without ownership lease' "$log" \
  || { printf 'watch did not diagnose unleased state\n' >&2; exit 1; }

rm -f "$root/pr-watch.state"
printf 'partial-owner\n' > "$root/pr-watch.state.lock"
if run_watch 0 1 >"$root/partial-owner-output" 2>&1; then
  printf 'watch reclaimed an unverifiable ownership lease\n' >&2
  exit 1
fi
[[ "$(<"$root/pr-watch.state.lock")" == "partial-owner" ]] \
  || { printf 'watch mutated an unverifiable ownership lease\n' >&2; exit 1; }
command grep -q 'ownership identity is unverifiable' "$log" \
  || {
    printf 'watch did not diagnose unverifiable ownership\n' >&2
    command tail -20 "$log" >&2
    exit 1
  }

rm -f "$root/pr-watch.state" "$root/pr-watch.state.lock"
corrupt_blob="$(command git -C "$checkout" hash-object "$script")"
cat > "$root/corrupt-owner-runner" <<'SH'
#!/usr/bin/env bash
printf 'pid=%s\nprocess_start=Mon Aug  3 07:37:54 2026\n' "$$" \
  > "$PR_SHEPHERD_PID.lock"
exec /bin/bash "$PR_WATCH_TEST_SCRIPT" watch 0 1
SH
chmod +x "$root/corrupt-owner-runner"
if HOME="$root/home" \
  PATH="$root/bin:/usr/bin:/bin" \
  PR_SHEPHERD_LOG="$log" \
  PR_SHEPHERD_PID="$root/pr-watch.state" \
  PR_SHEPHERD_STATE="$root/state" \
  PR_SHEPHERD_CACHE="$root/cache" \
  PR_WATCH_TEST_CALLS="$calls" \
  PR_WATCH_TEST_CHECKOUT="$checkout" \
  PR_WATCH_TEST_MARKER="$marker" \
  PR_WATCH_TEST_ROOT_MARKER="$root_marker" \
  PR_WATCH_TEST_SCRIPT="$script" \
  PR_SHEPHERD_CANONICAL_SCRIPT="$script" \
  PR_SHEPHERD_WATCH_LOADED_BLOB="$corrupt_blob" \
  PR_SHEPHERD_WATCH_PROCESS_START='Mon Aug  3 07:37:54 2026' \
  PR_SHEPHERD_WATCH_CYCLE=1 \
    /bin/bash "$root/corrupt-owner-runner" \
      >"$root/corrupt-owner-output" 2>&1; then
  printf 'watch accepted a post-exec lease without the strict owner schema\n' >&2
  exit 1
fi
command grep -q 'verified lease is absent' "$log" \
  || {
    printf 'watch did not diagnose the malformed post-exec lease\n' >&2
    command tail -20 "$log" >&2
    command sed -n '1,80p' "$root/corrupt-owner-output" >&2
    exit 1
  }

rm -f "$root/pr-watch.state" "$root/pr-watch.state.lock"
cat > "$root/pr-watch.state.lock" <<EOF
schema=pr-watch-owner-v1
pid=999999
process_start=Sun Aug  2 07:37:54 2026
canonical_script=$script
EOF
reclaim_repository="$root/pr-watch.state.reclaim.git"
reclaim_ref="refs/trureturing/pr-watch-reclaim"
command rm -rf "$reclaim_repository"
command mkdir "$reclaim_repository"
run_watch 0 1 >"$root/partial-reclaim-store-output" 2>&1 \
  || { command sed -n '1,120p' "$root/partial-reclaim-store-output" >&2; exit 1; }
[[ "$(command git -C "$reclaim_repository" rev-parse --is-bare-repository 2>/dev/null)" == "true" ]] \
  || { printf 'watch did not recover the partial reclaim store\n' >&2; exit 1; }
cat > "$root/pr-watch.state.lock" <<EOF
schema=pr-watch-owner-v1
pid=999997
process_start=Sun Aug  2 07:37:54 2026
canonical_script=$script
EOF
cat > "$root/dead-reclaimer" <<EOF
schema=pr-watch-owner-v1
pid=999998
process_start=Sun Aug  2 07:37:54 2026
canonical_script=$script
EOF
dead_reclaimer_blob="$(command git -C "$reclaim_repository" hash-object -w "$root/dead-reclaimer")"
command git -C "$reclaim_repository" update-ref "$reclaim_ref" "$dead_reclaimer_blob"
run_watch 0 1 >"$root/dead-reclaimer-output" 2>&1 \
  || { command sed -n '1,120p' "$root/dead-reclaimer-output" >&2; exit 1; }
! command git -C "$reclaim_repository" show-ref --verify --quiet "$reclaim_ref" \
  || { printf 'watch left the recovered reclaim claim active\n' >&2; exit 1; }

printf 'pr-shepherd watch freshness: 8 passed, 0 failed, 8 total\n'
