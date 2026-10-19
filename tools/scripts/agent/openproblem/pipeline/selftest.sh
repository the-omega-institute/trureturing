#!/bin/bash
# Hermetic contracts for the pipeline entry points.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd -P)
tool=${1:---selftest}
t=$(mktemp -d "${TMPDIR:-/tmp}/op-pipeline-test.XXXXXX") || exit 16
trap 'rm -rf "$t"' EXIT
mkdir -p "$t/repo/tools/scripts/agent/openproblem/pipeline" "$t/repo/tools/scripts/agent/seat" "$t/bin" "$t/scratch/briefs" "$t/scratch/preset" "$t/state/spool" "$t/state/running" "$t/state/joblogs" "$t/tree with space" "$t/sshx"
cp "$HERE/"*.sh "$t/repo/tools/scripts/agent/openproblem/pipeline/"
mkdir -p "$t/repo/tools/scripts/agent/openproblem/briefgen"
cp "$HERE/../briefgen/common.py" "$t/repo/tools/scripts/agent/openproblem/briefgen/"
export OP_TEST_ROOT="$t" OP_SCRATCH="$t/scratch" OP_STATE="$t/state" SSHX_HOME="$t/sshx"
export OP_POLL_SECONDS=0 OP_GATE_ROUNDS=2 OP_LOCK_ROUNDS=2 OP_RUNNER_POLL_SECONDS=0 OP_WATCH_MAX_SECONDS=0 OP_REFRESH_LOCK_ROUNDS=2
export OP_NAME_PREFIX=test- OP_WAIT_SINCE=$(date +%s) OP_MAX_SEATS=16
unset DWF_WAIT_SINCE DOTNET_ROOT DOTNET_HOST_PATH SCRIBE_DOTNET OP_PENDING OP_LANES OP_WORKTREE_PATTERN OP_REVIEW_PREPARE OP_SEARCH_SELECTION OP_SEARCH_EXCLUSIONS OP_GPTPRO_QUEUE
export PATH="$t/bin:$PATH"
cat > "$t/bin/ps" <<'STUB'
#!/bin/bash
if [ "${1:-}" = -o ]; then
  case "${4:-}" in 60) echo /usr/bin/python3;; 61) echo /usr/bin/node;; 62) echo /bin/bash;; *) echo init;; esac
  exit 0
fi
if [ -f "$OP_TEST_ROOT/ps-fail" ]; then exit 1; fi
if [ -f "$OP_TEST_ROOT/ps-wait" ]; then
  n=0; [ ! -f "$OP_TEST_ROOT/ps-count" ] || read -r n < "$OP_TEST_ROOT/ps-count"
  n=$((n+1)); echo "$n" > "$OP_TEST_ROOT/ps-count"
  if [ "$n" -eq 1 ]; then echo '30 1 bash /stub/run-codex-worker.sh --flight-id aaaaaaaaaaaaaaaaaaaaaaaa --work-target /other'; exit 0; fi
fi
if [ -s "$OP_TEST_ROOT/ps-rows" ]; then cat "$OP_TEST_ROOT/ps-rows"; else echo '1 0 init'; fi
STUB
cat > "$t/bin/git" <<'STUB'
#!/bin/bash
case " $* " in
  *' worktree list --porcelain '*) printf 'worktree %s/repo\nHEAD %040d\nbranch refs/heads/dev\n' "$OP_TEST_ROOT" 0;;
  *' rev-parse --is-bare-repository '*) echo false;;
  *' rev-parse --show-toplevel '*) echo "$OP_TEST_ROOT/repo";;
  *' rev-list --count '*) echo "${OP_TEST_AHEAD:-0}";;
  *' status --porcelain '*) [ ! -f "$OP_TEST_ROOT/dirty" ] || echo ' M D5/Test.lean';;
  *' diff --quiet '*) [ ! -f "$OP_TEST_ROOT/dirty" ];;
  *' merge-base --is-ancestor '*) exit "${OP_TEST_ANCESTOR_RC:-0}";;
  *' merge '*) echo "$*" >> "$OP_TEST_ROOT/merge-calls"; exit 0;;
  *' show '*) exit 1;;
  *' fetch '*) exit 0;;
  *' rev-parse --short '*) echo 123abcd;;
  *) echo "unexpected git: $*" >&2; exit 98;;
esac
STUB
cat > "$t/bin/make" <<'STUB'
#!/bin/bash
printf '%s\n' "$*" >> "$OP_TEST_ROOT/make-calls"
if [ "${OP_TEST_MAKE_RC:-0}" -ne 0 ]; then exit "$OP_TEST_MAKE_RC"; fi
if [ "${OP_TEST_CACHE_REFRESH:-0}" = 1 ] && [ "${3:-}" = lean-cache-ensure ]; then
  [ ! -e "$2/.lake" ] || exit 95
  mkdir -p "$2/.lake/build" || exit 16
  printf 'seeded\n' > "$2/.lake/build/content" || exit 16
fi
for arg in "$@"; do case "$arg" in DEST=*) mkdir -p "${arg#DEST=}";; esac; done
exit 0
STUB
for cmd in pgrep top lsof; do
  cat > "$t/bin/$cmd" <<'STUB'
#!/bin/bash
printf '%s\n' "$0 $*" >> "$OP_TEST_ROOT/forbidden-calls"
exit 97
STUB
done
cat > "$t/bin/sleep" <<'STUB'
#!/bin/bash
exit 0
STUB
cat > "$t/bin/kill" <<'STUB'
#!/bin/bash
echo "kill $*" >> "$OP_TEST_ROOT/forbidden-calls"
exit 97
STUB
cat > "$t/bin/gh" <<'STUB'
#!/bin/bash
exit 97
STUB
cat > "$t/repo/tools/scripts/agent/seat/dispatch.sh" <<'STUB'
#!/bin/bash
printf '%s\n' "$7" > "$OP_TEST_ROOT/dispatched-cap"
cat "$3" > "$OP_TEST_ROOT/dispatched-brief"
mkdir -p "$SSHX_HOME/$1/attempt-1"
printf '{}\n' > "$SSHX_HOME/$1/attempt-1/result.json"
if [ "${OP_TEST_LEFTOVERS:-0}" = 1 ]; then
  printf '60 1 python3 %s/%s/attempt-1/task.py\n61 1 node codex %s/%s/attempt-1/task\n62 1 bash dispatch %s/%s/attempt-1/task\n' "$SSHX_HOME" "$1" "$SSHX_HOME" "$1" "$SSHX_HOME" "$1" > "$OP_TEST_ROOT/ps-rows"
fi
echo "RUNNER_EXIT=${OP_TEST_DISPATCH_RC:-0}"
exit 0
STUB
kill() { printf '%s\n' "$*" >> "$OP_TEST_ROOT/kill-calls"; }
export -f kill
chmod +x "$t/bin/"* "$t/repo/tools/scripts/agent/seat/dispatch.sh"
R="$t/repo/tools/scripts/agent/openproblem/pipeline"
printf 'brief\n' > "$t/brief"
printf 'flight=__FLIGHT__\n' > "$OP_SCRATCH/briefs/process-safety-block.md"
printf '16\n' > "$OP_SCRATCH/max-seats"
fails=0
check() {
  local label=$1; shift
  if "$@"; then echo "ok $label"; else echo "FAIL $label"; fails=$((fails+1)); fi
}
run() { bash "$R/$tool.sh" "$@" > "$t/out" 2>&1; }
contains() { grep -q -- "$1" "$t/out"; }
seat() { run test-probe-one "$t/brief" "$t/tree with space" thinking 0; }
seat_tests() {
  echo "DONE $t/result with space.json" > "$OP_SCRATCH/preset/test-probe-one"
  echo '{}' > "$t/result with space.json"
  seat; check 'DONE preset preserves result path' contains "^$t/result with space.json$"
  check 'DONE preset consumed' test ! -e "$OP_SCRATCH/preset/test-probe-one"
  mkdir -p "$SSHX_HOME/aaaaaaaaaaaaaaaaaaaaaaaa/attempt-2" "$SSHX_HOME/aaaaaaaaaaaaaaaaaaaaaaaa/attempt-10"
  echo '{}' > "$SSHX_HOME/aaaaaaaaaaaaaaaaaaaaaaaa/attempt-2/result.json"
  echo '{}' > "$SSHX_HOME/aaaaaaaaaaaaaaaaaaaaaaaa/attempt-10/result.json"
  echo 'WAIT aaaaaaaaaaaaaaaaaaaaaaaa' > "$OP_SCRATCH/preset/test-probe-one"
  : > "$t/ps-wait"
  seat; check 'WAIT preset waits and selects numeric latest attempt' contains '/attempt-10/result.json$'
  check 'WAIT preset requires consecutive absent listings' test "$(cat "$t/ps-count")" -ge 4
  rm -f "$t/ps-wait" "$t/ps-count"
  seat; check 'seat dispatch succeeds' contains 'DISPATCH_EXIT=0'
  check 'cap forwarded to dispatcher' test "$(cat "$t/dispatched-cap")" = 16
  check 'safety block substitutes flight' grep -Eq '^flight=[0-9a-f]{24}$' "$t/dispatched-brief"
  OP_TEST_DISPATCH_RC=7 seat; rc=$?; check 'runner sentinel failure propagated' test "$rc" -eq 7
  check 'dispatch final line is terminal status' test "$(tail -1 "$t/out")" = DISPATCH_EXIT=7
  OP_TEST_LEFTOVERS=1 seat; rc=$?; check 'finished flight reaping completes' test "$rc" -eq 0
  check 'flight Python child reaped' grep -qx 60 "$t/kill-calls"
  check 'codex and dispatch executables never reaped' test "$(wc -l < "$t/kill-calls" | tr -d ' ')" -eq 1
  : > "$t/ps-rows"
  printf '20 1 bash /stub/run-codex-worker.sh --flight-id bbbbbbbbbbbbbbbbbbbbbbbb --work-target %s\n' "$t/tree with space" > "$t/ps-rows"
  seat; rc=$?; check 'busy worktree blocks' test "$rc" -eq 15
  check 'busy reason named' contains 'worktree-busy'
  echo '20 1 bash /stub/run-codex-worker.sh --flight-id bbbbbbbbbbbbbbbbbbbbbbbb --work-target /other' > "$t/ps-rows"
  echo 1 > "$OP_SCRATCH/max-seats"
  seat; rc=$?; check 'seat cap blocks' test "$rc" -eq 15
  check 'cap reason named' contains 'seat-cap'
  echo 16 > "$OP_SCRATCH/max-seats"; : > "$t/ps-rows"
  mkdir -p "$OP_SCRATCH/waiters"
  printf '{"name":"test-review-one","flight":"cccccccccccccccccccccccc","worktree":"/review","pid":40,"since":0}\n' > "$OP_SCRATCH/waiters/test-review-one.json"
  echo '40 1 bash /stub/seat-wait.sh test-review-one /brief /review review' > "$t/ps-rows"
  seat; rc=$?; check 'priority 2 yields to priority 0' test "$rc" -eq 15
  run test-review-two "$t/brief" "$t/tree with space" review; rc=$?; check 'priority 0 completes dispatch' test "$rc" -eq 0
  check 'priority 0 passes before priority 2' contains 'LOCKED_GATE_PASS'
  OP_WAIT_SINCE=1 seat; check 'aged priority 2 passes' contains 'LOCKED_GATE_PASS'
  printf '20 1 bash /stub/run-codex-worker.sh --flight-id bbbbbbbbbbbbbbbbbbbbbbbb --work-target /review\n40 1 bash /stub/seat-wait.sh test-review-one /brief /review review\n' > "$t/ps-rows"
  seat; check 'busy higher priority waiter does not block' contains 'LOCKED_GATE_PASS'
  : > "$t/ps-rows"; : > "$t/ps-fail"
  seat; rc=$?; check 'failed process listing fails closed' test "$rc" -eq 16
  rm "$t/ps-fail"
  run; rc=$?; check 'missing arguments named' test "$rc" -eq 10
  check 'usage diagnostic' contains 'USAGE'
  OP_SCRATCH= run a "$t/brief" "$t/tree with space" thinking; rc=$?; check 'missing scratch rejected' test "$rc" -eq 11
  check 'no load or destructive process probes' test ! -e "$t/forbidden-calls"
}
supervisor_tests() {
  printf 'printf "job-output\\n"; : > "$OP_STATE/spool/STOP"; exit 7\n' > "$OP_STATE/spool/one.job"
  echo 'exit 99' > "$OP_STATE/spool/ignored.job.tmp"
  run; rc=$?; check 'supervisor drains after STOP' test "$rc" -eq 0
  check 'job log ends with real exit sentinel' test "$(tail -1 "$OP_STATE/joblogs/one.log")" = JOB_EXIT=7
  check 'job moved to running' test -f "$OP_STATE/running/one.job"
  check '.tmp ignored' test ! -e "$OP_STATE/joblogs/ignored.log"
  check 'supervisor end sentinel' contains 'SUPERVISOR_END'
  check 'STOP consumed' test ! -e "$OP_STATE/spool/STOP"
}
case "$tool" in
  seat-wait) seat_tests;;
  supervisor) supervisor_tests;;
  --selftest|common|selftest)
    for name in supervisor seat-wait watch-jobs sweep-ghost-flights refresh-if-stale prep-lane-tree probe-queue resume-after-restart migrate-chain gptpro-search gptpro-queue; do
      bash "$HERE/$name.sh" --selftest || fails=$((fails+1))
    done;;
  watch-jobs)
    printf 'JOB_EXIT=4\n' > "$OP_STATE/joblogs/one.log"
    printf 'JOB_EXIT=0\nmore output\n' > "$OP_STATE/joblogs/not-done.log"
    run; rc=$?; check 'unseen completion returns' test "$rc" -eq 0
    check 'unseen completion named' contains '^== one$'
    run; check 'seen completion not repeated' contains WATCH_TIMEOUT
    check 'seen list has one entry' test "$(wc -l < "$OP_STATE/jobs-seen.txt" | tr -d ' ')" -eq 1
    check 'nonterminal sentinel ignored' test "$(grep -c not-done "$OP_STATE/jobs-seen.txt")" -eq 0;;
  sweep-ghost-flights)
    printf 'one aaaaaaaaaaaaaaaaaaaaaaaa\ntwo bbbbbbbbbbbbbbbbbbbbbbbb\nthree cccccccccccccccccccccccc\n' > "$OP_SCRATCH/flights.txt"
    mkdir -p "$SSHX_HOME/aaaaaaaaaaaaaaaaaaaaaaaa" "$SSHX_HOME/bbbbbbbbbbbbbbbbbbbbbbbb"
    echo '20 1 bash /stub/run-codex-worker.sh --flight-id bbbbbbbbbbbbbbbbbbbbbbbb --work-target /other' > "$t/ps-rows"
    run; rc=$?; check 'ghost sweep succeeds' test "$rc" -eq 0
    check 'finished flight tombstoned' grep -q '^one $' "$OP_SCRATCH/flights.txt"
    check 'live flight retained' test "$(grep -c '^two $' "$OP_SCRATCH/flights.txt")" -eq 0
    check 'unstarted flight retained' test "$(grep -c '^three $' "$OP_SCRATCH/flights.txt")" -eq 0
    : > "$t/ps-fail"; run; rc=$?; check 'failed ps cannot tombstone' test "$rc" -eq 16;;
  refresh-if-stale)
    run "$t/tree with space"; rc=$?; check 'unstamped main skipped' test "$rc" -eq 0
    check 'unstamped reason' contains main-not-stamped
    check 'unstamped main does not ensure cache' test ! -e "$t/make-calls"
    mkdir -p "$t/repo/.lake/build"
    printf '%040d 2000-01-01T00:00:00Z\n' 0 > "$t/repo/.lake/build/.main-built-at"
    mkdir -p "$t/tree with space/.lake/build" "$t/tree with space/.lake/packages"
    touch "$t/tree with space/.lake/build/old" "$t/tree with space/.lake/packages/old"
    refresh_tree=$(cd "$t/tree with space" && pwd -P)
    export OP_TEST_CACHE_REFRESH=1
    run "$t/tree with space"; rc=$?; check 'stale clean tree refreshed' test "$rc" -eq 0
    check 'cache ensure called for lane' grep -Fxq -- "-C $refresh_tree lean-cache-ensure" "$t/make-calls"
    check 'cache reseeded by make stub' grep -qx seeded "$t/tree with space/.lake/build/content"
    check 'old build removed' test ! -e "$t/tree with space/.lake/build/old"
    check 'old packages removed' test ! -e "$t/tree with space/.lake/packages/old"
    check 'clone stamp preserved' cmp -s "$t/repo/.lake/build/.main-built-at" "$t/tree with space/.lake/build/.main-cloned-at"
    check 'refresh receipt preserved' grep -Fxq -- "CACHE_REFRESH done tree=$refresh_tree main_sha=0000000000000000000000000000000000000000 rc=0" "$t/out"
    run "$t/tree with space"; check 'recent clone skipped' contains tree-cloned-recently
    : > "$t/dirty"; run "$t/tree with space"; check 'lane changes preserved' contains lane-work-present
    rm "$t/dirty"
    printf '20 1 bash /stub/run-codex-worker.sh --flight-id bbbbbbbbbbbbbbbbbbbbbbbb --work-target %s\n' "$t/tree with space" > "$t/ps-rows"
    run "$t/tree with space"; check 'in-flight tree preserved' contains seat-in-flight
    : > "$t/ps-rows"
    check 'skipped trees do not ensure cache' test "$(wc -l < "$t/make-calls" | tr -d ' ')" -eq 1
    rm "$t/tree with space/.lake/build/.main-cloned-at"
    OP_TEST_MAKE_RC=7 run "$t/tree with space"; rc=$?; check 'cache ensure failure rejected' test "$rc" -eq 16
    check 'cache ensure failure named' contains CACHE_REFRESH_FAILED
    check 'failed ensure leaves no clone stamp' test ! -e "$t/tree with space/.lake/build/.main-cloned-at"
    check 'refresh lock released on failure' test ! -d "$OP_STATE/main-lean.lock"
    mkdir "$OP_STATE/main-lean.lock"
    run "$t/tree with space"; rc=$?; check 'held refresh lock fails closed' test "$rc" -eq 15;;
  prep-lane-tree)
    run "$t/tree with space"; rc=$?; check 'prep uses canonical cache entry' test "$rc" -eq 0
    check 'cache ensure called' grep -q lean-cache-ensure "$t/make-calls"
    OP_TEST_ANCESTOR_RC=1 run "$t/tree with space"; rc=$?; check 'fast-forward lane succeeds' test "$rc" -eq 0
    check 'fast-forward flag' grep -q -- --ff-only "$t/merge-calls"
    : > "$t/dirty"
    OP_TEST_ANCESTOR_RC=1 OP_TEST_AHEAD=1 run "$t/tree with space"; rc=$?; check 'dirty divergent lane refused' test "$rc" -eq 6
    OP_TEST_MAKE_RC=7 run "$t/tree with space"; rc=$?; check 'cache failure propagated' test "$rc" -eq 7;;
  probe-queue)
    export OP_PENDING="$t/pending" OP_LANES='one:one two:-' OP_WORKTREE_PATTERN='../tree-{suffix}'
    mkdir "$OP_PENDING"
    printf brief > "$OP_SCRATCH/briefs/probe-one-r1.md"
    run; rc=$?; check 'probe queue dispatches and joins' test "$rc" -eq 0
    check 'queue terminal sentinel' contains PROBE_QUEUE=0
    check 'waiter completed before return' grep -q DISPATCH_EXIT=0 "$OP_SCRATCH/logs/probe-one-r1.log"
    check 'dispatched state written' grep -qx one "$OP_SCRATCH/pq-dispatched.txt"
    run; check 'queue safely reruns' contains 'already dispatched one'
    OP_PENDING= run; rc=$?; check 'pending input required' test "$rc" -eq 11;;
  resume-after-restart)
    echo 'echo done' > "$OP_STATE/running/complete.job"
    echo JOB_EXIT=0 > "$OP_STATE/joblogs/complete.log"
    echo 'bash /runtime/seat-wait.sh test-review-one brief tree review' > "$OP_STATE/running/unfinished.job"
    mkdir -p "$SSHX_HOME/aaaaaaaaaaaaaaaaaaaaaaaa/attempt-3"
    echo '{}' > "$SSHX_HOME/aaaaaaaaaaaaaaaaaaaaaaaa/attempt-3/result.json"
    printf 'test-review-one aaaaaaaaaaaaaaaaaaaaaaaa\n' > "$OP_SCRATCH/flights.txt"
    run --dry-run; rc=$?; check 'resume dry-run succeeds' test "$rc" -eq 0
    check 'dry-run leaves job in running' test -f "$OP_STATE/running/unfinished.job"
    check 'dry-run writes no preset' test ! -f "$OP_SCRATCH/preset/test-review-one"
    run; rc=$?; check 'resume respools unfinished job' test "$rc" -eq 0
    check 'completed job retained' test -f "$OP_STATE/running/complete.job"
    check 'unfinished job spooled' test -f "$OP_STATE/spool/unfinished.job"
    check 'recovery picks latest result' grep -q '^DONE .*/attempt-3/result.json$' "$OP_SCRATCH/preset/test-review-one"
    echo 'echo must-not-replay' > "$OP_STATE/running/duplicate.job"
    echo 'echo already-queued' > "$OP_STATE/spool/duplicate.job"
    run; rc=$?; check 'resume refuses duplicate spool entry' test "$rc" -eq 14;;
  migrate-chain)
    export JOB=chain CMD='echo resumed'
    echo '50 1 bash /runtime/chain-one.sh' > "$t/ps-rows"
    run --dry-run chain-one.sh review-one; rc=$?; check 'migration dry-run identifies chain' test "$rc" -eq 0
    check 'dry-run never signals or spools' test ! -f "$OP_STATE/spool/chain.job"
    echo '50 1 bash /runtime/dispatch.sh' > "$t/ps-rows"
    run --dry-run dispatch.sh review-one; rc=$?; check 'dispatch carrier protected' test "$rc" -eq 16
    echo '50 1 node /runtime/codex exec' > "$t/ps-rows"
    run --dry-run codex review-one; rc=$?; check 'codex carrier protected' test "$rc" -eq 16
    echo '50 1 bash /runtime/chain-one.sh' > "$t/ps-rows"
    run chain-one.sh review-one; rc=$?; check 'migration spools after chain-only signal' test "$rc" -eq 0
    check 'only chain shell receives TERM' grep -qx -- '-TERM 50' "$t/kill-calls"
    check 'migrated command preserved' grep -qx 'echo resumed' "$OP_STATE/spool/chain.job";;
  gptpro-search|gptpro-queue)
    mkdir -p "$t/repo/tools/scripts/agent/nyx"
    cat > "$t/repo/tools/scripts/agent/nyx/nyx.py" <<'STUB'
import os, pathlib, sys
root = pathlib.Path(os.environ['OP_TEST_ROOT'])
if not (pathlib.Path(os.environ['OP_STATE']) / 'gptpro.lock').is_dir():
    sys.exit(96)
with (root / 'asks').open('a') as stream:
    stream.write(' '.join(sys.argv[1:]) + '\n')
if (root / 'nyx-fail').exists():
    sys.exit(1)
pathlib.Path(sys.argv[3]).write_text('answer')
print('NYX_RESULT status=complete')
STUB
    cat > "$t/repo/tools/scripts/agent/openproblem/render-search-brief.sh" <<'STUB'
#!/bin/bash
printf 'search %s %s\n' "$3" "$4" > "$2"
STUB
    printf selection > "$OP_SCRATCH/briefs/search-selection-block.md"
    printf exclusions > "$OP_SCRATCH/briefs/search-exclusions-compact.md"
    if [ "$tool" = gptpro-search ]; then
      run one quick 2601; rc=$?; check 'search asks canonical broker under lock' test "$rc" -eq 0
      check 'search complete sentinel' contains NYX_OK
      check 'selection included' grep -q selection "$OP_SCRATCH/briefs/gptpro-search-one.md"
      : > "$t/nyx-fail"; run two deep; rc=$?; check 'broker failure propagated' test "$rc" -eq 1
    else
      printf 'one quality 1 12\ntwo architecture 2 13\n' > "$OP_SCRATCH/gptpro-queue.txt"
      printf review > "$OP_SCRATCH/briefs/review-one-quality.md"
      printf review > "$OP_SCRATCH/briefs/review-two-architecture.md"
      run; rc=$?; check 'review queue drains serially' test "$rc" -eq 0
      check 'two broker calls' test "$(wc -l < "$t/asks" | tr -d ' ')" -eq 2
      check 'queue-empty sentinel' contains QUEUE_EMPTY
      printf 'one quality 1 12\n' > "$OP_SCRATCH/gptpro-queue.txt"
      : > "$t/nyx-fail"; run; rc=$?; check 'review failure propagated' test "$rc" -eq 1
      check 'failed review remains queued' test -s "$OP_SCRATCH/gptpro-queue.txt"
    fi
    mkdir "$OP_STATE/gptpro.lock"
    if [ "$tool" = gptpro-search ]; then run three deep; else run; fi
    rc=$?; check 'shared request lock blocks' test "$rc" -eq 15
    rmdir "$OP_STATE/gptpro.lock"
    echo '22 1 python3 /runtime/nyx.py ask /brief /out' > "$t/ps-rows"
    if [ "$tool" = gptpro-search ]; then run four deep; else run; fi
    rc=$?; check 'external broker request blocks' test "$rc" -eq 15
    check 'broker lock released on failure' test ! -d "$OP_STATE/gptpro.lock";;
  *) echo "FAIL unknown selftest $tool"; fails=$((fails+1));;
esac
echo "SELFTEST_FAILS=$fails"
[ "$fails" -eq 0 ]
