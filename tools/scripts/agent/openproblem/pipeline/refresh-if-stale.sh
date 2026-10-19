#!/bin/bash
# Refresh an idle, clean tree's build from the stamped main checkout.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest refresh-if-stale; exit $?; }
[ "$#" -eq 1 ] || op_fail 10 USAGE 'refresh-if-stale.sh TREE'
op_init; op_main
[ -d "$1" ] || op_fail 11 INPUT_MISSING "$1"
T=$(cd "$1" && pwd -P)
lag=${REFRESH_LAG_SECONDS:-10800}; op_uint REFRESH_LAG_SECONDS "$lag"
lock=$OP_REFRESH_LOCK
rounds=${OP_REFRESH_LOCK_ROUNDS:-480}; op_uint OP_REFRESH_LOCK_ROUNDS "$rounds"
[ "$T" != "$OP_MAIN" ] || { echo "CACHE_REFRESH skip tree=$T reason=is-main"; exit 0; }
check_idle() {
  op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
  if op_process busy "$T"; then echo "CACHE_REFRESH skip tree=$T reason=seat-in-flight"; return 1; fi
  dirty=$(git -C "$T" status --porcelain -- D5) || op_fail 16 GIT_FAILED status
  git -C "$T" diff --quiet origin/dev...HEAD -- D5; diff_rc=$?
  [ "$diff_rc" -le 1 ] || op_fail 16 GIT_FAILED diff
  if [ -n "$dirty" ] || [ "$diff_rc" -eq 1 ]; then echo "CACHE_REFRESH skip tree=$T reason=lane-work-present"; return 1; fi
}
check_idle || exit 0
state=$(op_data stale "$OP_MAIN" "$T" "$lag") || exit $?
case "$state" in skip*) echo "CACHE_REFRESH $state tree=$T"; exit 0;; esac
mkdir -p "$(dirname "$lock")" || op_fail 16 IO_ERROR "$lock"
op_lock "$lock" "$rounds" || op_fail 15 LOCK_TIMEOUT "$lock"
cleanup() { rmdir "$lock"; }
trap cleanup EXIT
check_idle || exit 0
state=$(op_data stale "$OP_MAIN" "$T" "$lag") || exit $?
case "$state" in skip*) echo "CACHE_REFRESH $state tree=$T"; exit 0;; esac
read -r _ msha mtime <<< "$state"
rm -rf -- "$T/.lake" && make -C "$T" lean-cache-ensure || op_fail 16 CACHE_REFRESH_FAILED "$T"
printf '%s %s\n' "$msha" "$mtime" > "$T/.lake/build/.main-cloned-at" || op_fail 16 IO_ERROR stamp
echo "CACHE_REFRESH done tree=$T main_sha=$msha rc=0"
