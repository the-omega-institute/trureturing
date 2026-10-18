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
lock=${OP_REFRESH_LOCK:-$OP_STATE/main-lean.lock}
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
work=
cleanup() { [ -z "$work" ] || rm -rf "$work"; rmdir "$lock"; }
trap cleanup EXIT
check_idle || exit 0
state=$(op_data stale "$OP_MAIN" "$T" "$lag") || exit $?
case "$state" in skip*) echo "CACHE_REFRESH $state tree=$T"; exit 0;; esac
read -r _ msha mtime <<< "$state"
mkdir -p "$T/.lake" || op_fail 16 IO_ERROR .lake
work=$(mktemp -d "$T/.lake/build.refresh.XXXXXX") || op_fail 16 IO_ERROR refresh
# clonefile is a macOS capability; ordinary copies provide the same cache contents.
if [ "$(uname -s)" = Darwin ]; then
  cp -cR "$OP_MAIN/.lake/build" "$work/build" || op_fail 16 CACHE_COPY_FAILED clonefile
else
  cp -R "$OP_MAIN/.lake/build" "$work/build" || op_fail 16 CACHE_COPY_FAILED copy
fi
printf '%s %s\n' "$msha" "$mtime" > "$work/build/.main-cloned-at" || op_fail 16 IO_ERROR stamp
[ ! -d "$T/.lake/build" ] || mv "$T/.lake/build" "$work/old" || op_fail 16 IO_ERROR old-build
if ! mv "$work/build" "$T/.lake/build"; then
  [ ! -d "$work/old" ] || mv "$work/old" "$T/.lake/build"
  op_fail 16 CACHE_SWAP_FAILED "$T"
fi
echo "CACHE_REFRESH done tree=$T main_sha=$msha rc=0"
