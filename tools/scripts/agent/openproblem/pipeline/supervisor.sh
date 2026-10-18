#!/bin/bash
# Run spool/*.job in a persistent terminal and drain all children on STOP or signal.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest supervisor; exit $?; }
[ "$#" -eq 0 ] || op_fail 10 USAGE supervisor.sh
op_init; op_main
mkdir -p "$OP_STATE/spool" "$OP_STATE/running" "$OP_STATE/joblogs" || op_fail 16 IO_ERROR OP_STATE
stopping=0
trap 'stopping=1' INT TERM
# EXIT also covers an I/O failure after children have started.
trap 'wait' EXIT
printf 'SUPERVISOR_START pid=%s\n' "$$"
while [ "$stopping" -eq 0 ] && [ ! -e "$OP_STATE/spool/STOP" ]; do
  for f in "$OP_STATE/spool/"*.job; do
    [ -f "$f" ] || continue
    [ "$stopping" -eq 0 ] && [ ! -e "$OP_STATE/spool/STOP" ] || break
    n=${f##*/}; n=${n%.job}
    mv "$f" "$OP_STATE/running/$n.job" || op_fail 16 IO_ERROR "claim $n"
    # The parent owns and waits for every child before returning.
    (
      trap '' INT TERM
      cd "$OP_MAIN" && bash "$OP_STATE/running/$n.job"
      rc=$?
      printf '\nJOB_EXIT=%s\n' "$rc"
    ) > "$OP_STATE/joblogs/$n.log" 2>&1 &
    printf 'STARTED %s pid=%s\n' "$n" "$!"
  done
  sleep "$OP_POLL_SECONDS"
done
rm -f "$OP_STATE/spool/STOP"
echo SUPERVISOR_WAIT
wait
echo SUPERVISOR_END
