#!/usr/bin/env bash
# Restore or build the measured high-memory modules sequentially through Lake.
set -euo pipefail
[[ $# == 1 ]] || { echo 'usage: oom-guard.sh <lane-dir>' >&2; exit 2; }
LANE="$1"
[[ -d "$LANE" ]] || { echo 'OOM_GUARD status=failed reason=no-such-lane' >&2; exit 2; }
for module in \
  D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree \
  D5/S0/Certificates/Games/VersionBOddCountUnderdetermines; do
  [[ -f "$LANE/$module.lean" ]] || continue
  make -C "$LANE" lean "LEAN_TARGETS=$module.lean" || { echo 'OOM_GUARD status=failed' >&2; exit 1; }
done
echo 'OOM_GUARD status=complete'
