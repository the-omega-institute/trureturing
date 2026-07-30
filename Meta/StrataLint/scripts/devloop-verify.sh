#!/usr/bin/env bash
# devloop-verify — the repository's local iteration gate for the fkst devloop,
# wrapped in the typed verdict contract (local_iteration_result v1). The
# devloop treats an untyped nonzero exit as UNKNOWN, which dead-ends the
# base-vs-candidate attribution rerun and makes a single red terminal; the
# full-line marker below is load-bearing, not cosmetic. Emit it exactly once,
# as the final stdout line, and pass the inner exit code through.
#
#   usage: devloop-verify.sh [command arg...]   (default: make preflight)
#
# Verdict mapping: 0 = PASS; 126/127 (tool missing or not executable) and
# >=128 (killed by a signal) = UNKNOWN infrastructure; any other nonzero is a
# deterministic SEMANTIC_FAIL — the devloop's base-side counterfactual replay
# of this same command owns base-red vs candidate-red attribution.
set -uo pipefail

if [[ $# -gt 0 ]]; then
  "$@"
else
  make preflight
fi
status=$?

if [[ "$status" -eq 0 ]]; then
  verdict=PASS
elif [[ "$status" -eq 126 || "$status" -eq 127 || "$status" -ge 128 ]]; then
  verdict=UNKNOWN
else
  verdict=SEMANTIC_FAIL
fi

printf 'FKST_LOCAL_ITERATION_RESULT:v1:%s\n' "$verdict"
exit "$status"
