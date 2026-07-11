#!/usr/bin/env bash
# Exit-semantics separated baseline admission (zero-trust gate).
#   0 = admitted: full content rules ran and passed, no protected-surface change.
#   3 = SL-022 protected-surface change: annotated scaffold path; candidate lake
#       build below is the blocking content floor until component C replaces it.
#   * = content violation or infrastructure failure: fail closed.
set -uo pipefail
set +e
dotnet "$JUDGE_ROOT/Meta/StrataLint/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll" check --protected-base "$DEV_BASELINE_SHA"
rc=$?
set -e
if [[ $rc -eq 0 ]]; then
  printf '%s\n' "### Admission: content fully validated, no protected-surface change" >> "$GITHUB_STEP_SUMMARY"
  exit 0
elif [[ $rc -eq 3 ]]; then
  echo "::warning title=SL-022 protected-surface change::Scaffold path: lake build floor enforced; machine meta-gate arrives with component C."
  printf '%s\n' "### SL-022 protected-surface change (bootstrap scaffold path)" >> "$GITHUB_STEP_SUMMARY"
  "$HOME/.elan/bin/lake" build
  exit 0
else
  exit "$rc"
fi
