#!/usr/bin/env bash
set -euo pipefail

engineering_test_evidence="not-required"
if [[ "$SCOPE_RUN" == "true" ]]; then
  if [[ "$ENGINEERING_TEST_OUTCOME" != "success"
    || ! -f "$ENGINEERING_EXECUTION_RECEIPT"
    || "$(cat -- "$ENGINEERING_EXECUTION_RECEIPT" 2>/dev/null)" != "candidate-engineering-tests-v1" ]]; then
    printf 'candidate engineering execution evidence is absent or invalid (outcome=%s)\n' \
      "$ENGINEERING_TEST_OUTCOME" >&2
    exit 1
  fi
  engineering_test_evidence="verified"
fi

result="$SCOPE_RUN"
if [[ -z "$result" ]]; then
  result="unavailable"
fi
{
  printf '%s\n' '## Candidate engineering scope'
  printf '\n'
  printf -- '- Event: %s\n' "$SCOPE_EVENT"
  printf -- '- Run engineering: %s\n' "$result"
  printf -- '- Dev parent: %s\n' "$SCOPE_BASE"
  printf -- '- Changed paths: %s\n' "$SCOPE_CHANGED_COUNT"
  printf -- '- Trigger matches: %s\n' "$SCOPE_MATCHED_COUNT"
  printf -- '- Decision: %s\n' "$SCOPE_REASON"
  printf -- '- Engineering test execution: %s\n' "$engineering_test_evidence"
  printf -- '%s\n' '- Detail: see the ENGINEERING_SCOPE_CHANGED and ENGINEERING_SCOPE_MATCHED log lines of the scope step.'
} >> "$GITHUB_STEP_SUMMARY"
