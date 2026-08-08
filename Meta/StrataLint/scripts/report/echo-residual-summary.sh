#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
BASE="${1:-origin/dev}"
REPORT_SCRIPT="$ROOT/Meta/StrataLint/scripts/report/lean-report.sh"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"

if [[ "${STRATALINT_PR_A_NO_BUILD:-0}" == "1" ]]; then
  for suffix in '' .sha256 .input.attestation .provenance.json; do
    [[ -f "${REPORT}${suffix}" ]] || {
      echo "echo-residual-summary: PR-A Lean report bundle is incomplete at ${REPORT}${suffix}" >&2
      exit 2
    }
  done
else
  "$REPORT_SCRIPT" >&2
fi
cd "$ROOT"
if [[ -n "${STRATALINT_PR_A_CLI_DLL:-}" ]]; then
  exec dotnet "$STRATALINT_PR_A_CLI_DLL" echo-verify --emit --base "$BASE"
fi
exec dotnet run --project "$PROJECT" --configuration Release -- \
  echo-verify --emit --base "$BASE"
