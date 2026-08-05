#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
COMMAND="${1:-}"
BASE="${2:-origin/dev}"

run_digest_status() {
  dotnet run --project "$PROJECT" --configuration Release -- digest-status --base "$BASE"
}

receipts_stage() {
  make ingest BASE="$BASE"
  run_digest_status
}

cd "$ROOT"
case "$COMMAND" in
  deliver-check)
    make lean-report
    make emit
    receipts_stage
    # Freeze last among all mutating derivations so the receipt binds committed source bytes.
    dotnet run --project "$PROJECT" --configuration Release -- \
      ledger-append --candidate-lean-report "$REPORT"
    make emit-check BASE="$BASE"
    run_digest_status
    make preflight BASE="$BASE"
    ;;
  receipts-stage)
    receipts_stage
    ;;
  derived-refresh)
    git merge --no-edit "$BASE"
    make lean-report
    make emit
    receipts_stage
    make emit-check BASE="$BASE"
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check|receipts-stage|derived-refresh [BASE]" >&2
    exit 2
    ;;
esac
