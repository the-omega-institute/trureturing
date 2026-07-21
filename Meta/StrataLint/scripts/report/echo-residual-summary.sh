#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
BASE="${1:-origin/dev}"
MODE="${2:-render}"
REVIEW="${3:-}"
REPORT_SCRIPT="$ROOT/Meta/StrataLint/scripts/report/lean-report.sh"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"

case "$MODE" in
  render)
    [[ -z "$REVIEW" ]] \
      || { echo "echo-residual-summary: render mode does not accept a review path" >&2; exit 2; }
    ;;
  --verify)
    [[ -n "$REVIEW" ]] \
      || { echo "echo-residual-summary: --verify requires a review path" >&2; exit 2; }
    ;;
  *)
    echo "echo-residual-summary: expected --verify REVIEW after BASE" >&2
    exit 2
    ;;
esac

"$REPORT_SCRIPT" >&2
cd "$ROOT"
if [[ "$MODE" == "--verify" ]]; then
  exec dotnet run --project "$PROJECT" --configuration Release -- \
    digest-status --residual-summary --base "$BASE" --verify-review "$REVIEW"
fi
exec dotnet run --project "$PROJECT" --configuration Release -- \
  digest-status --residual-summary --base "$BASE"
