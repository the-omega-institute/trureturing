#!/usr/bin/env bash
# Glue only: the candidate CLI owns selection, identities and validation.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
MODE="${1:-}"; [[ $# -gt 0 ]] && shift
REPORT="" BASE="" PURPOSE=check DESTINATION=""
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 && -n "$2" ]] || { echo 'history-report: option requires a value' >&2; exit 2; }
  case "$1" in
    --report) REPORT="$2" ;;
    --protected-base) BASE="$2" ;;
    --purpose) PURPOSE="$2" ;;
    --destination) DESTINATION="$2" ;;
    *) echo "history-report: unknown option $1" >&2; exit 2 ;;
  esac
  shift 2
done
[[ "$MODE" == produce || "$MODE" == stage ]] && [[ -n "$REPORT" ]] \
  || { echo 'history-report: produce|stage --report FILE [--protected-base REV] [--purpose check|seed|discharge]' >&2; exit 2; }
[[ "$PURPOSE" == check || "$PURPOSE" == seed || "$PURPOSE" == discharge ]] \
  || { echo 'history-report: invalid purpose' >&2; exit 2; }
[[ "$MODE" != stage || ( -n "$BASE" && -n "$DESTINATION" ) ]] \
  || { echo 'history-report: stage requires --protected-base and --destination' >&2; exit 2; }
[[ "$REPORT" == /* ]] || REPORT="$ROOT/$REPORT"
[[ -z "$DESTINATION" || "$DESTINATION" == /* ]] || DESTINATION="$ROOT/$DESTINATION"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"
CLI="$ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
cd "$ROOT"
# inspect.sh and the engineering phase already built this exact candidate.
# A standalone consumer has no such guarantee and uses the native incremental build.
if [[ "${STRATALINT_HISTORY_CLI_BUILT:-0}" != 1 ]]; then
  dotnet build "$PROJECT" --configuration Release --nologo --verbosity quiet
fi
[[ -s "$CLI" ]] || { echo 'history-report: candidate CLI is missing' >&2; exit 2; }
TEMP="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-history-plan.XXXXXXXX")"
trap 'rm -rf -- "$TEMP"' EXIT
base_args=()
[[ -z "$BASE" ]] || base_args=(--protected-base "$BASE")
dotnet "$CLI" information-template-history plan ${base_args[@]+"${base_args[@]}"} --purpose "$PURPOSE" --output "$TEMP/plan.json"
revisions="$(python3 -c 'import json,sys; print("\n".join(t["revision"] for t in json.load(open(sys.argv[1]))["targets"]))' "$TEMP/plan.json")"
adjacent="$(dirname "$REPORT")/information-template-history"
writer="$ROOT/.lake/build/stratalint/information-template-history"
donor_args=()
[[ -z "${STRATALINT_HISTORY_CACHE_DONOR:-}" ]] || donor_args=(--cache-donor "$STRATALINT_HISTORY_CACHE_DONOR")
while IFS= read -r revision; do
  [[ -n "$revision" ]] || continue
  if [[ "$MODE" == produce ]]; then
    dotnet "$CLI" information-template-history produce --plan "$TEMP/plan.json" --revision "$revision" \
      --output "$writer/$revision" ${donor_args[@]+"${donor_args[@]}"}
    if [[ "$adjacent" != "$writer" ]]; then
      dotnet "$CLI" information-template-history validate --plan "$TEMP/plan.json" --revision "$revision" \
        --bundle "$writer/$revision" --output "$adjacent/$revision"
    fi
  else
    dotnet "$CLI" information-template-history validate --plan "$TEMP/plan.json" --revision "$revision" \
      --bundle "$adjacent/$revision" --output "$DESTINATION/information-template-history/$revision"
  fi
done <<< "$revisions"
