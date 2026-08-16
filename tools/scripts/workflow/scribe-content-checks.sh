#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo "usage: scribe-content-checks.sh REPORT [SCRIBE_DLL [BASE]]" >&2
  exit 2
fi

REPORT="$1"
SCRIBE_DLL="${2:-}"
BASE="${3:-${STRATALINT_SCRIBE_BASE:-}}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$REPO_ROOT/tools/StrataLint.Scribe/StrataLint.Scribe.csproj"
if [[ ! -s "$REPORT" ]]; then
  echo "scribe-content-checks: raw Lean report is missing or empty at $REPORT" >&2
  exit 2
fi
if [[ ! "$BASE" =~ ^[0-9a-fA-F]{40}$|^[0-9a-fA-F]{64}$ ]]; then
  echo "scribe-content-checks: an exact merge-base is required" >&2
  exit 2
fi
git -C "$REPO_ROOT" cat-file -e "${BASE}^{commit}" \
  || { echo "scribe-content-checks: BASE commit is unavailable" >&2; exit 2; }
SCRIBE=(dotnet run --project "$PROJECT" --configuration Release --)
if [[ -n "$SCRIBE_DLL" ]]; then
  SCRIBE=(dotnet "$SCRIBE_DLL")
fi

cd "$REPO_ROOT"
run_scribe() {
  STRATALINT_LEAN_REPORT="$REPORT" "${SCRIBE[@]}" "$@"
}

CHANGED_PATHS=()
while IFS= read -r -d '' path; do
  CHANGED_PATHS+=("$path")
done < <(
  git diff --name-only --no-renames -z "$BASE" --
  git ls-files --others --exclude-standard -z
)

requires_emission_checks=0
derive_producer_closure=0
if [[ "${#CHANGED_PATHS[@]}" -gt 0 ]]; then
  for path in "${CHANGED_PATHS[@]}"; do
    case "$path" in
      Blueprint/*|D5/*.lean|Trureturing.lean|lean-toolchain|lake-manifest.json|lakefile.toml|lakefile.lean|\
      Library/*|Golden/Projection/*|Meta/BACKFILL.yaml|Meta/Digestion/ticket-index.toml|\
      Meta/Digestion/backfill/*|Golden/values-kernels.toml|Evidence/D5/values.json|\
      .github/workflows/ci.yml|Directory.Build.props|Directory.Build.targets|Directory.Packages.props|\
      global.json|tools/StrataLint.Scribe/*|tools/StrataLint.Engine/*|tools/StrataLint.Cli/*|\
      tools/Architecture/*|tools/lean-inspector/*|tools/scripts/workflow/scribe-content-checks.sh|\
      tools/scripts/report/lean-report-input.sh)
        requires_emission_checks=1
        break
        ;;
      *.cs|*.sh|*.csproj|*.props|*.targets|*/packages.lock.json)
        derive_producer_closure=1
        ;;
    esac
  done
fi

if [[ "$requires_emission_checks" == "0" && "$derive_producer_closure" == "1" ]]; then
  producer_output="$(
    "$REPO_ROOT/tools/scripts/report/lean-report-input.sh" scribe-producer-paths \
      --repository "$REPO_ROOT"
  )" || { echo "scribe-content-checks: Scribe producer closure is unavailable" >&2; exit 2; }
  while IFS= read -r producer_path; do
    for path in "${CHANGED_PATHS[@]}"; do
      if [[ "$path" == "$producer_path" ]]; then
        requires_emission_checks=1
        break 2
      fi
    done
  done <<< "$producer_output"
fi

run_scribe projections --check --report "$REPORT"
if [[ "$requires_emission_checks" == "1" ]]; then
  run_scribe emit --check
  run_scribe emit-values --check
else
  echo "skipped: emit --check and emit-values --check (delta misses coarse emission closure)"
fi
run_scribe describe-report --check
