#!/usr/bin/env bash
set -euo pipefail

# Run after make lean-cache-ensure and lake build Trureturing LeanInformationAudit.
# Exit 64 means bad arguments, 66 missing inputs, 69 missing tools, 73 output
# unavailable; otherwise preserve the failing command's exit code. Only exit 0
# and ANALYSIS_FIXTURES_EXIT=0 indicate that all fixtures finished.
finish() {
  local fixture_exit=$?
  printf 'ANALYSIS_FIXTURES_EXIT=%s\n' "$fixture_exit"
  exit "$fixture_exit"
}
trap finish EXIT

fail() {
  printf '%s\n' "$2" >&2
  exit "$1"
}

[[ $# -eq 1 && -n $1 ]] || fail 64 "usage: $0 OUTPUT_DIRECTORY"
command -v lake >/dev/null 2>&1 || fail 69 'missing command: lake'
command -v shasum >/dev/null 2>&1 || fail 69 'missing command: shasum'

script_directory=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
repository=$(cd -- "$script_directory/../../.." && pwd -P)
output_directory=$1
if [[ $output_directory != /* ]]; then
  output_directory=$PWD/$output_directory
fi
cd -- "$repository"

fixtures=(CausalProjection FrozenRootAnalysis BoundedClosure)
for input in lakefile.toml lake-manifest.json lean-toolchain; do
  [[ -r $input ]] || fail 66 "missing input: $input"
done
for fixture in "${fixtures[@]}"; do
  input=$script_directory/$fixture.lean
  [[ -r $input ]] || fail 66 "missing input: $input"
done

# Lean resolves the import paths; check all three before starting costly work.
for fixture in "${fixtures[@]}"; do
  dependencies=$(lake env lean --deps "$script_directory/$fixture.lean")
  while IFS= read -r dependency; do
    [[ -r $dependency ]] || fail 66 "missing built input: $dependency"
  done <<< "$dependencies"
done

mkdir -p -- "$output_directory" || fail 73 "cannot create output: $output_directory"
[[ -w $output_directory ]] || fail 73 "output is not writable: $output_directory"
export IE_PROJECTION_OUTPUT_DIR=$output_directory
export LC_ALL=C

for fixture in "${fixtures[@]}"; do
  TIMEFORMAT="ANALYSIS_FIXTURE file=$fixture wall_seconds=%R"
  time lake env lean "tools/lean-inspector/LeanInformationAuditAnalysis/$fixture.lean"
  case $fixture in
    CausalProjection) artifacts=(causal-analysis.json causal-analysis.txt) ;;
    FrozenRootAnalysis) artifacts=(frozen-seal.json frozen-analysis.json frozen-analysis.txt) ;;
    BoundedClosure) artifacts=(bounded-analysis.json bounded-analysis.txt) ;;
  esac
  for artifact in "${artifacts[@]}"; do
    shasum -a 256 -- "$output_directory/$artifact"
  done
done
