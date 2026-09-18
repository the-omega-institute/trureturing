#!/usr/bin/env bash
set -euo pipefail

# Prepare through make lean-cache-ensure, then build the non-default analysis
# library and its dependencies; clear only its own traces to repeat exports.
# The recursive LeanInformationAuditAnalysis.+ glob covers this directory dedicated
# to opt-in full analyses; adding an exporting fixture requires updating this
# runner's artifact inventory.
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
command -v make >/dev/null 2>&1 || fail 69 'missing command: make'
command -v dotnet >/dev/null 2>&1 || fail 69 'missing command: dotnet'

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

mkdir -p -- "$output_directory" || fail 73 "cannot create output: $output_directory"
[[ -w $output_directory ]] || fail 73 "output is not writable: $output_directory"
make -C "$repository" lean-cache-ensure
export IE_PROJECTION_OUTPUT_DIR=$output_directory
export LC_ALL=C

# The output directory is not a Lake input. Re-elaborate only these modules so a
# cached successful build cannot leave the caller's directory without artifacts.
for fixture in "${fixtures[@]}"; do
  rm -f -- ".lake/build/lib/lean/LeanInformationAuditAnalysis/$fixture.trace"
done
TIMEFORMAT='ANALYSIS_FIXTURES_BUILD wall_seconds=%R'
time lake build LeanInformationAuditAnalysis

for fixture in "${fixtures[@]}"; do
  case $fixture in
    CausalProjection) artifacts=(causal-analysis.json causal-analysis.txt) ;;
    FrozenRootAnalysis) artifacts=(frozen-seal.json frozen-analysis.json frozen-analysis.txt) ;;
    BoundedClosure) artifacts=(bounded-analysis.json bounded-analysis.txt) ;;
  esac
  for artifact in "${artifacts[@]}"; do
    shasum -a 256 -- "$output_directory/$artifact"
  done
done
