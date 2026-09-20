#!/usr/bin/env bash
set -euo pipefail

# Build the nondefault analysis libraries through make lean; clear only each
# exporting fixture's trace so a warm build repeats its output operations.
# Generic analyses remain in Impl; production analyses belong to Reg.
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

[[ $# -ge 1 && $# -le 2 && -n $1 ]] || fail 64 "usage: $0 OUTPUT_DIRECTORY [all|generic|production]"
scope=${2:-all}
case "$scope" in all|generic|production) ;; *) fail 64 "invalid analysis scope: $scope" ;; esac
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

fixtures=() targets=() traces=() sources=()
if [[ $scope == all || $scope == generic ]]; then
  fixtures+=(CausalProjection BoundedClosure)
  targets+=(LeanInformationAuditAnalysis)
  for fixture in CausalProjection BoundedClosure; do
    sources+=("$script_directory/$fixture.lean")
    traces+=(".lake/build/lib/lean/LeanInformationAuditAnalysis/$fixture.trace")
  done
fi
if [[ $scope == all || $scope == production ]]; then
  fixtures+=(FrozenRootAnalysis)
  targets+=(@reg/LeanInformationAuditRegAnalysis)
  sources+=("$script_directory/../LeanInformationAuditRegAnalysis/FrozenRootAnalysis.lean"
    Reg/lakefile.toml Reg/lake-manifest.json)
  traces+=(.lake/build/reg/lib/lean/LeanInformationAuditRegAnalysis/FrozenRootAnalysis.trace)
fi
for input in lakefile.toml lake-manifest.json lean-toolchain; do
  [[ -r $input ]] || fail 66 "missing input: $input"
done
for input in "${sources[@]}"; do
  [[ -r $input ]] || fail 66 "missing input: $input"
done

mkdir -p -- "$output_directory" || fail 73 "cannot create output: $output_directory"
[[ -w $output_directory ]] || fail 73 "output is not writable: $output_directory"
make -C "$repository" lean-cache-ensure
export IE_PROJECTION_OUTPUT_DIR=$output_directory
export LC_ALL=C

# The output directory is not a Lake input. Re-elaborate only these modules so a
# cached successful build cannot leave the caller's directory without artifacts.
for trace in "${traces[@]}"; do
  rm -f -- "$trace"
done
TIMEFORMAT='ANALYSIS_FIXTURES_BUILD wall_seconds=%R'
time make -C "$repository" lean LEAN_TARGETS="${targets[*]}"

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
