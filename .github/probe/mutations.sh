#!/bin/bash
# One-off probe (never merged): does any change confined to an excluded region
# change the verdict of the program that the exclusion skips?
# Each scenario commits a synthetic change on top of the event commit M and
# reruns the skipped programs; outputs go to /tmp/probe/mutations/<scenario>.
set -uo pipefail
cd "$GITHUB_WORKSPACE"
: "${CLI:?}" "${SCRIBE:?}" "${REPORT:?}"
M="$(git rev-parse HEAD)"
OUT=/tmp/probe/mutations
mkdir -p "$OUT"
git config user.email probe@example.invalid
git config user.name probe

first() { git ls-files -- "$@" | head -n 1; }

run_checks() {
  local name="$1" kinds="$2" dir="$OUT/$1"
  mkdir -p "$dir"
  git add -A -- . ':!:.lake' >/dev/null 2>&1 || true
  git commit -q --allow-empty -m "probe $name" >/dev/null 2>&1
  git diff --name-status --no-renames "$M" HEAD > "$dir/changed.txt"
  git diff --name-only --no-renames -z "$M" HEAD > "$dir/changed.z"
  tools/scripts/workflow/scribe-scope-paths.sh "$dir/changed.z" > "$dir/scribe-paths" 2> "$dir/scribe-scope.err"
  echo $? > "$dir/scribe-scope.rc"
  if [[ "$kinds" == *current* ]]; then
    dotnet "$CLI" check-current --candidate-lean-report "$REPORT" --scribe-paths-from "$dir/scribe-paths" > "$dir/current.log" 2>&1
    echo $? > "$dir/current.rc"
    tools/scripts/workflow/scribe-content-checks.sh "$REPORT" "$SCRIBE" "$dir/scribe-paths" > "$dir/scribe.log" 2>&1
    echo $? > "$dir/scribe.rc"
  fi
  if [[ "$kinds" == *filemap* ]]; then
    make filemap-conform > "$dir/filemap.log" 2>&1
    echo $? > "$dir/filemap.rc"
  fi
  if [[ "$kinds" == *delta* ]]; then
    dotnet "$CLI" check-delta --protected-base "$M" --candidate-lean-report "$REPORT" > "$dir/delta.log" 2>&1
    echo $? > "$dir/delta.rc"
  fi
  echo "PROBE_SCENARIO $name current=$(cat "$dir/current.rc" 2>/dev/null) scribe=$(cat "$dir/scribe.rc" 2>/dev/null) filemap=$(cat "$dir/filemap.rc" 2>/dev/null) delta=$(cat "$dir/delta.rc" 2>/dev/null)"
  git reset -q --hard "$M"
}

append() { local f; for f in "$@"; do [[ -f "$f" ]] && printf '\nprobe\n' >> "$f"; done; }

# Baseline at M itself.
run_checks S00-baseline current,filemap,delta

# Regions excluded from current, filemap and delta.
append README.md docs/VISION.md docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md \
  docs/develop/spec/trureturing_engineering_optimization_v1.md tools/lean-inspector/README.md \
  tools/scripts/agent/openproblem/README.md tools/scripts/agent/openproblem/SCREENED-OUT.md \
  tools/scripts/agent/prime_slabs/CPU.md
printf '<!-- probe -->\n' >> docs/assets/inquiry-cycle.svg
rts="$(first 'tools/TestSupport/StrataLint.RuleTestSupport/*.cs')"
[[ -n "$rts" ]] && printf '\n// probe\n' >> "$rts"
report="$(first 'docs/reports/*')"
[[ -n "$report" ]] && printf '\nprobe\n' >> "$report"
run_checks C01-modify-excluded current,filemap,delta

git rm -q -- README.md docs/VISION.md docs/assets/inquiry-cycle.svg \
  docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md \
  docs/develop/spec/trureturing_engineering_optimization_v1.md tools/lean-inspector/README.md \
  tools/scripts/agent/openproblem/README.md tools/scripts/agent/prime_slabs/CPU.md \
  tools/scripts/agent/openproblem/SCREENED-OUT-R52.md
run_checks C02-delete-excluded current,filemap,delta

mkdir -p docs/reports
printf 'probe\n' > docs/reports/probe-unregistered.md
printf 'probe\n' > tools/TestSupport/StrataLint.RuleTestSupport/probe.txt
printf 'probe\n' > tools/scripts/agent/openproblem/SCREENED-OUT-PROBE.md
run_checks C03-add-unregistered current,filemap,delta

rtsproj="$(first 'tools/TestSupport/StrataLint.RuleTestSupport/*.csproj')"
if [[ -n "$rtsproj" ]]; then
  sed -i 's#</Project>#  <ItemGroup><ProjectReference Include="../../StrataLint.Cli/StrataLint.Cli.csproj" /></ItemGroup>\n</Project>#' "$rtsproj"
fi
printf 'namespace Probe; public sealed class Broken { this is not csharp }\n' > tools/TestSupport/StrataLint.RuleTestSupport/ProbeBroken.cs
run_checks C04-rule-test-support-code current,filemap,delta

ln -s ../../../README.md docs/develop/theory/probe-link.md
printf '\x00\x01probe' > docs/develop/theory/probe.bin
run_checks C05-theory-filemap filemap

for count in $(seq 1 150); do printf 'probe %s\n' "$count" > "docs/reports/probe-$count.md"; done
run_checks C06-reports-capacity current,filemap,delta

# Regions excluded only from delta.
bp="$(first 'Blueprint/*.scribe.cs')"
append "$bp" "${bp%.scribe.cs}.md"
run_checks D01-blueprint-modify delta

bpmd="$(first 'Blueprint/*.md')"
git rm -q -- "$bpmd"
mkdir -p Blueprint/D5/ProbeOrphan
printf '// probe orphan\n' > Blueprint/D5/ProbeOrphan/Orphan.scribe.cs
run_checks D02-blueprint-delete-orphan delta

ev="$(first 'Evidence/*')"
append "$ev"
mkdir -p Evidence/probe
printf 'probe\n' > Evidence/probe/unknown.format
run_checks D03-evidence delta

gp="$(first 'Golden/Projection/*.json')"
[[ -n "$gp" ]] && printf '{ not json\n' >> "$gp"
run_checks D04-golden-projection delta

lib="$(first 'Library/*/*.md')"
append "$lib"
libdir="$(dirname "$lib")"
printf 'not a library note\n' > "$libdir/probe-malformed.md"
run_checks D05-library delta

pb="$(first 'Problems/*')"
git rm -q -- "$pb"
printf 'not a dossier\n' > Problems/probe-malformed.md
run_checks D06-problems delta

bpdir="$(dirname "$bp")"
for count in $(seq 1 200); do printf '// probe %s\n' "$count" > "$bpdir/Probe$count.scribe.cs"; done
run_checks D07-blueprint-capacity delta

echo "PROBE_MUTATIONS_DONE base=$M"
