#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
tools_dir="$(cd "$script_dir/.." && pwd -P)"
project="$tools_dir/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj"
contract="$tools_dir/tests/StrataLint.Scribe.Tests/Projection/RendererCorpusContractTests.cs"
test_name='FullyQualifiedName=StrataLint.Scribe.Tests.FormulaCorpusInventoryTests.FixedSyntheticCorpusFreezesRendererBehavior'
log="$(mktemp "${TMPDIR:-/tmp}/renderer-contract.XXXXXX")"
trap 'rm -f "$log"' EXIT

set +e
STRATALINT_PRINT_RENDERER_CONTRACT=1 \
  dotnet test "$project" \
    --configuration Release \
    --filter "$test_name" \
    --logger 'console;verbosity=normal' >"$log" 2>&1
test_rc=$?
set -e

if [[ $test_rc -eq 0 ]]; then
  echo "renderer contract updater failed: print mode unexpectedly passed" >&2
  exit 1
fi

sha="$({ sed -nE 's/.*RENDERER_CONTRACT_SHA256=([0-9a-f]{64}).*/\1/p' "$log" || true; } | head -n 1)"
if [[ ! $sha =~ ^[0-9a-f]{64}$ ]]; then
  echo "renderer contract updater failed: test did not emit a complete SHA-256" >&2
  cat "$log" >&2
  exit 1
fi

RENDERER_CONTRACT_SHA256="$sha" perl -0pi -e '
  BEGIN { $count = 0; }
  $count += s{(private const string CanonicalRendererSha256\s*=\s*\n\s*")[0-9a-f]{64}(";)}{$1 . $ENV{"RENDERER_CONTRACT_SHA256"} . $2}e;
  END { die "renderer contract updater matched $count constants, expected 1\n" unless $count == 1; }
' "$contract"

dotnet test "$project" \
  --configuration Release \
  --filter "$test_name" \
  --logger 'console;verbosity=minimal'
printf 'updated renderer behavior contract: %s\n' "$sha"
