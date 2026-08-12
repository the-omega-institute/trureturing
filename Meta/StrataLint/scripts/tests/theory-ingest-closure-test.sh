#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../" && pwd -P)"
SCRIPT="$ROOT/Meta/StrataLint/scripts/theory-ingest-closure.sh"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
git_init() { git -C "$1" init -q; git -C "$1" config user.email test@example.com; git -C "$1" config user.name test; }
expect_green() { "$SCRIPT" "$1" --exclude Meta/StrataLint --exclude Makefile --exclude global.json; }
expect_red() { if "$SCRIPT" "$1" --exclude Meta/StrataLint --exclude Makefile --exclude global.json >"$2" 2>&1; then return 1; fi; grep -q 'THEORY-INGEST-CLOSURE-001' "$2"; grep -q 'docs/develop/theory/volume/source.toml' "$2"; }

# A committed candidate with no working-tree differences is clean and green.
d="$tmp/clean"; mkdir -p "$d/Meta/StrataLint" "$d/docs/develop/theory/volume"; git_init "$d"
printf base > "$d/Meta/StrataLint/judge.sh"; printf base > "$d/Makefile"; printf '{}' > "$d/global.json"
printf '# volume\n' > "$d/docs/develop/theory/volume/theory.md"; printf '[source]\nid="volume"\n' > "$d/docs/develop/theory/volume/source.toml"
git -C "$d" add .; git -C "$d" commit -qm init
expect_green "$d"

# The judge overlay changes harness files only; it is excluded from the closure ledger.
d="$tmp/overlay-only"; mkdir -p "$d/Meta/StrataLint" "$d/docs/develop/theory/volume"; git_init "$d"
printf base > "$d/Meta/StrataLint/judge.sh"; printf base > "$d/Makefile"; printf '{}' > "$d/global.json"
printf '# volume\n' > "$d/docs/develop/theory/volume/theory.md"; printf '[source]\nid="volume"\n' > "$d/docs/develop/theory/volume/source.toml"
git -C "$d" add .; git -C "$d" commit -qm init
printf judge > "$d/Meta/StrataLint/judge.sh"; printf judge > "$d/Makefile"; printf '{"judge":true}\n' > "$d/global.json"
expect_green "$d"

# A real ingest ledger/input difference remains visible and names the exact path.
d="$tmp/ledger-dirty"; mkdir -p "$d/Meta/StrataLint" "$d/docs/develop/theory/volume"; git_init "$d"
printf base > "$d/Meta/StrataLint/judge.sh"; printf base > "$d/Makefile"; printf '{}' > "$d/global.json"
printf '# volume\n' > "$d/docs/develop/theory/volume/theory.md"; printf '[source]\nid="volume"\n' > "$d/docs/develop/theory/volume/source.toml"
git -C "$d" add .; git -C "$d" commit -qm init
printf updated > "$d/docs/develop/theory/volume/source.toml"
expect_red "$d" "$tmp/ledger-dirty.out"
printf '%s\n' 'theory-ingest-closure fixtures: 3 passed (clean green, overlay-only green, ledger-dirty red)'
