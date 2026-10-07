#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo "usage: scribe-content-checks.sh REPORT SCRIBE_DLL PATHS_FILE" >&2
  exit 2
fi
REPORT="$1"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
SCRIBE_DLL="${2:-$REPO_ROOT/tools/StrataLint.Scribe/bin/Release/net10.0/StrataLint.Scribe.dll}"
PATHS_FILE="${3:-}"
[[ -s "$REPORT" && -f "$SCRIBE_DLL" ]] || { echo "scribe-content-checks: report or candidate DLL missing" >&2; exit 2; }
cd "$REPO_ROOT"
if [[ ! -f "$PATHS_FILE" || ! -r "$PATHS_FILE" ]]; then
  echo "scribe-content-checks: PATHS_FILE must be a readable regular file: $PATHS_FILE" >&2
  exit 2
fi
STRATALINT_LEAN_REPORT="$REPORT" dotnet "$SCRIBE_DLL" content-check --report "$REPORT" --paths-from "$PATHS_FILE"
