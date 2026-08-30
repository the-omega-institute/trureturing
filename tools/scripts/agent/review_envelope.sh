#!/usr/bin/env bash
# review_envelope.sh WORKTREE BASE HEAD — run the typed verb inside WORKTREE and print its JSON.
# The one place the repository invokes `review-envelope` (CliVerbLinkageTests scans *.sh callers).
# STRATALINT_CLI overrides the launcher (e.g. "dotnet /path/StrataLint.dll") on trees that predate the verb.
set -euo pipefail
[[ $# -eq 3 ]] || { echo "usage: review_envelope.sh WORKTREE BASE HEAD" >&2; exit 64; }
[[ -d "$1/.git" || -f "$1/.git" ]] || { echo "REVIEW_ENVELOPE_NOT_A_WORKTREE $1" >&2; exit 65; }
cd "$1"
if [[ -n "${STRATALINT_CLI:-}" ]]; then
  # shellcheck disable=SC2086
  exec $STRATALINT_CLI review-envelope --base "$2" --head "$3"
fi
exec dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- review-envelope --base "$2" --head "$3"
