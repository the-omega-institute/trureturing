#!/usr/bin/env bash
set -euo pipefail

# Runs one command-line verb against the pinned project with the build output reused.
#
# The four Makefile targets that reach the command line directly pass --no-build so that a warm tree
# answers in one process start. A fresh worktree carries no build output, so before this script those
# targets failed with a raw process-start exception naming a missing file. Two of five implementation
# seats on 2026-09-11 hit that exception six times between them, and every implementation brief opens
# by calling show-atom. Building once when the binary is absent keeps the warm path unchanged: the
# test is a stat, and a warm tree answers as before.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"
BINARY="$ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint"

cd "$ROOT"

if [ "$#" -eq 0 ]; then
  echo "usage: cli.sh VERB [ARGUMENT ...]" >&2
  exit 2
fi

if [ ! -x "$BINARY" ]; then
  dotnet build "$PROJECT" --configuration Release >/dev/null
fi

exec dotnet run --no-build --project "$PROJECT" --configuration Release -- "$@"
