#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
BASE_REF="origin/dev"
FORCE=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --base)
      [[ $# -ge 2 ]] || { echo "clean-lanes.sh: --base requires a value" >&2; exit 2; }
      BASE_REF="$2"
      shift 2
      ;;
    --force)
      [[ "$FORCE" == "0" ]] || { echo "clean-lanes.sh: duplicate --force" >&2; exit 2; }
      FORCE=1
      shift
      ;;
    *)
      echo "clean-lanes.sh: unknown argument '$1'" >&2
      exit 2
      ;;
  esac
done

arguments=(clean-lanes --base "$BASE_REF")
if [[ "$FORCE" == "1" ]]; then arguments+=(--force); fi

exec dotnet run \
  --project "$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release \
  -- "${arguments[@]}"
