#!/usr/bin/env bash
set -euo pipefail

mode="${1:?prepare or verify is required}"
shift
root=""
args=("$@")
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) root="$2"; shift 2 ;;
    *) shift ;;
  esac
done
[[ -d "$root" ]] || { echo 'source-context: repository is absent' >&2; exit 2; }
if [[ "$mode" == prepare ]]; then
  dotnet build "$root/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
    --configuration Release --nologo --verbosity quiet
elif [[ "$mode" == verify ]]; then
  args+=(--verify)
else
  echo 'source-context: expected prepare or verify' >&2
  exit 2
fi
exec python3 "$root/tools/lean-inspector/source-context.py" "${args[@]}"
