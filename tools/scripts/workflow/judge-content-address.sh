#!/usr/bin/env bash
# Default dev ci.yml transition. Remove after successful ci-push/ci-pr checks
# and required-set migration, together with its remaining caller.
set -euo pipefail
export DOTNET_CLI_UI_LANGUAGE=en-US

if [[ "$#" -ne 1 || ! "$1" =~ ^[0-9a-f]{64}$ ]]; then
  echo 'usage: judge-content-address.sh <source-address-sha256>' >&2
  exit 2
fi
source_address="$1"
dotnet_info="$(dotnet --info)"
runtime="$(awk '
  $0 == "Host:" { in_host = 1; next }
  in_host && $1 == "Version:" { print $2; exit }
' <<< "$dotnet_info")"
architecture="$(awk '
  $0 == "Host:" { in_host = 1; next }
  in_host && $1 == "Architecture:" { print $2; exit }
' <<< "$dotnet_info")"
sdk="$(dotnet --version)"
if [[ -z "$runtime" || -z "$architecture" || -z "$sdk" ]]; then
  echo 'dotnet did not report its runtime, architecture, and SDK version' >&2
  exit 1
fi
address="$(printf 'source=%s\nruntime=%s\narchitecture=%s\nsdk=%s\n' \
  "$source_address" "$runtime" "$architecture" "$sdk" \
  | python3 -c 'import hashlib, sys; print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())')"
[[ "$address" =~ ^[0-9a-f]{64}$ ]]
printf 'address=%s\nruntime=%s\n' "$address" "$runtime"
