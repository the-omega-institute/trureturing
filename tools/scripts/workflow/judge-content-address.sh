#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 1 || ! "$1" =~ ^[0-9a-f]{64}$ ]]; then
  printf '%s\n' 'usage: judge-content-address.sh <source-address-sha256>' >&2
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
  printf '%s\n' 'dotnet did not report its runtime, architecture, and SDK version' >&2
  exit 1
fi

address="$(printf 'source=%s\nruntime=%s\narchitecture=%s\nsdk=%s\n' \
  "$source_address" "$runtime" "$architecture" "$sdk" | sha256sum | cut -d ' ' -f 1)"
[[ "$address" =~ ^[0-9a-f]{64}$ ]]
printf 'address=%s\nruntime=%s\n' "$address" "$runtime"
