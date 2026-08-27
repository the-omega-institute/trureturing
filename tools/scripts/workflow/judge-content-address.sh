#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 1 || ! "$1" =~ ^[0-9a-f]{64}$ ]]; then
  printf '%s\n' 'usage: judge-content-address.sh <source-address-sha256>' >&2
  exit 2
fi

source_address="$1"
runtime="$(dotnet --info | awk '
  $0 == "Host:" { in_host = 1; next }
  in_host && $1 == "Version:" { print $2; exit }
')"
if [[ -z "$runtime" ]]; then
  printf '%s\n' 'dotnet --info did not report an executing host runtime version' >&2
  exit 1
fi

address="$(printf 'source=%s\nruntime=%s\n' "$source_address" "$runtime" | sha256sum | cut -d ' ' -f 1)"
[[ "$address" =~ ^[0-9a-f]{64}$ ]]
printf 'address=%s\nruntime=%s\n' "$address" "$runtime"
