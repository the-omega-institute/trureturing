#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -gt 0 ]; then
  out=$1
else
  out=$(mktemp -d "${TMPDIR:-/tmp}/phi4-gap4.XXXXXX")
fi
python3 "$here/rebuild_gap4.py" "$out"
printf 'Exact proof and replay outputs: %s\n' "$out"
