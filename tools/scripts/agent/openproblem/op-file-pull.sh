#!/bin/bash
# op-file-pull.sh <remote-path> <local-file>
#
# The reverse of op-file-push.sh: copy one file back from the Lean build host through the
# nyxid ssh command proxy, chunked and SHA-256 verified. Used to bring a git bundle back to a
# machine that holds GitHub credentials, since the build host has none.
#
# Each chunk is its own invocation returning exactly that chunk and nothing else; any other
# output on the same command corrupts the base64 stream.
set -u
# shasum is a Perl script on macOS; pin the locale so its output is byte-stable.
export LC_ALL=C
PRINCIPAL="${OP_SSH_PRINCIPAL:-mstudio1}"
SERVICE="${OP_SSH_SERVICE:-omega-m3-ssh}"
CHUNK="${OP_TRANSFER_CHUNK:-6000}"

src="${1:?remote path}"; dst="${2:?local file}"
unset NYXID_ACCESS_TOKEN

remote() { timeout 60 nyxid ssh exec --principal "$PRINCIPAL" "$SERVICE" "$1"; }

want=$(remote "shasum -a 256 $src | cut -d' ' -f1" 2>/dev/null | tr -d ' \r\n')
[ -n "$want" ] || { echo "PULL_NO_SOURCE $src"; exit 2; }
n=$(remote "base64 < $src | tr -d '\n' | wc -c" 2>/dev/null | tr -d ' \r\n')
[ -n "$n" ] || { echo "PULL_NO_SIZE $src"; exit 2; }
remote "base64 < $src | tr -d '\n' > $src.b64" >/dev/null 2>&1 \
  || { echo "PULL_B64_FAIL $src"; exit 3; }

: > "$dst.b64"; i=1
while [ "$i" -le "$n" ]; do
  e=$((i + CHUNK - 1))
  c=$(remote "cut -c$i-$e $src.b64" 2>/dev/null | tr -d ' \r\n')
  [ -n "$c" ] || { echo "PULL_CHUNK_EMPTY at $i"; exit 4; }
  printf '%s' "$c" >> "$dst.b64"
  i=$((e + 1))
done

base64 -d < "$dst.b64" > "$dst" && rm -f "$dst.b64"
got=$(shasum -a 256 "$dst" | cut -d' ' -f1)
remote "rm -f $src.b64" >/dev/null 2>&1
if [ "$want" = "$got" ]; then
  echo "PULL_OK $dst $got"
else
  echo "PULL_SHA_MISMATCH want=$want got=$got"
  exit 5
fi
