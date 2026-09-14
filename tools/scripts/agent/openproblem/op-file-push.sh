#!/bin/bash
# op-file-push.sh <local-file> <remote-path>
#
# Copy one file to the Lean build host through the nyxid ssh command proxy, which has no file
# transfer of its own and caps each command at about eight kilobytes. The file is base64
# encoded, sent in chunks, decoded on the far side, and the SHA-256 of the result is compared
# with the source. A mismatch is an error, so a truncated or interleaved transfer cannot be
# mistaken for a delivered file.
#
# Each chunk is its own invocation that emits nothing else: mixing base64 with any other
# output on the same command corrupts the stream.
#
# Host selection comes from the environment so that a driver on another machine does not have
# to edit this file.
set -u
# shasum is a Perl script on macOS; pin the locale so its output is byte-stable.
export LC_ALL=C
PRINCIPAL="${OP_SSH_PRINCIPAL:-mstudio1}"
SERVICE="${OP_SSH_SERVICE:-omega-m3-ssh}"
CHUNK="${OP_TRANSFER_CHUNK:-5000}"

src="${1:?local file}"; dst="${2:?remote path}"
[ -s "$src" ] || { echo "PUSH_NO_SOURCE $src"; exit 5; }
unset NYXID_ACCESS_TOKEN

remote() { timeout 60 nyxid ssh exec --principal "$PRINCIPAL" "$SERVICE" "$1"; }

b64=$(base64 < "$src" | tr -d '\n'); n=${#b64}; i=0
remote "mkdir -p $(dirname "$dst"); : > $dst.b64" >/dev/null 2>&1 \
  || { echo "PUSH_INIT_FAIL $dst"; exit 2; }
while [ "$i" -lt "$n" ]; do
  chunk=${b64:$i:$CHUNK}
  remote "printf '%s' '$chunk' >> $dst.b64" >/dev/null 2>&1 \
    || { echo "PUSH_CHUNK_FAIL at $i"; exit 3; }
  i=$((i + CHUNK))
done

want=$(shasum -a 256 "$src" | cut -d' ' -f1)
got=$(remote "base64 -d < $dst.b64 > $dst && rm -f $dst.b64 && shasum -a 256 $dst | cut -d' ' -f1" 2>/dev/null | tail -1)
if [ "$want" = "$got" ]; then
  echo "PUSH_OK $dst $want"
else
  echo "PUSH_SHA_MISMATCH want=$want got=$got"
  exit 4
fi
