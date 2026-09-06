#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

# The report consumer also sources the shared manifest and memo primitives.
if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  COMMAND="${1:-}"
  if [[ -n "$COMMAND" ]]; then shift; fi
  REPOSITORY=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --repository) REPOSITORY="${2:?--repository needs a value}"; shift 2 ;;
      *) echo "lean-cache-input: unknown argument '$1'" >&2; exit 2 ;;
    esac
  done
  [[ "$COMMAND" == "address" ]] \
    || { echo "usage: lean-cache-input.sh address --repository DIR" >&2; exit 2; }
  [[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
    || { echo "lean-cache-input: --repository requires an absolute directory" >&2; exit 2; }
  REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
  TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-lean-input.XXXXXXXX")"
  cleanup() { rm -rf -- "$TMP_ROOT"; }
  trap cleanup EXIT
fi

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

MEMO_ROOT="${STRATALINT_LEAN_INPUT_MEMO_ROOT:-}"
if [[ -z "$MEMO_ROOT" ]]; then
  if [[ -n "${XDG_CACHE_HOME:-}" ]]; then
    MEMO_ROOT="$XDG_CACHE_HOME/stratalint-lean-input-memo"
  elif [[ -n "${HOME:-}" ]]; then
    MEMO_ROOT="$HOME/.cache/stratalint-lean-input-memo"
  fi
fi
MEMO_FILE="$MEMO_ROOT/memo.v1"
MEMO_ELIGIBLE="$TMP_ROOT/memo.eligible"
MEMO_SNAPSHOT="$TMP_ROOT/memo.snapshot"
MEMO_UPDATES="$TMP_ROOT/memo.updates"
MEMO_ENABLED=0

memo_root_trusted() {
  [[ -n "$MEMO_ROOT" && -d "$MEMO_ROOT" ]] || return 1
  local owner perm
  if owner="$(stat -f '%u' "$MEMO_ROOT" 2>/dev/null)" \
    && perm="$(stat -f '%Lp' "$MEMO_ROOT" 2>/dev/null)"; then
    :
  elif owner="$(stat -c '%u' "$MEMO_ROOT" 2>/dev/null)" \
    && perm="$(stat -c '%a' "$MEMO_ROOT" 2>/dev/null)"; then
    :
  else
    return 1
  fi
  [[ "$owner" == "$(id -u)" && "$perm" =~ ^[0-7]+$ ]] || return 1
  (( (8#$perm & 8#22) == 0 )) || return 1
}

prepare_memo() {
  : > "$MEMO_ELIGIBLE"
  : > "$MEMO_SNAPSHOT"
  : > "$MEMO_UPDATES"
  [[ -n "$MEMO_ROOT" ]] || return 0

  local status="$TMP_ROOT/git-status"
  local index="$TMP_ROOT/git-index"
  git -C "$REPOSITORY" status --porcelain=v1 -z --untracked-files=all > "$status" \
    2>/dev/null || return 0
  git -C "$REPOSITORY" ls-files -s -z > "$index" 2>/dev/null || return 0

  if [[ ! -e "$MEMO_ROOT" ]]; then
    local old_umask
    old_umask="$(umask)"
    umask 077
    mkdir -p "$MEMO_ROOT" 2>/dev/null || { umask "$old_umask"; return 0; }
    umask "$old_umask"
  fi
  memo_root_trusted || return 0
  [[ ! -e "$MEMO_FILE" || -f "$MEMO_FILE" ]] || return 0

  if ! python3 - "$MEMO_FILE" "$status" "$index" \
    "$MEMO_ELIGIBLE" "$MEMO_SNAPSHOT" 2>/dev/null <<'PY'
import pathlib
import re
import sys

memo_path, status_path, index_path, eligible_path, snapshot_path = map(pathlib.Path, sys.argv[1:])
oid_pattern = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})")
sha_pattern = re.compile(r"[0-9a-f]{64}")

memo = {}
if memo_path.exists():
    with memo_path.open("r", encoding="ascii", newline="") as source:
        for raw_line in source:
            if not raw_line.endswith("\n"):
                raise ValueError("unterminated memo line")
            line = raw_line[:-1]
            fields = line.split(" ")
            if (len(fields) != 2 or not oid_pattern.fullmatch(fields[0])
                    or not sha_pattern.fullmatch(fields[1]) or fields[0] in memo):
                raise ValueError("malformed memo")
            memo[fields[0]] = fields[1]

status_records = status_path.read_bytes().split(b"\0")
dirty = set()
position = 0
while position < len(status_records) and status_records[position]:
    record = status_records[position]
    position += 1
    if len(record) < 4 or record[2:3] != b" ":
        raise ValueError("malformed git status")
    code = record[:2]
    dirty.add(record[3:])
    if b"R" in code or b"C" in code:
        if position >= len(status_records) or not status_records[position]:
            raise ValueError("malformed git rename status")
        dirty.add(status_records[position])
        position += 1

eligible = {}
for record in index_path.read_bytes().split(b"\0"):
    if not record:
        continue
    header, separator, relative = record.partition(b"\t")
    fields = header.split(b" ")
    if not separator or len(fields) != 3:
        raise ValueError("malformed git index")
    mode, oid, stage = fields
    if stage == b"0" and mode in (b"100644", b"100755") and relative not in dirty:
        if not oid_pattern.fullmatch(oid.decode("ascii")) or relative in eligible:
            raise ValueError("malformed stage-zero git index")
        eligible[relative] = oid

with eligible_path.open("wb") as output:
    for relative, oid in eligible.items():
        output.write(relative + b"\0" + oid + b"\0")
with snapshot_path.open("w", encoding="ascii", newline="") as output:
    for oid in sorted(memo):
        output.write(f"{oid} {memo[oid]}\n")
PY
  then
    : > "$MEMO_ELIGIBLE"
    : > "$MEMO_SNAPSHOT"
    return 0
  fi
  MEMO_ENABLED=1
}

hash_files_batch() {
  local paths="$1"
  local hashes="$2"
  : > "$hashes"
  [[ -s "$paths" ]] || return 0
  if command -v sha256sum >/dev/null 2>&1; then
    xargs -0 sha256sum < "$paths" | awk '{print $1}' > "$hashes"
  elif command -v openssl >/dev/null 2>&1; then
    xargs -0 openssl dgst -sha256 < "$paths" | awk '{print $NF}' > "$hashes"
  else
    xargs -0 shasum -a 256 < "$paths" | awk '{print $1}' > "$hashes"
  fi
}

materialize_manifest() {
  local manifest="$1"
  local requests="${manifest}.requests"
  local plan="${manifest}.plan"
  local live_paths="${manifest}.live-paths"
  local live_hashes="${manifest}.live-hashes"
  local eligible="$MEMO_ELIGIBLE"
  local snapshot="$MEMO_SNAPSHOT"
  if [[ "$MEMO_ENABLED" != "1" ]]; then
    eligible="$TMP_ROOT/memo.disabled.eligible"
    snapshot="$TMP_ROOT/memo.disabled.snapshot"
    : > "$eligible"
    : > "$snapshot"
  fi

  python3 - "$REPOSITORY" "$requests" "$eligible" "$snapshot" \
    "$plan" "$live_paths" <<'PY' || return 2
import pathlib
import re
import sys
import os

repository = pathlib.Path(sys.argv[1])
requests_path, eligible_path, memo_path, plan_path, live_path = map(pathlib.Path, sys.argv[2:])

def pairs(path):
    fields = path.read_bytes().split(b"\0")
    if fields and fields[-1] == b"":
        fields.pop()
    if len(fields) % 2:
        raise ValueError(f"malformed pair file: {path}")
    return zip(fields[::2], fields[1::2])

eligible = dict(pairs(eligible_path))
memo = {}
sha_pattern = re.compile(rb"[0-9a-f]{64}")
for line in memo_path.read_bytes().splitlines():
    oid, separator, sha = line.partition(b" ")
    if not separator or not sha_pattern.fullmatch(sha):
        raise ValueError("malformed memo snapshot")
    memo[oid] = sha

repository_prefix = os.fsencode(repository) + b"/"
with plan_path.open("wb") as plan, live_path.open("wb") as live:
    for relative, path in pairs(requests_path):
        oid = eligible.get(relative, b"") if path == repository_prefix + relative else b""
        sha = memo.get(oid, b"") if oid else b""
        plan.write(relative + b"\0" + oid + b"\0" + sha + b"\0")
        if not sha:
            live.write(path + b"\0")
PY

  hash_files_batch "$live_paths" "$live_hashes" || return 2
  python3 - "$plan" "$live_hashes" "$manifest" "$MEMO_UPDATES" <<'PY'
import pathlib
import re
import sys

plan_path, hashes_path, manifest_path, updates_path = map(pathlib.Path, sys.argv[1:])
fields = plan_path.read_bytes().split(b"\0")
if fields and fields[-1] == b"":
    fields.pop()
if len(fields) % 3:
    raise ValueError("malformed hash plan")
records = list(zip(fields[::3], fields[1::3], fields[2::3]))
hashes = hashes_path.read_bytes().splitlines()
sha_pattern = re.compile(rb"[0-9a-f]{64}")
if any(not sha_pattern.fullmatch(value) for value in hashes):
    raise ValueError("hasher returned a malformed SHA-256")

hash_position = 0
updates = []
with manifest_path.open("wb") as manifest:
    for relative, oid, cached_sha in records:
        if cached_sha:
            sha = cached_sha
        else:
            if hash_position >= len(hashes):
                raise ValueError("hasher returned too few SHA-256 values")
            sha = hashes[hash_position]
            hash_position += 1
            if oid:
                updates.append(oid + b" " + sha + b"\n")
        manifest.write(sha + b"  " + relative + b"\n")
if hash_position != len(hashes):
    raise ValueError("hasher returned too many SHA-256 values")
with updates_path.open("ab") as updates_file:
    updates_file.writelines(updates)
PY
}

store_memo_updates() {
  [[ "$MEMO_ENABLED" == "1" && -s "$MEMO_UPDATES" ]] || return 0
  memo_root_trusted || return 0
  [[ ! -e "$MEMO_FILE" || -f "$MEMO_FILE" ]] || return 0
  local tmp
  tmp="$(mktemp "$MEMO_ROOT/.memo.v1.tmp.XXXXXXXX" 2>/dev/null)" || return 0
  if ! python3 - "$MEMO_FILE" "$MEMO_UPDATES" "$tmp" 2>/dev/null <<'PY'
import pathlib
import re
import sys

memo_path, updates_path, output_path = map(pathlib.Path, sys.argv[1:])
oid_pattern = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})")
sha_pattern = re.compile(r"[0-9a-f]{64}")
memo = {}

def load(path, reject_duplicates):
    if not path.exists():
        return
    with path.open("r", encoding="ascii", newline="") as source:
        for raw_line in source:
            if not raw_line.endswith("\n"):
                raise ValueError("unterminated memo line")
            fields = raw_line[:-1].split(" ")
            if (len(fields) != 2 or not oid_pattern.fullmatch(fields[0])
                    or not sha_pattern.fullmatch(fields[1])):
                raise ValueError("malformed memo")
            if reject_duplicates and fields[0] in memo:
                raise ValueError("duplicate memo key")
            memo[fields[0]] = fields[1]

load(memo_path, True)
load(updates_path, False)
with output_path.open("w", encoding="ascii", newline="") as output:
    for oid in sorted(memo):
        output.write(f"{oid} {memo[oid]}\n")
PY
  then
    rm -f -- "$tmp"
    return 0
  fi
  chmod 600 "$tmp" 2>/dev/null || { rm -f -- "$tmp"; return 0; }
  memo_root_trusted || { rm -f -- "$tmp"; return 0; }
  mv -f -- "$tmp" "$MEMO_FILE" 2>/dev/null || rm -f -- "$tmp"
  return 0
}

append_manifest_entry() {
  local manifest="$1"
  local relative="$2"
  local path="$REPOSITORY/$relative"
  [[ -f "$path" ]] \
    || { echo "lean-cache-input: repository input is absent: $path" >&2; return 2; }
  printf '%s\0%s\0' "$relative" "$path" >> "${manifest}.requests"
}

# Lean input preimage v1: root, sorted D5 sources, sorted inspector Lean
# sources; then toolchain, manifest, and lakefiles in their declared order.
lean_cache_address() {
  local sources_manifest="$TMP_ROOT/sources.manifest"
  local sources_list="$TMP_ROOT/sources.list"
  local inspector_sources_list="$TMP_ROOT/inspector-sources.list"
  local config_manifest="$TMP_ROOT/config.manifest"
  local sources_sha256 config_sha256 lakefile_count=0 lakefile

  : > "$sources_manifest"
  : > "${sources_manifest}.requests"
  append_manifest_entry "$sources_manifest" "Trureturing.lean" || return 2
  [[ -d "$REPOSITORY/D5" ]] \
    || { echo "lean-cache-input: managed Lean root is absent: $REPOSITORY/D5" >&2; return 2; }
  find "$REPOSITORY/D5" -type f -name '*.lean' -print | sort > "$sources_list" || return 2
  while IFS= read -r path; do
    append_manifest_entry "$sources_manifest" "${path#"$REPOSITORY/"}" || return 2
  done < "$sources_list"
  if [[ -d "$REPOSITORY/tools/lean-inspector" ]]; then
    find "$REPOSITORY/tools/lean-inspector" -type f -name '*.lean' -print \
      | sort > "$inspector_sources_list" || return 2
    while IFS= read -r path; do
      append_manifest_entry "$sources_manifest" "${path#"$REPOSITORY/"}" || return 2
    done < "$inspector_sources_list"
  fi
  materialize_manifest "$sources_manifest" || return 2
  sources_sha256="$(hash_file "$sources_manifest")" || return 2

  : > "$config_manifest"
  : > "${config_manifest}.requests"
  append_manifest_entry "$config_manifest" "lean-toolchain" || return 2
  append_manifest_entry "$config_manifest" "lake-manifest.json" || return 2
  for lakefile in lakefile.toml lakefile.lean; do
    if [[ -f "$REPOSITORY/$lakefile" ]]; then
      append_manifest_entry "$config_manifest" "$lakefile" || return 2
      lakefile_count=$((lakefile_count + 1))
    fi
  done
  [[ "$lakefile_count" -gt 0 ]] \
    || { echo "lean-cache-input: repository has no lakefile" >&2; return 2; }
  materialize_manifest "$config_manifest" || return 2
  config_sha256="$(hash_file "$config_manifest")" || return 2

  printf '%s %s\n' "$sources_sha256" "$config_sha256"
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  prepare_memo
  lean_cache_address
  store_memo_updates
fi
