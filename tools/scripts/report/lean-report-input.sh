#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

COMMAND="${1:-}"
if [[ -n "$COMMAND" ]]; then shift; fi
REPOSITORY=""
REPORT=""
PRODUCER_OVERRIDE=""
INSPECTOR_OVERRIDE=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) REPOSITORY="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    --producer) PRODUCER_OVERRIDE="$2"; shift 2 ;;
    --inspector) INSPECTOR_OVERRIDE="$2"; shift 2 ;;
    *) echo "lean-report-input: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ "$COMMAND" == "address" || "$COMMAND" == "verify" || "$COMMAND" == "modules" \
  || "$COMMAND" == "producer-paths" || "$COMMAND" == "scribe-producer-paths" ]] \
  || { echo "usage: lean-report-input.sh address|verify|modules|producer-paths|scribe-producer-paths --repository DIR [--report FILE] [--producer FILE] [--inspector FILE]" >&2; exit 2; }
[[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
  || { echo "lean-report-input: --repository requires an absolute directory" >&2; exit 2; }
[[ -z "$PRODUCER_OVERRIDE" || ( "$PRODUCER_OVERRIDE" == /* && -f "$PRODUCER_OVERRIDE" ) ]] \
  || { echo "lean-report-input: --producer requires an absolute file" >&2; exit 2; }
[[ -z "$INSPECTOR_OVERRIDE" || ( "$INSPECTOR_OVERRIDE" == /* && -f "$INSPECTOR_OVERRIDE" ) ]] \
  || { echo "lean-report-input: --inspector requires an absolute file" >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
if [[ "$COMMAND" == "verify" ]]; then
  [[ -n "$REPORT" && "$REPORT" == /* && -s "$REPORT" ]] \
    || { echo "lean-report-input: raw Lean report is missing; run make lean-report first" >&2; exit 2; }
fi

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-input.XXXXXXXX")"
cleanup() { rm -rf -- "$TMP_ROOT"; }
trap cleanup EXIT

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
    "$plan" "$live_paths" <<'PY'
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

  hash_files_batch "$live_paths" "$live_hashes"
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
    || { echo "lean-report-input: repository input is absent: $path" >&2; return 2; }
  printf '%s\0%s\0' "$relative" "$path" >> "${manifest}.requests"
}

append_producer_manifest_entry() {
  local manifest="$1"
  local relative="$2"
  local path="$REPOSITORY/$relative"
  if [[ "$relative" == "tools/lean-inspector/inspect.sh" && -n "$PRODUCER_OVERRIDE" ]]; then
    path="$PRODUCER_OVERRIDE"
  elif [[ "$relative" == "tools/lean-inspector/Inspector.lean" && -n "$INSPECTOR_OVERRIDE" ]]; then
    path="$INSPECTOR_OVERRIDE"
  fi
  [[ -f "$path" ]] \
    || { echo "lean-report-input: repository input is absent: $path" >&2; return 2; }
  printf '%s\0%s\0' "$relative" "$path" >> "${manifest}.requests"
}

producer_declared_paths() {
  local relative
  for relative in \
    tools/StrataLint.Cli/StrataLint.Cli.csproj \
    tools/StrataLint.Engine/StrataLint.Engine.csproj \
    tools/Trureturing.Truth/Trureturing.Truth.csproj \
    Directory.Build.props \
    Directory.Build.targets \
    Directory.Packages.props \
    tools/lean-inspector/inspect.sh \
    tools/lean-inspector/Inspector.lean \
    tools/lean-inspector/delta.py \
    tools/lean-inspector/materials.py \
    tools/scripts/report/lean-report-input.sh \
    tools/scripts/lean-report-pair.sh \
    tools/StrataLint.Engine/packages.lock.json \
    tools/StrataLint.Cli/packages.lock.json \
    tools/Trureturing.Truth/packages.lock.json \
    global.json; do
    if [[ -f "$REPOSITORY/$relative" \
      || ( "$relative" == "tools/lean-inspector/inspect.sh" && -n "$PRODUCER_OVERRIDE" ) \
      || ( "$relative" == "tools/lean-inspector/Inspector.lean" && -n "$INSPECTOR_OVERRIDE" ) ]]; then
      printf '%s\n' "$relative"
    fi
  done
}

producer_reachable_script_paths() {
  local scope="${1:-lean-report}"
  python3 - "$REPOSITORY" "$scope" <<'PY'
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1]).resolve()
scope = sys.argv[2]
if scope == "lean-report":
    entrypoints = (
        pathlib.PurePosixPath(".github/workflows/ci.yml"),
        pathlib.PurePosixPath("tools/lean-inspector/inspect.sh"),
        pathlib.PurePosixPath("tools/scripts/lean-report-pair.sh"),
        pathlib.PurePosixPath("tools/scripts/report/lean-report-input.sh"),
    )
elif scope == "scribe-content":
    entrypoints = (
        pathlib.PurePosixPath(".github/workflows/ci.yml"),
        pathlib.PurePosixPath("tools/scripts/workflow/scribe-content-checks.sh"),
    )
else:
    raise SystemExit(f"lean-report-input: unknown producer scope: {scope}")
reference_pattern = re.compile(
    r"(?P<path>(?:\$[A-Za-z_][A-Za-z0-9_]*|\$\{[A-Za-z_][A-Za-z0-9_]*\}|[A-Za-z0-9_.-]+)"
    r"(?:/[A-Za-z0-9_.$@{}+-]+)+\.sh)(?![A-Za-z0-9_.])"
)


def source_text(relative):
    path = root.joinpath(*relative.parts).resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise SystemExit(f"lean-report-input: producer script escaped repository: {relative}") from error
    if not path.is_file():
        raise SystemExit(f"lean-report-input: reachable producer input is absent: {relative}")
    text = path.read_text(encoding="utf-8")
    if relative == pathlib.PurePosixPath(".github/workflows/ci.yml"):
        start_marker = "  lean-inspect:\n"
        end_marker = "  baseline-admission:\n"
        if start_marker not in text or end_marker not in text:
            raise SystemExit("lean-report-input: Lean-report workflow job boundaries are absent")
        text = text[text.index(start_marker):text.index(end_marker)]
    return text


def normalize(reference, source):
    if "/candidate/" in reference:
        reference = reference.split("/candidate/", 1)[1]
    elif reference.startswith("candidate/"):
        reference = reference[len("candidate/"):]
    elif reference.startswith("$"):
        reference = reference.split("/", 1)[1]
        if reference.startswith("candidate/"):
            reference = reference[len("candidate/"):]
    if reference.startswith(("tools/", ".github/")):
        candidate = pathlib.PurePosixPath(reference)
    else:
        candidate = source.parent.joinpath(pathlib.PurePosixPath(reference))
    normalized = pathlib.PurePosixPath(pathlib.PurePosixPath(candidate).as_posix())
    parts = []
    for part in normalized.parts:
        if part in ("", "."):
            continue
        if part == "..":
            if not parts:
                raise SystemExit(f"lean-report-input: producer script escaped repository: {reference}")
            parts.pop()
        else:
            parts.append(part)
    return pathlib.PurePosixPath(*parts)


pending = list(entrypoints)
reachable = set()
while pending:
    source = pending.pop()
    if source in reachable:
        continue
    text = source_text(source)
    reachable.add(source)
    for match in reference_pattern.finditer(text):
        if text[max(0, match.start() - 3):match.start()] == "://":
            continue
        referenced = normalize(match.group("path"), source)
        if referenced not in reachable:
            pending.append(referenced)

for relative in sorted(reachable, key=lambda path: path.as_posix().encode("utf-8")):
    print(relative.as_posix())
PY
}

producer_compile_paths() {
  local scope="${1:-lean-report}"
  local project json
  local projects=()
  if [[ "$scope" == "lean-report" ]]; then
    projects=(
      tools/StrataLint.Cli/StrataLint.Cli.csproj
      tools/StrataLint.Engine/StrataLint.Engine.csproj
      tools/Trureturing.Truth/Trureturing.Truth.csproj)
  elif [[ "$scope" == "scribe-content" ]]; then
    projects=(
      tools/StrataLint.Scribe/StrataLint.Scribe.csproj
      tools/StrataLint.Engine/StrataLint.Engine.csproj
      tools/Trureturing.Truth/Trureturing.Truth.csproj)
  else
    return 1
  fi
  for project in "${projects[@]}"; do
    [[ -f "$REPOSITORY/$project" ]] || return 1
    json="$TMP_ROOT/$(basename "$project").compile.json"
    dotnet msbuild "$REPOSITORY/$project" -getItem:Compile \
      -verbosity:quiet -nologo > "$json" 2>/dev/null || return 1
    python3 - "$REPOSITORY" "$json" <<'PY' || return 1
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve()
items = json.loads(pathlib.Path(sys.argv[2]).read_text(encoding="utf-8"))["Items"]["Compile"]
if not items:
    raise SystemExit(1)
for item in items:
    path = pathlib.Path(item["FullPath"]).resolve()
    try:
        relative = path.relative_to(root)
    except ValueError:
        raise SystemExit(1)
    if not path.is_file():
        raise SystemExit(1)
    print(relative.as_posix())
PY
  done
}

complete_producer_paths() {
  local compile_paths="$TMP_ROOT/producer-compile-paths"
  local script_paths="$TMP_ROOT/producer-script-paths"
  producer_compile_paths lean-report > "$compile_paths" || return 1
  producer_reachable_script_paths lean-report > "$script_paths" || return 1
  { cat "$compile_paths"; cat "$script_paths"; producer_declared_paths; } | sort -u
}

scribe_declared_paths() {
  local relative
  for relative in \
    tools/StrataLint.Scribe/StrataLint.Scribe.csproj \
    tools/StrataLint.Scribe/packages.lock.json; do
    [[ -f "$REPOSITORY/$relative" ]] && printf '%s\n' "$relative"
  done
}

complete_scribe_producer_paths() {
  local compile_paths="$TMP_ROOT/scribe-compile-paths"
  local script_paths="$TMP_ROOT/scribe-script-paths"
  local lean_paths="$TMP_ROOT/lean-producer-paths"
  producer_compile_paths scribe-content > "$compile_paths" || return 1
  producer_reachable_script_paths scribe-content > "$script_paths" || return 1
  complete_producer_paths > "$lean_paths" || return 1
  {
    cat "$compile_paths"
    cat "$script_paths"
    cat "$lean_paths"
    scribe_declared_paths
  } | sort -u
}

producer_sha256() {
  local manifest="$1"
  local relative
  : > "$manifest"
  : > "${manifest}.unsorted"
  : > "${manifest}.unsorted.requests"
  local producer_paths="$TMP_ROOT/producer-paths"
  local closure_complete=1
  if ! complete_producer_paths > "$producer_paths"; then
    closure_complete=0
    producer_declared_paths | sort -u > "$producer_paths"
  fi
  while IFS= read -r relative; do
    append_producer_manifest_entry "${manifest}.unsorted" "$relative" || return 2
  done < "$producer_paths"
  materialize_manifest "${manifest}.unsorted"
  if [[ "$closure_complete" == "0" ]]; then
    printf '%s\n' "unavailable:candidate" >> "${manifest}.unsorted"
  fi
  sort "${manifest}.unsorted" > "$manifest"
  rm -f -- "${manifest}.unsorted"
  hash_file "$manifest"
}

managed_modules() {
  [[ -f "$REPOSITORY/Trureturing.lean" && -d "$REPOSITORY/D5" ]] \
    || { echo "lean-report-input: managed Lean roots are absent" >&2; return 2; }
  printf 'Trureturing\tTrureturing.lean\n'
  find "$REPOSITORY/D5" -type f -name '*.lean' -print \
    | sed "s#^$REPOSITORY/##" \
    | sort \
    | while IFS= read -r path; do
        module="${path%.lean}"
        printf '%s\t%s\n' "${module//\//.}" "$path"
      done
}

repository_address() {
  local resident_manifest="$TMP_ROOT/resident-inspector.manifest"
  local sources_manifest="$TMP_ROOT/sources.manifest"
  local sources_list="$TMP_ROOT/sources.list"
  local config_manifest="$TMP_ROOT/config.manifest"
  local preimage="$TMP_ROOT/repository-input.preimage"
  local resident_sha256 sources_sha256 config_sha256 lakefile_count=0 lakefile

  prepare_memo
  resident_sha256="$(producer_sha256 "$resident_manifest")"

  : > "$sources_manifest"
  : > "${sources_manifest}.requests"
  append_manifest_entry "$sources_manifest" "Trureturing.lean"
  [[ -d "$REPOSITORY/D5" ]] \
    || { echo "lean-report-input: managed Lean root is absent: $REPOSITORY/D5" >&2; return 2; }
  find "$REPOSITORY/D5" -type f -name '*.lean' -print | sort > "$sources_list"
  while IFS= read -r path; do
    append_manifest_entry "$sources_manifest" "${path#"$REPOSITORY/"}"
  done < "$sources_list"
  materialize_manifest "$sources_manifest"
  sources_sha256="$(hash_file "$sources_manifest")"

  : > "$config_manifest"
  : > "${config_manifest}.requests"
  append_manifest_entry "$config_manifest" "lean-toolchain"
  append_manifest_entry "$config_manifest" "lake-manifest.json"
  for lakefile in lakefile.toml lakefile.lean; do
    if [[ -f "$REPOSITORY/$lakefile" ]]; then
      append_manifest_entry "$config_manifest" "$lakefile"
      lakefile_count=$((lakefile_count + 1))
    fi
  done
  [[ "$lakefile_count" -gt 0 ]] \
    || { echo "lean-report-input: repository has no lakefile" >&2; return 2; }
  materialize_manifest "$config_manifest"
  config_sha256="$(hash_file "$config_manifest")"

  {
    printf '%s\n' "schema=stratalint-lean-report-repository-input-v1"
    printf 'repository_inspector_sha256=%s\n' "$resident_sha256"
    printf 'lean_sources_sha256=%s\n' "$sources_sha256"
    printf 'lean_config_sha256=%s\n' "$config_sha256"
  } > "$preimage"
  local address_sha256
  address_sha256="$(hash_file "$preimage")"
  store_memo_updates
  printf '%s %s %s %s\n' \
    "$address_sha256" "$resident_sha256" "$sources_sha256" "$config_sha256"
}

verify_report_sha() {
  local declared="" declared_name="" actual
  [[ -f "${REPORT}.sha256" ]] \
    || { echo "lean-report-input: report SHA is missing; run make lean-report first" >&2; return 2; }
  read -r declared declared_name < "${REPORT}.sha256" || true
  actual="$(hash_file "$REPORT")"
  [[ "$declared" =~ ^[0-9a-f]{64}$ \
    && "$declared" == "$actual" \
    && "$declared_name" == "$(basename "$REPORT")" \
    && "$(awk 'END {print NR}' "${REPORT}.sha256")" == "1" ]] \
    || { echo "lean-report-input: raw Lean report SHA is stale; run make lean-report first" >&2; return 2; }
  REPORT_SHA256="$actual"
}

case "$COMMAND" in
  address)
    repository_address
    ;;
  modules)
    managed_modules
    ;;
  producer-paths)
    complete_producer_paths \
      || { echo "lean-report-input: producer compile closure is unavailable" >&2; exit 2; }
    ;;
  scribe-producer-paths)
    complete_scribe_producer_paths \
      || { echo "lean-report-input: Scribe producer closure is unavailable" >&2; exit 2; }
    ;;
  verify)
    verify_report_sha
    [[ -f "${REPORT}.input.attestation" ]] \
      || { echo "lean-report-input: production input attestation is missing; run make lean-report first" >&2; exit 2; }
    schema=""
    declared=""
    producer=""
    attested_report=""
    extra=""
    {
      IFS= read -r schema || true
      IFS= read -r declared || true
      IFS= read -r producer || true
      IFS= read -r attested_report || true
      IFS= read -r extra || true
    } < "${REPORT}.input.attestation"
    [[ "$schema" == "schema=stratalint-lean-report-input-attestation-v1" ]] \
      || { echo "lean-report-input: production input attestation is malformed or stale; run make lean-report first" >&2; exit 2; }
    [[ "$declared" =~ ^repository_input_sha256=[0-9a-f]{64}$ \
      && "$producer" =~ ^producer_sha256=[0-9a-f]{64}$ \
      && "$attested_report" == "report_sha256=$REPORT_SHA256" \
      && -z "$extra" ]] \
      || { echo "lean-report-input: production input attestation is malformed or stale; run make lean-report first" >&2; exit 2; }
    declared="${declared#repository_input_sha256=}"
    read -r address _ <<< "$(repository_address)"
    [[ "$declared" == "$address" ]] \
      || { echo "lean-report-input: raw Lean report is stale for current repository inputs; run make lean-report first" >&2; exit 2; }
    ;;
esac
