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

append_manifest_entry() {
  local manifest="$1"
  local relative="$2"
  local path="$REPOSITORY/$relative"
  [[ -f "$path" ]] \
    || { echo "lean-report-input: repository input is absent: $path" >&2; return 2; }
  printf '%s  %s\n' "$(hash_file "$path")" "$relative" >> "$manifest"
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
  printf '%s  %s\n' "$(hash_file "$path")" "$relative" >> "$manifest"
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
    r"(?P<path>(?:\$[A-Z_][A-Z0-9_]*|\$\{[A-Z_][A-Z0-9_]*\}|[A-Za-z0-9_.-]+)"
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
  local producer_paths="$TMP_ROOT/producer-paths"
  local closure_complete=1
  if ! complete_producer_paths > "$producer_paths"; then
    closure_complete=0
    producer_declared_paths | sort -u > "$producer_paths"
  fi
  while IFS= read -r relative; do
    append_producer_manifest_entry "${manifest}.unsorted" "$relative" || return 2
  done < "$producer_paths"
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

  resident_sha256="$(producer_sha256 "$resident_manifest")"

  : > "$sources_manifest"
  append_manifest_entry "$sources_manifest" "Trureturing.lean"
  [[ -d "$REPOSITORY/D5" ]] \
    || { echo "lean-report-input: managed Lean root is absent: $REPOSITORY/D5" >&2; return 2; }
  find "$REPOSITORY/D5" -type f -name '*.lean' -print | sort > "$sources_list"
  while IFS= read -r path; do
    append_manifest_entry "$sources_manifest" "${path#"$REPOSITORY/"}"
  done < "$sources_list"
  sources_sha256="$(hash_file "$sources_manifest")"

  : > "$config_manifest"
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
  config_sha256="$(hash_file "$config_manifest")"

  {
    printf '%s\n' "schema=stratalint-lean-report-repository-input-v1"
    printf 'repository_inspector_sha256=%s\n' "$resident_sha256"
    printf 'lean_sources_sha256=%s\n' "$sources_sha256"
    printf 'lean_config_sha256=%s\n' "$config_sha256"
  } > "$preimage"
  printf '%s %s %s %s\n' \
    "$(hash_file "$preimage")" "$resident_sha256" "$sources_sha256" "$config_sha256"
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
