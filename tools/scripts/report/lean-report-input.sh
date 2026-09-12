#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

COMMAND="${1:-}"
if [[ -n "$COMMAND" ]]; then shift; fi
REPOSITORY=""
REPORT=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) REPOSITORY="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    *) echo "lean-report-input: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ "$COMMAND" == "address" || "$COMMAND" == "verify" || "$COMMAND" == "modules" \
  || "$COMMAND" == "compatibility-token" || "$COMMAND" == "scribe-input-patterns" ]] \
  || { echo "usage: lean-report-input.sh address|verify|modules|compatibility-token|scribe-input-patterns --repository DIR [--report FILE]" >&2; exit 2; }
[[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
  || { echo "lean-report-input: --repository requires an absolute directory" >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-input.XXXXXXXX")"
cleanup() { rm -rf -- "$TMP_ROOT"; }
trap cleanup EXIT

SCRIPT_DIRECTORY="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
source "$SCRIPT_DIRECTORY/../worktree/lean-cache-input.sh"

# One canonical, dependency-free reader for the registered manifest. The closed
# TOML subset is documented in the report contract; no SDK/MSBuild evaluation or
# executable-byte discovery participates in report compatibility.
python3 - "$REPOSITORY" "$COMMAND" "$TMP_ROOT" <<'PY' || exit 2
import hashlib
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
command = sys.argv[2]
scratch = pathlib.Path(sys.argv[3])
manifest = "Meta/lean-report.toml"

try:
    text = (root / manifest).read_bytes().decode("utf-8")
    # Selectors cannot contain '#'; comments and whitespace have no identity.
    text = re.sub(r"#[^\n]*", "", text)
    values = {}
    decoder = json.JSONDecoder()
    while text.strip():
        match = re.match(r"\s*([a-z_]+)[ \t]*=[ \t]*", text)
        if match is None:
            raise ValueError("invalid assignment")
        key = match[1]
        if key not in {"compatibility_version", "source_patterns", "scribe_check_inputs"} or key in values:
            raise ValueError(f"unknown or duplicate key: {key}")
        value_text = text[match.end():]
        value, end = decoder.raw_decode(value_text)
        if key == "compatibility_version" and not re.fullmatch(r"[1-9][0-9]*", value_text[:end]):
            raise ValueError("compatibility_version must be a positive decimal integer")
        values[key] = value
        text = value_text[end:]
        if text and not re.match(r"[ \t]*\r?\n", text):
            raise ValueError(f"unexpected bytes after {key}")
    version = values.get("compatibility_version")
    if type(version) is not int or version <= 0:
        raise ValueError("compatibility_version is missing or is not a positive integer")

    def patterns(key):
        items = values.get(key)
        if (not isinstance(items, list) or not items
                or any(not isinstance(item, str) or not item
                       or not re.fullmatch(r"[A-Za-z0-9_./*?-]+", item)
                       or item.startswith("/") or ".." in item.split("/")
                       or "." in item.split("/") or "//" in item for item in items)
                or len(items) != len(set(items))):
            raise ValueError(f"{key} must register unique relative path patterns")
        return items

    sources = patterns("source_patterns")
    token = hashlib.sha256(
        f"schema=stratalint-lean-report-compatibility\nversion={version}\n".encode("utf-8")
    ).hexdigest()
    (scratch / "compatibility").write_text(token + "\n", encoding="ascii")
    if command == "compatibility-token":
        print(token)
    elif command == "scribe-input-patterns":
        try:
            print("\n".join(patterns("scribe_check_inputs")))
        except ValueError as error:
            raise ValueError(f"scribe-content-checks: {error}") from error
    else:
        paths = []
        for pattern in sources:
            selected = sorted((path for path in root.glob(pattern)
                               if path.is_file() and not path.is_symlink()),
                              key=lambda path: path.as_posix().encode("utf-8"))
            if not selected and not any(char in pattern for char in "*?"):
                raise ValueError(f"registered report source is absent: {pattern}")
            paths.extend(path.relative_to(root).as_posix() for path in selected)
        if len(paths) != len(set(paths)):
            raise ValueError("overlapping source_patterns")
        if not paths or any(not path.endswith(".lean") or "\t" in path or "\n" in path for path in paths):
            raise ValueError("source_patterns must select Lean module paths")
        (scratch / "modules").write_text("".join(
            path[:-5].replace("/", ".") + "\t" + path + "\n" for path in paths), encoding="utf-8")
except (OSError, UnicodeError, ValueError) as error:
    print(f"lean-report-input: {manifest} compatibility_version/config invalid: {error}", file=sys.stderr)
    sys.exit(2)
PY

if [[ "$COMMAND" == "verify" ]]; then
  [[ -n "$REPORT" && "$REPORT" == /* && -s "$REPORT" ]] \
    || { echo "lean-report-input: raw Lean report is missing; run make lean-report first" >&2; exit 2; }
fi

# Digest-shaped producer/resident fields are the same version-derived token.
# Report sources exclude Inspector; the Lean config preimage is shared with the
# compiled-cache helper without changing its source scope or configuration.
repository_address() {
  local preimage="$TMP_ROOT/repository-input.preimage"
  local sources_manifest="$TMP_ROOT/report-sources.manifest"
  local resident_sha256 sources_sha256 config_sha256 module path

  resident_sha256="$(cat "$TMP_ROOT/compatibility")" || return 2
  prepare_memo
  : > "${sources_manifest}.requests"
  while IFS=$'\t' read -r module path; do
    append_manifest_entry "$sources_manifest" "$path" || return 2
  done < "$TMP_ROOT/modules"
  materialize_manifest "$sources_manifest" || return 2
  sources_sha256="$(hash_file "$sources_manifest")" || return 2
  config_sha256="$(lean_config_sha256)" || return 2

  {
    printf '%s\n' "schema=stratalint-lean-report-repository-input-v1"
    printf 'repository_inspector_sha256=%s\n' "$resident_sha256"
    printf 'lean_sources_sha256=%s\n' "$sources_sha256"
    printf 'lean_config_sha256=%s\n' "$config_sha256"
  } > "$preimage" || return 2
  local address_sha256
  address_sha256="$(hash_file "$preimage")" || return 2
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
    cat "$TMP_ROOT/modules"
    ;;
  compatibility-token|scribe-input-patterns)
    # Already emitted by the canonical manifest reader above.
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
    producer="${producer#producer_sha256=}"
    address_output="$(repository_address)" || exit 2
    # Validate the complete tuple before read can collapse an empty field.
    address_pattern='^([0-9a-f]{64} ){3}[0-9a-f]{64}$'
    [[ "$address_output" =~ $address_pattern ]] \
      || { echo "lean-report-input: repository address is malformed" >&2; exit 2; }
    IFS=' ' read -r address current_producer current_sources current_config <<< "$address_output"
    [[ "$producer" == "$current_producer" ]] \
      || { echo "lean-report-input: raw Lean report producer is stale for current repository inputs; run make lean-report first" >&2; exit 2; }
    [[ "$declared" == "$address" ]] \
      || { echo "lean-report-input: raw Lean report is stale for current repository inputs; run make lean-report first" >&2; exit 2; }
    ;;
esac
