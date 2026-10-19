#!/usr/bin/env bash
# Requires Bash, git, and the SDK selected by global.json.
# BASE selects the comparison revision (default origin/dev). PATHS supplies an
# existing NUL-separated manifest instead of computing tracked and untracked changes.
# EMIT_FULL_REPORT explicitly consumes an existing complete report bundle instead
# of producing a scoped report. Its input and material checks remain mandatory.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Scribe/StrataLint.Scribe.csproj"
LEAN_REPORT="$ROOT/.lake/build/stratalint/scoped-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
MODE="${1:-}"

case "$MODE" in
  emit) ;;
  *) echo "usage: scribe.sh emit" >&2; exit 2 ;;
esac

cd "$ROOT"
PATHS_FILE="${PATHS:-}"
TEMP_PATHS=
cleanup() { if [[ -n "$TEMP_PATHS" ]]; then rm -f -- "$TEMP_PATHS"; fi; }
trap cleanup EXIT
if [[ -n "$PATHS_FILE" ]]; then
  [[ -f "$PATHS_FILE" && -r "$PATHS_FILE" ]] || { echo "scribe: PATHS must be a readable regular file" >&2; exit 2; }
else
  command -v git >/dev/null || { echo "scribe: git is required to select changes" >&2; exit 2; }
  TEMP_PATHS="$(mktemp "${TMPDIR:-/tmp}/scribe-paths.XXXXXXXX")"
  PATHS_FILE="$TEMP_PATHS"
  git diff --name-only -z "${BASE:-origin/dev}" -- > "$PATHS_FILE"
  git ls-files --others --exclude-standard -z >> "$PATHS_FILE"
fi

dotnet build "$PROJECT" --configuration Release --nologo --verbosity quiet
SCRIBE_DLL="$ROOT/tools/StrataLint.Scribe/bin/Release/net10.0/StrataLint.Scribe.dll"
consumer_args=(--role scribe-consumer)
emit_args=(--paths-from "$PATHS_FILE")
if [[ -n "${EMIT_FULL_REPORT:-}" ]]; then
  LEAN_REPORT="$EMIT_FULL_REPORT"
  [[ "$LEAN_REPORT" == /* ]] || LEAN_REPORT="$ROOT/$LEAN_REPORT"
  consumer_args+=(--report "$LEAN_REPORT" --validate-materials)
else
  LEAN_TARGETS="$(dotnet "$SCRIBE_DLL" lean-inputs --paths-from "$PATHS_FILE")"
  [[ -n "$LEAN_TARGETS" ]] || { echo 'scribe: Lean input scope is empty' >&2; exit 2; }
  LEAN_TARGETS="${LEAN_TARGETS//$'\n'/ }"
  make lean-report-scoped "LEAN_TARGETS=$LEAN_TARGETS"
  consumer_args+=(--report "$LEAN_REPORT" --targets "$LEAN_TARGETS")
  emit_args+=(--scoped)
fi

run_scribe() {
  local command=(dotnet "$SCRIBE_DLL" "$1")
  if [[ "$1" == "emit" ]]; then
    command+=("${emit_args[@]}")
    "$CONSUMER" "${consumer_args[@]}" -- "${command[@]}"
  else
    "${command[@]}"
  fi
}

run_generator() {
  case "$1" in
    emit|emit-values) run_scribe "$1" ;;
    *) echo "scribe: unknown generator '$1'" >&2; return 2 ;;
  esac
}

generators=(emit emit-values)

for generator in "${generators[@]}"; do run_generator "$generator"; done
