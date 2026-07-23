#!/usr/bin/env bash
set -euo pipefail

ROOT="${PR_SHEPHERD_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)}"
REMOTE="${PR_SHEPHERD_REMOTE:-origin}"
REPO="${PR_SHEPHERD_REPO:-the-omega-institute/trureturing}"
LOG="${PR_SHEPHERD_LOG:-$HOME/.pr-shepherd.log}"
SCRIBE_PROJECT="$ROOT/Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj"

NUM="${1:-}"
HEAD_REF="${2:-}"
EXPECTED_HEAD="${3:-}"
EXPECTED_BASE="${4:-}"
CROSS_REPOSITORY="${5:-}"

GH() { LEAN4_GUARDRAILS_BYPASS=1 gh "$@"; }

log() { printf '%s %s\n' "$(date '+%F %T')" "$*" | tee -a "$LOG" >&2; }

fail() {
  log "RECONCILE #$NUM refused: $*"
  return 1
}

is_generated_artifact() {
  local candidate="$1" artifact
  for artifact in "${GENERATED_ARTIFACTS[@]}"; do
    [[ "$candidate" == "$artifact" ]] && return 0
  done
  return 1
}

is_executor_path() {
  case "$1" in
    .fkst/*|.github/*|Meta/StrataLint/*|Makefile|global.json|Directory.Build.*|Directory.Packages.*|*NuGet.Config|*nuget.config|lean-toolchain|lakefile.toml|lake-manifest.json) return 0 ;;
    *) return 1 ;;
  esac
}

credentialless() {
  local isolated_home="$1"
  shift
  env \
    -u GH_TOKEN \
    -u GITHUB_TOKEN \
    -u GITHUB_PAT \
    -u SSH_AUTH_SOCK \
    -u SSH_AGENT_PID \
    -u GIT_ASKPASS \
    HOME="$isolated_home" \
    GH_CONFIG_DIR="$isolated_home/gh" \
    XDG_CONFIG_HOME="$isolated_home/config" \
    XDG_CACHE_HOME="$isolated_home/cache" \
    DOTNET_CLI_HOME="$isolated_home/dotnet" \
    NUGET_PACKAGES="${NUGET_PACKAGES:-${ORIGINAL_HOME}/.nuget/packages}" \
    ELAN_HOME="${ELAN_HOME:-${ORIGINAL_HOME}/.elan}" \
    GIT_CONFIG_GLOBAL=/dev/null \
    GIT_CONFIG_NOSYSTEM=1 \
    GIT_TERMINAL_PROMPT=0 \
    GCM_INTERACTIVE=Never \
    "$@"
}

[[ "$NUM" =~ ^[1-9][0-9]*$ ]] || { echo "usage: pr-reconcile.sh NUM HEAD HEAD_OID BASE_OID CROSS_REPOSITORY" >&2; exit 2; }
[[ "$EXPECTED_HEAD" =~ ^[0-9a-f]{40}$ ]] || { echo "pr-reconcile: invalid expected head OID" >&2; exit 2; }
[[ "$EXPECTED_BASE" =~ ^[0-9a-f]{40}$ ]] || { echo "pr-reconcile: invalid expected base OID" >&2; exit 2; }
[[ "$CROSS_REPOSITORY" == "true" || "$CROSS_REPOSITORY" == "false" ]] \
  || { echo "pr-reconcile: invalid cross-repository flag" >&2; exit 2; }
git check-ref-format --branch "$HEAD_REF" >/dev/null \
  || { echo "pr-reconcile: invalid head branch" >&2; exit 2; }

TEMP_ROOT=""
WORKSPACE=""
cleanup() {
  if [[ -n "$WORKSPACE" ]]; then
    git -C "$ROOT" worktree remove --force "$WORKSPACE" >/dev/null 2>&1 || true
  fi
  [[ -z "$TEMP_ROOT" ]] || rm -rf "$TEMP_ROOT"
}
trap cleanup EXIT HUP INT TERM

remote_head="$(git -C "$ROOT" ls-remote --refs "$REMOTE" "refs/heads/$HEAD_REF" | cut -f1)"
remote_base="$(git -C "$ROOT" ls-remote --refs "$REMOTE" refs/heads/dev | cut -f1)"
[[ "$remote_head" == "$EXPECTED_HEAD" ]] || { fail "head changed before reconciliation"; exit 1; }
[[ "$remote_base" == "$EXPECTED_BASE" ]] || { fail "base changed before reconciliation"; exit 1; }
git -C "$ROOT" fetch --no-tags "$REMOTE" refs/heads/dev "refs/heads/$HEAD_REF" >/dev/null
git -C "$ROOT" cat-file -e "$EXPECTED_HEAD^{commit}" \
  || { fail "expected head commit is unavailable"; exit 1; }
git -C "$ROOT" cat-file -e "$EXPECTED_BASE^{commit}" \
  || { fail "expected base commit is unavailable"; exit 1; }

TEMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/pr-shepherd-$NUM.XXXXXXXX")"
inventory="$TEMP_ROOT/generated-artifacts"
if ! (cd "$ROOT" && dotnet run \
  --project "$SCRIBE_PROJECT" \
  --configuration Release \
  -- artifact-inventory --null) > "$inventory"; then
  fail "base-owned generated artifact inventory failed"
  exit 1
fi

GENERATED_ARTIFACTS=()
while IFS= read -r -d '' artifact; do
  [[ -n "$artifact" ]] || { fail "generated artifact inventory contains an empty path"; exit 1; }
  GENERATED_ARTIFACTS+=("$artifact")
done < "$inventory"
[[ "${#GENERATED_ARTIFACTS[@]}" -gt 0 ]] \
  || { fail "generated artifact inventory is empty"; exit 1; }

generated_change=0
unsafe_path=""
while IFS= read -r -d '' path; do
  if is_generated_artifact "$path"; then
    generated_change=1
  elif is_executor_path "$path"; then
    unsafe_path="$path"
    break
  fi
done < <(git -C "$ROOT" diff --name-only --no-renames -z "$EXPECTED_BASE...$EXPECTED_HEAD")

if [[ "$generated_change" -eq 0 ]]; then
  log "RECONCILE #$NUM not applicable: PR changes no registered generated artifact"
  exit 3
fi
[[ "$CROSS_REPOSITORY" == "false" ]] \
  || { fail "cross-repository content writeback has no same-repository lease target"; exit 1; }
[[ -z "$unsafe_path" ]] \
  || { fail "content reconciliation cannot execute a candidate-owned harness path: $unsafe_path"; exit 1; }

WORKSPACE="$TEMP_ROOT/worktree"
git -C "$ROOT" worktree add --detach "$WORKSPACE" "$EXPECTED_HEAD" >/dev/null
merge_output="$TEMP_ROOT/merge-output"
if ! git -C "$WORKSPACE" \
  -c core.hooksPath=/dev/null \
  -c user.name=pr-shepherd \
  -c user.email=pr-shepherd@users.noreply.github.com \
  merge --no-edit -m "Merge dev into $HEAD_REF (pr-shepherd)" "$EXPECTED_BASE" \
  > "$merge_output" 2>&1; then
  git -C "$WORKSPACE" merge --abort >/dev/null 2>&1 || true
  fail "semantic merge conflict; no derivation or writeback performed"
  exit 1
fi
merged_head="$(git -C "$WORKSPACE" rev-parse HEAD)"

ORIGINAL_HOME="${HOME:-/tmp}"
isolated_home="$TEMP_ROOT/credentialless-home"
mkdir -p "$isolated_home"
if ! credentialless "$isolated_home" make -C "$WORKSPACE" --no-print-directory lean-report; then
  fail "lean-report derivation failed"
  exit 1
fi
if ! credentialless "$isolated_home" make -C "$WORKSPACE" --no-print-directory emit; then
  fail "Scribe emission failed"
  exit 1
fi
if ! credentialless "$isolated_home" make -C "$WORKSPACE" --no-print-directory ingest "BASE=$EXPECTED_BASE"; then
  fail "residual ingestion failed"
  exit 1
fi
projection="$TEMP_ROOT/echo-residual-summary.md"
if ! credentialless "$isolated_home" make -C "$WORKSPACE" --no-print-directory \
  echo-residual-summary "BASE=$EXPECTED_BASE" > "$projection"; then
  fail "echo residual derivation failed"
  exit 1
fi
mkdir -p "$WORKSPACE/Generated"
mv "$projection" "$WORKSPACE/Generated/echo-residual-summary.md"
[[ "$(git -C "$WORKSPACE" rev-parse HEAD)" == "$merged_head" ]] \
  || { fail "candidate producer changed HEAD during derivation"; exit 1; }

changes="$TEMP_ROOT/changed-paths"
git -C "$WORKSPACE" diff --name-only --no-renames -z > "$changes"
git -C "$WORKSPACE" diff --cached --name-only --no-renames -z >> "$changes"
git -C "$WORKSPACE" ls-files --others --exclude-standard -z >> "$changes"
allowed_changes=()
while IFS= read -r -d '' path; do
  if is_generated_artifact "$path" \
    || [[ "$path" == "Meta/BACKFILL.yaml" ]] \
    || [[ "$path" == Meta/Digestion/atoms/* ]]; then
    allowed_changes+=("$path")
  else
    fail "producer touched a path outside the derivation whitelist: $path"
    exit 1
  fi
done < "$changes"

if [[ "${#allowed_changes[@]}" -gt 0 ]]; then
  git -C "$WORKSPACE" -c core.hooksPath=/dev/null add -- "${allowed_changes[@]}"
  git -C "$WORKSPACE" \
    -c core.hooksPath=/dev/null \
    -c user.name=pr-shepherd \
    -c user.email=pr-shepherd@users.noreply.github.com \
    commit -m "chore(derived): rederive after dev merge" >/dev/null
fi

live="$(GH pr view "$NUM" --repo "$REPO" \
  --json headRefOid,baseRefOid,headRefName,isCrossRepository \
  --jq '[.headRefOid,.baseRefOid,.headRefName,.isCrossRepository] | @tsv')"
IFS=$'\t' read -r live_head live_base live_ref live_cross <<< "$live"
if [[ "$live_head" != "$EXPECTED_HEAD" \
  || "$live_base" != "$EXPECTED_BASE" \
  || "$live_ref" != "$HEAD_REF" \
  || "$live_cross" != "$CROSS_REPOSITORY" ]]; then
  fail "head or base changed during reconciliation"
  exit 1
fi

GH auth setup-git >/dev/null
if ! git -C "$WORKSPACE" -c core.hooksPath=/dev/null push \
  "--force-with-lease=refs/heads/$HEAD_REF:$EXPECTED_HEAD" \
  "$REMOTE" "HEAD:refs/heads/$HEAD_REF"; then
  fail "expected-head lease rejected writeback"
  exit 1
fi

new_head="$(git -C "$WORKSPACE" rev-parse HEAD)"
log "RECONCILE #$NUM merged base=$EXPECTED_BASE rederived registered artifacts head=$new_head"
