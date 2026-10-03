#!/usr/bin/env bash
# Requires Bash, the SDK selected by global.json, and gh for publish/fetch.
# Usage: scribe-release.sh [publish --target COMMIT [--prefix P]
#        | fetch HEX64 [--prefix P] [--out DIR]]
# SCRIBE_RELEASE_REPO selects OWNER/REPO; GITHUB_REPOSITORY or the project repo
# is the default. gh uses GH_TOKEN or its normal authenticated configuration.
set -euo pipefail

fail() {
  printf 'SCRIBE_RELEASE %s\n' "$2" >&2
  exit "$1"
}

MODE=local PREFIX=scribe-resources DIGEST= TARGET= OUTPUT=
if [[ "$#" -gt 0 ]]; then
  MODE="$1"
  shift
  case "$MODE" in
    publish) ;;
    fetch)
      [[ "$#" -gt 0 ]] || fail 2 'InvalidArguments: fetch requires HEX64'
      DIGEST="$1"
      shift
      [[ "$DIGEST" =~ ^[0-9a-f]{64}$ ]] || fail 2 'InvalidDigest: requires 64 lowercase hexadecimal characters'
      ;;
    *) fail 2 'InvalidArguments: expected publish or fetch' ;;
  esac
fi
seen_prefix=0 seen_target=0 seen_out=0
while [[ "$#" -gt 0 ]]; do
  [[ "$#" -ge 2 && -n "$2" ]] || fail 2 'InvalidArguments: options require a nonempty value'
  case "$1" in
    --prefix)
      [[ "$seen_prefix" -eq 0 ]] || fail 2 'InvalidArguments: duplicate --prefix'
      PREFIX="$2"; seen_prefix=1 ;;
    --target)
      [[ "$MODE" == publish && "$seen_target" -eq 0 ]] || fail 2 'InvalidArguments: unexpected or duplicate --target'
      TARGET="$2"; seen_target=1 ;;
    --out)
      [[ "$MODE" == fetch && "$seen_out" -eq 0 ]] || fail 2 'InvalidArguments: unexpected or duplicate --out'
      OUTPUT="$2"; seen_out=1 ;;
    *) fail 2 'InvalidArguments: unknown option' ;;
  esac
  shift 2
done
[[ "$PREFIX" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ && "$PREFIX" != *..* ]] \
  || fail 2 'InvalidPrefix: requires a release-name prefix without consecutive dots'
[[ "$MODE" != publish || "$TARGET" =~ ^[0-9a-f]{40}$ ]] \
  || fail 2 'InvalidTarget: publish requires --target with a 40-hex commit'
REPO="${SCRIBE_RELEASE_REPO:-${GITHUB_REPOSITORY:-the-omega-institute/trureturing}}"
[[ "$REPO" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] || fail 2 'InvalidRepositoryName: requires OWNER/REPO'
command -v dotnet >/dev/null 2>&1 || fail 2 'MissingTool: dotnet'
if [[ "$MODE" != local ]]; then
  command -v gh >/dev/null 2>&1 || fail 2 'MissingTool: gh'
fi
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj"
[[ -f "$ROOT/global.json" && -f "$PROJECT" && -d "$ROOT/Blueprint" ]] \
  || fail 2 'InvalidRepository: global.json, Blueprint and the documents host are required'
cd "$ROOT"
dotnet --version >/dev/null || fail 2 'SdkUnavailable: install the SDK selected by global.json'
DIRECTORY="$ROOT/Generated/scribe-release"
ASSET=scribe-resources.zip
TEMP_DIRECTORY= DRAFT_TAG=
cleanup() {
  local rc="$?"
  trap - EXIT
  if [[ -n "$DRAFT_TAG" ]]; then
    TAG="$DRAFT_TAG"
    RELEASE_STATE_CLEANUP=1
    if release_state; then
      case "$STATE" in
        true)
          gh release delete "$DRAFT_TAG" --repo "$REPO" --yes \
            || { printf 'SCRIBE_RELEASE DraftCleanupFailed tag=%s\n' "$DRAFT_TAG" >&2; rc=1; }
          ;;
        false|missing) ;;
      esac
    else
      printf 'SCRIBE_RELEASE DraftCleanupFailed tag=%s\n' "$DRAFT_TAG" >&2
      rc=1
    fi
  fi
  if [[ -n "$TEMP_DIRECTORY" ]]; then rm -rf -- "$TEMP_DIRECTORY" || rc=1; fi
  exit "$rc"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

run_scribe() {
  dotnet run --project "$PROJECT" --configuration Release -- "$@"
}

release_state() {
  local response rc
  if response="$(gh release view "$TAG" --repo "$REPO" --json isDraft --jq .isDraft 2>&1)"; then
    case "$response" in
      true|false) STATE="$response" ;;
      *)
        if [[ "${RELEASE_STATE_CLEANUP:-0}" == 1 ]]; then
          return 1
        fi
        fail 1 "InvalidReleaseMetadata: tag=$TAG"
        ;;
    esac
  else
    rc="$?"
    case "$response" in
      *'release not found'*|*'(HTTP 404)'*) STATE=missing ;;
      *)
        if [[ "${RELEASE_STATE_CLEANUP:-0}" == 1 ]]; then
          return "$rc"
        fi
        printf '%s\n' "$response" >&2
        fail "$rc" "ReleaseQueryFailed: tag=$TAG"
        ;;
    esac
  fi
}

verify_pack() {
  local result
  result="$(run_scribe resources verify --pack "$1")" || fail "$?" 'PackVerificationFailed'
  printf '%s\n' "$result"
  [[ "$result" =~ totalSha256=([0-9a-f]{64})([[:space:]]|$) ]] \
    || fail 1 'MissingTotalSha256: resources verify must report the verified manifest digest'
  [[ "${BASH_REMATCH[1]}" == "$DIGEST" ]] || fail 1 "DigestMismatch: expected=$DIGEST"
}

download_pack() {
  TEMP_DIRECTORY="$(mktemp -d "${TMPDIR:-/tmp}/scribe-resources.XXXXXXXX")" || fail "$?" 'TemporaryDirectoryFailed'
  gh release download "$TAG" --repo "$REPO" --pattern "$ASSET" --dir "$TEMP_DIRECTORY" \
    || fail "$?" "DownloadFailed: tag=$TAG"
  verify_pack "$TEMP_DIRECTORY/$ASSET"
}

if [[ "$MODE" == fetch ]]; then
  TAG="$PREFIX-$DIGEST"
  OUTPUT="${OUTPUT:-$ROOT/Generated/scribe-resources/$DIGEST}"
  if [[ -f "$OUTPUT/$ASSET" ]]; then
    verify_pack "$OUTPUT/$ASSET"
  else
    release_state
    [[ "$STATE" != missing ]] || fail 1 "ReleaseNotFound: tag=$TAG"
    [[ "$STATE" == false ]] || fail 1 "ReleaseNotPublished: tag=$TAG"
    download_pack
    mkdir -p -- "$OUTPUT" || fail "$?" 'OutputDirectoryFailed'
    mv -- "$TEMP_DIRECTORY/$ASSET" "$OUTPUT/$ASSET" || fail "$?" 'PackInstallFailed'
  fi
  OUTPUT="$(cd "$OUTPUT" && pwd -P)" || fail "$?" 'OutputDirectoryFailed'
  printf 'SCRIBE_RELEASE fetched file=%s digest=%s\n' "$OUTPUT/$ASSET" "$DIGEST"
  exit 0
fi

rm -rf -- "$DIRECTORY"
dotnet run --project "$PROJECT" --configuration Release -- \
  resources release --out "$DIRECTORY" || fail "$?" 'ReleaseFailed'
if [[ "$MODE" == local ]]; then
  dotnet run --project "$PROJECT" --configuration Release -- \
    resources verify-release --dir "$DIRECTORY" || fail "$?" 'VerificationFailed'
  printf 'SCRIBE_RELEASE verified %s\n' "$DIRECTORY"
  exit 0
fi
verification="$(run_scribe resources verify-release --dir "$DIRECTORY")" || fail "$?" 'VerificationFailed'
printf '%s\n' "$verification"
[[ "$verification" =~ totalSha256=([0-9a-f]{64})([[:space:]]|$) ]] \
  || fail 1 'MissingTotalSha256: resources verify-release must report the verified manifest digest'
DIGEST="${BASH_REMATCH[1]}"
TAG="$PREFIX-$DIGEST"
release_state
if [[ "$STATE" == false ]]; then
  download_pack
  printf 'SCRIBE_RELEASE reused tag=%s digest=%s\n' "$TAG" "$DIGEST"
  exit 0
fi
if [[ "$STATE" == true ]]; then
  gh release delete "$TAG" --repo "$REPO" --yes || fail "$?" "DraftDeleteFailed: tag=$TAG"
fi
DRAFT_TAG="$TAG"
printf 'SCRIBE_RELEASE draft-requested tag=%s digest=%s\n' "$TAG" "$DIGEST"
gh release create "$TAG" --repo "$REPO" --draft --target "$TARGET" --title "$TAG" \
  --notes 'Verified Scribe resource pack.' --latest=false || fail "$?" "DraftCreateFailed: tag=$TAG"
printf 'SCRIBE_RELEASE draft-created tag=%s digest=%s\n' "$TAG" "$DIGEST"
gh release upload "$TAG" "$DIRECTORY/$ASSET" --repo "$REPO" || fail "$?" "UploadFailed: tag=$TAG"
download_pack
gh release edit "$TAG" --repo "$REPO" --draft=false --latest=false || fail "$?" "PublicationFailed: tag=$TAG"
DRAFT_TAG=
printf 'SCRIBE_RELEASE published tag=%s digest=%s\n' "$TAG" "$DIGEST"
