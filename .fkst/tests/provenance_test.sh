#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
temporary=""

die() {
  printf 'provenance test: %s\n' "$*" >&2
  exit 1
}

cleanup() {
  if [[ -n "${temporary:-}" ]]; then
    rm -rf -- "$temporary"
  fi
}

make_stub() {
  local path="$1"
  printf '%s\n' \
    '#!/usr/bin/env bash' \
    "printf 'fake engine unexpectedly executed\\n' >&2" \
    'exit 73' >"$path"
  chmod +x "$path"
}

assert_rejected() {
  local label="$1"
  local expected="$2"
  shift 2
  local output="$temporary/$label.out"
  local status

  set +e
  "$@" >"$output" 2>&1
  status=$?
  set -e
  [[ $status -ne 0 ]] || die "$label unexpectedly succeeded"
  grep -Fq -- "$expected" "$output" \
    || die "$label missed diagnostic '$expected': $(<"$output")"
}

readonly PIN="$(<"$ROOT/substrate-ref")"
if [[ -n "${FKST_SUBSTRATE_ROOT:-}" ]]; then
  PINNED_CHECKOUT="$FKST_SUBSTRATE_ROOT"
elif [[ -n "${BIN:-}" && -e "$BIN" ]]; then
  physical_bin="$(python3 - "$BIN" <<'PY'
import os
import sys
print(os.path.realpath(sys.argv[1]))
PY
)"
  PINNED_CHECKOUT="$(
    env -u GIT_DIR -u GIT_WORK_TREE -u GIT_INDEX_FILE -u GIT_COMMON_DIR \
      -u GIT_OBJECT_DIRECTORY -u GIT_ALTERNATE_OBJECT_DIRECTORIES \
      git -C "$(dirname -- "$physical_bin")" rev-parse --show-toplevel 2>/dev/null
  )" || die "set FKST_SUBSTRATE_ROOT or pass BIN inside the pinned substrate checkout"
else
  die "set FKST_SUBSTRATE_ROOT or pass BIN inside the pinned substrate checkout"
fi
readonly PINNED_CHECKOUT
readonly CHECKOUT_HEAD="$(
  env -u GIT_DIR \
    -u GIT_WORK_TREE \
    -u GIT_INDEX_FILE \
    -u GIT_COMMON_DIR \
    -u GIT_OBJECT_DIRECTORY \
    -u GIT_ALTERNATE_OBJECT_DIRECTORIES \
    git -C "$PINNED_CHECKOUT" rev-parse HEAD
)"
[[ "$CHECKOUT_HEAD" == "$PIN" ]] \
  || die "pinned checkout HEAD $CHECKOUT_HEAD does not match pin $PIN"

temporary="$(mktemp -d "${TMPDIR:-/tmp}/fkst-provenance-test.XXXXXX")"
trap cleanup EXIT

mkdir "$temporary/ambient" "$temporary/gitfile" "$temporary/core-worktree"
make_stub "$temporary/ambient/fkst-framework"
make_stub "$temporary/gitfile/fkst-framework"
make_stub "$temporary/core-worktree/fkst-framework"

assert_rejected \
  ambient-git-dir \
  "engine provenance-unverified: physical BIN is not inside a git checkout" \
  env -u GIT_WORK_TREE \
    -u GIT_INDEX_FILE \
    -u GIT_COMMON_DIR \
    -u GIT_OBJECT_DIRECTORY \
    -u GIT_ALTERNATE_OBJECT_DIRECTORIES \
    GIT_DIR="$PINNED_CHECKOUT/.git" \
    BIN="$temporary/ambient/fkst-framework" \
    bash "$ROOT/scripts/run.sh" test

printf 'gitdir: %s\n' "$PINNED_CHECKOUT/.git" >"$temporary/gitfile/.git"
assert_rejected \
  unregistered-gitfile \
  "engine provenance-unverified: checkout is not a registered worktree" \
  env -u GIT_DIR \
    -u GIT_WORK_TREE \
    -u GIT_INDEX_FILE \
    -u GIT_COMMON_DIR \
    -u GIT_OBJECT_DIRECTORY \
    -u GIT_ALTERNATE_OBJECT_DIRECTORIES \
    BIN="$temporary/gitfile/fkst-framework" \
    bash "$ROOT/scripts/run.sh" test

git -C "$temporary/core-worktree" init -q
git -C "$temporary/core-worktree" config core.worktree "$PINNED_CHECKOUT"
assert_rejected \
  redirected-core-worktree \
  "engine provenance-unverified: BIN is not inside the pinned checkout" \
  env -u GIT_DIR \
    -u GIT_WORK_TREE \
    -u GIT_INDEX_FILE \
    -u GIT_COMMON_DIR \
    -u GIT_OBJECT_DIRECTORY \
    -u GIT_ALTERNATE_OBJECT_DIRECTORIES \
    BIN="$temporary/core-worktree/fkst-framework" \
    bash "$ROOT/scripts/run.sh" test

printf 'provenance tests: ok\n'
