#!/usr/bin/env bash
# Detect a branch whose global environment pins are stale relative to its base branch.
#
# A pin (lean-toolchain, lake-manifest.json, lakefile.*) is a single global write point: it
# names the ground every proof in the repository stands on. Judging a candidate at its fork
# point is deliberate and correct for *rules* -- a candidate should answer only to the harness
# that existed when it departed (see the comment on lean-inspect's base resolution). It is not
# correct for the ground: when the base branch moves a pin, a branch that departed earlier
# builds against a toolchain that will not exist after the merge, so its green says nothing
# about the tree that lands.
#
# The failure that produces is also actively misleading. When dev reverted lean-toolchain from
# v4.33 to v4.31 on 2026-08-15, four in-flight PRs turned red reporting four unrelated Lean
# modules as broken mathematics; nothing named the pin. Detect the staleness, not its symptom.
#
# Fires only when the base moved a pin and this branch did not touch it. A branch that changes
# a pin on purpose -- the upgrade PR itself -- is the case where head and fork differ, and is
# never reported.
set -euo pipefail

BASE_TIP="${1:?base tip ref required}"
FORK_POINT="${2:?fork point ref required}"
HEAD_REF="${3:?head ref required}"
REPO="${4:-.}"

PINS=(lean-toolchain lake-manifest.json lakefile.toml lakefile.lean)

stale=()
for pin in "${PINS[@]}"; do
  base_pin="$(git -C "$REPO" show "${BASE_TIP}:${pin}" 2>/dev/null || true)"
  fork_pin="$(git -C "$REPO" show "${FORK_POINT}:${pin}" 2>/dev/null || true)"
  head_pin="$(git -C "$REPO" show "${HEAD_REF}:${pin}" 2>/dev/null || true)"

  # Untouched by this branch, yet different from where the base now stands.
  if [[ "$head_pin" == "$fork_pin" && "$head_pin" != "$base_pin" ]]; then
    stale+=("$pin")
  fi
done

if (( ${#stale[@]} == 0 )); then
  printf 'environment pins current against base\n'
  exit 0
fi

{
  printf 'stale environment pin(s): %s\n' "${stale[*]}"
  printf 'The base branch moved these since this branch departed, and this branch did not\n'
  printf 'change them. Anything built here stands on a toolchain that will not exist after\n'
  printf 'the merge. Merge the base branch into this branch and push again.\n'
} >&2
exit 1
