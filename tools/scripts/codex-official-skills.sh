#!/usr/bin/env bash
set -euo pipefail

# Keep the checkout outside the repository. The repository must not carry a
# symlink (the admission snapshot is intentionally regular-file only).
codex_home="${CODEX_HOME:-$HOME/.codex}"
checkout_dir="${CODEX_OFFICIAL_SKILLS_DIR:-$codex_home/openai-skills}"
link_path="${CODEX_SKILLS_LINK:-$HOME/.agents/skills}"
repository="${CODEX_OFFICIAL_SKILLS_REPO:-https://github.com/openai/skills.git}"
ref="${CODEX_OFFICIAL_SKILLS_REF:-main}"
source_path="${CODEX_OFFICIAL_SKILLS_PATH:-skills/.curated}"

die() {
  printf 'codex-official-skills: %s\n' "$*" >&2
  exit 1
}

[[ "$checkout_dir" = /* ]] || die "CODEX_OFFICIAL_SKILLS_DIR must be absolute: $checkout_dir"
[[ "$link_path" = /* ]] || die "CODEX_SKILLS_LINK must be absolute: $link_path"
[[ "$source_path" != /* && "$source_path" != *..* ]] \
  || die "CODEX_OFFICIAL_SKILLS_PATH must be a repository-relative path without '..': $source_path"

mkdir -p "$(dirname "$checkout_dir")" "$(dirname "$link_path")"

if [[ -d "$checkout_dir/.git" ]]; then
  origin="$(git -C "$checkout_dir" remote get-url origin 2>/dev/null || true)"
  [[ "$origin" == "$repository" ]] \
    || die "existing checkout has origin '$origin', expected '$repository': $checkout_dir"
  [[ -z "$(git -C "$checkout_dir" status --porcelain)" ]] \
    || die "existing checkout is dirty; commit or remove local changes: $checkout_dir"
  git -C "$checkout_dir" fetch --depth=1 origin "$ref"
  git -C "$checkout_dir" checkout --detach FETCH_HEAD >/dev/null
else
  [[ ! -e "$checkout_dir" ]] || die "destination exists but is not an official-skills checkout: $checkout_dir"
  git clone --depth=1 --filter=blob:none --sparse --branch "$ref" \
    "$repository" "$checkout_dir" >/dev/null
fi

git -C "$checkout_dir" sparse-checkout set "$source_path"
source_dir="$checkout_dir/$source_path"
[[ -d "$source_dir" ]] || die "official skills path is missing: $source_path"

if [[ -L "$link_path" ]]; then
  current_target="$(readlink "$link_path")"
  [[ "$current_target" == "$source_dir" ]] || die \
    "existing skills link points to '$current_target', expected '$source_dir': $link_path"
elif [[ -e "$link_path" ]]; then
  die "refusing to replace existing non-symlink path: $link_path"
else
  ln -s "$source_dir" "$link_path"
fi

printf 'official Codex skills synced\n'
printf 'source: %s @ %s\n' "$repository" "$(git -C "$checkout_dir" rev-parse --short HEAD)"
printf 'link:   %s -> %s\n' "$link_path" "$source_dir"
