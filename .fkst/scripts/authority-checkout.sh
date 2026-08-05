#!/usr/bin/env bash

sync_authority_checkout() {
  local target_revision="$1" authority_root="${FKST_GITHUB_PROXY_AUTHORITY_ROOT:-}"
  local authority_head authority_status
  if [[ -z "$authority_root" ]]; then
    say "AUTHORITY-CONFIG-MISSING; authority checkout not changed"
    return 0
  fi
  [[ "$target_revision" =~ ^[0-9a-f]{40}$ ]] || {
    say "AUTHORITY-TARGET-INVALID; authority checkout not changed"
    return 0
  }
  if ! git -C "$authority_root" fetch origin dev >/dev/null 2>&1; then
    say "AUTHORITY-FETCH-FAIL; authority checkout not changed"
    return 0
  fi
  authority_head="$(git -C "$authority_root" rev-parse HEAD 2>/dev/null)"
  if [[ ! "$authority_head" =~ ^[0-9a-f]{40}$ ]] \
      || ! git -C "$authority_root" cat-file -e \
        "$target_revision^{commit}" 2>/dev/null; then
    say "AUTHORITY-REV-PARSE-FAIL; authority checkout not changed"
    return 0
  fi
  if [[ "$authority_head" == "$target_revision" ]]; then
    say "AUTHORITY CURRENT (${authority_head:0:12})"
    return 0
  fi
  if ! git -C "$authority_root" merge-base --is-ancestor \
      "$authority_head" "$target_revision" >/dev/null 2>&1; then
    say "AUTHORITY DIVERGED from deployed pin ${target_revision:0:12}; not auto-FF"
    return 0
  fi
  if ! authority_status="$(
      git -C "$authority_root" status --porcelain --untracked-files=no 2>/dev/null
    )"; then
    say "AUTHORITY-STATUS-FAIL; authority checkout not changed"
    return 0
  fi
  if [[ -n "$authority_status" ]]; then
    say "AUTHORITY-FF-BLOCKED (uncommitted changes); authority stays on ${authority_head:0:12}"
    return 0
  fi

  say "AUTHORITY BEHIND ${authority_head:0:12} -> ${target_revision:0:12}; FF to deployed pin"
  if ! git -C "$authority_root" merge --ff-only "$target_revision" >/dev/null 2>&1; then
    say "AUTHORITY-FF-BLOCKED; authority stays on ${authority_head:0:12}"
  fi
  return 0
}
