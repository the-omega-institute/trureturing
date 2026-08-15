#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf 'usage: %s TOOLCHAIN_FILE [--attempts N] [--github-path FILE]\n' "$0" >&2
}

if (($# == 0)); then
  usage
  exit 64
fi

toolchain_file="$1"
attempt_count=3
github_path=""
shift

while (($# > 0)); do
  case "$1" in
    --attempts)
      if (($# < 2)); then
        usage
        exit 64
      fi
      attempt_count="$2"
      shift 2
      ;;
    --github-path)
      if (($# < 2)) || [[ -z "$2" ]]; then
        usage
        exit 64
      fi
      github_path="$2"
      shift 2
      ;;
    *)
      usage
      exit 64
      ;;
  esac
done

if [[ ! "$attempt_count" =~ ^[1-9][0-9]*$ ]]; then
  usage
  exit 64
fi

retry_attempts=()
for ((attempt = 1; attempt <= attempt_count; attempt++)); do
  retry_attempts+=("$attempt")
done

toolchain=""
read_toolchain() {
  toolchain="$(tr -d '\r\n' < "$toolchain_file")"
  test -n "$toolchain"
}

# Engineering read this before installation; inspect read it afterwards.
if [[ -n "$github_path" ]]; then
  read_toolchain
fi

elan_install_with_retry() {
  for attempt in "${retry_attempts[@]}"; do
    if curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh \
      | sh -s -- -y --default-toolchain none; then
      return 0
    fi
    printf '%s\n' "elan install attempt $attempt failed" >&2
    sleep 5
  done
  return 1
}
# 工具链本体走 releases.lean-lang.org,那一跳会返回空响应([52] Empty reply
# from server)。elan 自己在解析失败时回退,但下载失败不重试。
elan_toolchain_with_retry() {
  for attempt in "${retry_attempts[@]}"; do
    if "$HOME/.elan/bin/elan" toolchain install "$1"; then
      return 0
    fi
    printf '%s\n' "elan toolchain install attempt $attempt failed" >&2
    sleep 15
  done
  return 1
}
if [[ ! -x "$HOME/.elan/bin/elan" ]]; then
  elan_install_with_retry
fi
if [[ -n "$github_path" ]]; then
  echo "$HOME/.elan/bin" >> "$github_path"
else
  read_toolchain
fi
if ! "$HOME/.elan/bin/elan" toolchain list 2>/dev/null | grep -qF "$toolchain"; then
  elan_toolchain_with_retry "$toolchain"
fi
"$HOME/.elan/bin/elan" default "$toolchain"
"$HOME/.elan/bin/lake" --version
