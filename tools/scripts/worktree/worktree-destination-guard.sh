#!/usr/bin/env bash
set -euo pipefail

make_pid="${1:-}"
if [[ ! "$make_pid" =~ ^[0-9]+$ ]]; then
  printf '%s\n' 'WORKTREE_DEST_INPUT_UNREADABLE: make process id is unavailable' >&2
  exit 2
fi

reject_whitespace() {
  printf '%s\n' 'WORKTREE_DEST_WHITESPACE: worktree destination must not contain whitespace' >&2
  exit 2
}

contains_whitespace() {
  [[ "$1" =~ [[:space:]] ]]
}

dest_value="${DEST-}"
name_value="${NAME-}"

if [[ "$(uname -s)" == "Linux" ]]; then
  argv_path="/proc/$make_pid/cmdline"
  if [[ ! -r "$argv_path" ]]; then
    printf '%s\n' 'WORKTREE_DEST_INPUT_UNREADABLE: raw make arguments are unavailable' >&2
    exit 2
  fi

  while IFS= read -r -d '' argument; do
    case "$argument" in
      DEST=*)
        dest_value="${argument#DEST=}"
        ;;
      NAME=*)
        name_value="${argument#NAME=}"
        ;;
    esac
  done < "$argv_path"

  if contains_whitespace "$dest_value"; then
    reject_whitespace
  fi
  if [[ -z "$dest_value" ]] && contains_whitespace "$name_value"; then
    reject_whitespace
  fi
else
  make_command="$(ps -ww -o command= -p "$make_pid" 2>/dev/null || true)"
  if [[ -z "$make_command" ]]; then
    printf '%s\n' 'WORKTREE_DEST_INPUT_UNREADABLE: raw make arguments are unavailable' >&2
    exit 2
  fi

  hidden_leading_whitespace() {
    local variable="$1"
    local make_value="$2"
    if [[ "$make_command" == *"$variable=\\0"[0-7][0-7]* ]]; then
      return 0
    fi
    if [[ -n "$make_value" && "$make_command" == *"$variable= "* ]]; then
      return 0
    fi
    if [[ -z "$make_value"
      && ("$make_command" == *"$variable=  "*
        || "$make_command" == *"$variable= ") ]]; then
      return 0
    fi
    return 1
  }

  if contains_whitespace "$dest_value" || hidden_leading_whitespace DEST "$dest_value"; then
    reject_whitespace
  fi
  if [[ -z "$dest_value" ]] \
    && (contains_whitespace "$name_value" || hidden_leading_whitespace NAME "$name_value"); then
    reject_whitespace
  fi
fi
