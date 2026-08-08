#!/usr/bin/env bash
# Verified bootstrap and atomic remote-dev reload for the canonical shepherd.

reload_watch() {
  local interval="$1" max="$2" next_cycle="$3" snapshot_root snapshot source_root source_snapshot blob rc
  local script_repository destination_file
  local script_relative tracked_blob actual_blob name relative source_oid remote_paths path
  local local_tracked_paths local_expected_paths=""
  local module_relative bootstrap="${WATCH_LOADED_BLOB:+0}"
  local -a remote_module_names=()
  [[ -n "$bootstrap" ]] || bootstrap=1
  if ! snapshot_root="$(mktemp -d "${TMPDIR:-/tmp}/pr-shepherd-watch.XXXXXXXX")"; then
    log "WATCH reload unavailable: immutable snapshot cannot be allocated"; return 1
  fi
  snapshot="$snapshot_root/pr-shepherd.sh"
  if ! source_root="$(mktemp -d "${TMPDIR:-/tmp}/pr-shepherd-watch.XXXXXXXX")"; then
    rmdir "$snapshot_root"; log "WATCH reload unavailable: composite staging cannot be allocated"; return 1
  fi
  source_snapshot="$source_root/pr-shepherd.sh"
  mkdir "$source_root/shepherd" || { rmdir "$source_root" "$snapshot_root"; return 1; }
  script_repository="${bootstrap_repository:-}"
  if [[ -z "$script_repository" ]]; then
    GIT_CAPTURE script_repository watch-reload-root -C "$(dirname "$SCRIPT_PATH")" \
      rev-parse --show-toplevel 2>/dev/null || script_repository=""
  fi
  if [[ "$SCRIPT_PATH" == "$script_repository/"* ]]; then
    script_relative="${SCRIPT_PATH#"$script_repository/"}"
  else
    script_relative=""
  fi
  if [[ "$bootstrap" == 1 ]]; then
    module_relative="${script_relative%/*}/shepherd"
    GIT_CAPTURE local_tracked_paths watch-reload-bootstrap-tree -C "$script_repository" \
      ls-tree -r --name-only HEAD -- "$module_relative" 2>/dev/null || local_tracked_paths=""
    for name in pr-shepherd.sh "${SHEPHERD_MODULE_NAMES[@]}"; do
      [[ "$name" == pr-shepherd.sh ]] || local_expected_paths+="${local_expected_paths:+$'\n'}$module_relative/$name"
    done
    if [[ -z "$script_relative" || "$local_tracked_paths" != "$local_expected_paths" ]] \
        || ! GIT watch-reload-bootstrap-clean -C "$script_repository" diff --quiet HEAD -- \
          "$script_relative" "$module_relative"; then
      remove_watch_snapshot "$source_snapshot"; remove_watch_snapshot "$snapshot"
      log "WATCH reload blocked: canonical script or module does not match tracked HEAD path=$SCRIPT_PATH"
      return 1
    fi
  fi
  if [[ -z "$script_repository" || -z "$script_relative" ]] \
      || ! GIT watch-reload-fetch -C "$script_repository" fetch --no-tags "$REMOTE" \
        "+refs/heads/dev:refs/remotes/$REMOTE/dev" \
      || ! GIT_CAPTURE source_oid watch-reload-source -C "$script_repository" \
        rev-parse "refs/remotes/$REMOTE/dev^{commit}"; then
    remove_watch_snapshot "$source_snapshot"; remove_watch_snapshot "$snapshot"
    log "WATCH reload unavailable: remote dev source cannot be pinned remote=$REMOTE"
    return 1
  fi
  module_relative="${script_relative%/*}/shepherd"
  if ! GIT_CAPTURE remote_paths watch-reload-module-list -C "$script_repository" \
      ls-tree -r --name-only "$source_oid" -- "$module_relative"; then
    remove_watch_snapshot "$source_snapshot"; remove_watch_snapshot "$snapshot"
    log "WATCH reload unavailable: module tree cannot be read source_commit=$source_oid"; return 1
  fi
  while IFS= read -r path || [[ -n "$path" ]]; do
    case "$path" in "$module_relative"/pr-shepherd-*.sh) ;; *) continue ;; esac
    name="${path#"$module_relative/"}"; [[ "$name" != */* ]] || continue
    remote_module_names+=("$name")
  done <<< "$remote_paths"
  if [[ "${#remote_module_names[@]}" -eq 0 ]]; then
    remove_watch_snapshot "$source_snapshot"; remove_watch_snapshot "$snapshot"
    log "WATCH reload unavailable: remote dev has no shepherd modules source_commit=$source_oid"
    return 1
  fi
  for name in pr-shepherd.sh "${remote_module_names[@]}"; do
    if [[ "$name" == pr-shepherd.sh ]]; then
      relative="$script_relative"; destination_file="$source_snapshot"
    else
      relative="$module_relative/$name"; destination_file="$source_root/shepherd/$name"
    fi
    if ! run_bounded_to_file "$destination_file" git watch-reload-extract \
        "$GIT_TIMEOUT_SECONDS" git -C "$script_repository" cat-file blob "$source_oid:$relative" \
        || ! chmod 0400 "$destination_file" || ! /bin/bash -n "$destination_file" \
        || ! GIT_CAPTURE tracked_blob watch-reload-tracked-blob -C "$script_repository" \
          rev-parse "$source_oid:$relative" \
        || ! GIT_CAPTURE actual_blob watch-reload-actual-blob hash-object "$destination_file" \
        || [[ "$actual_blob" != "$tracked_blob" ]]; then
      remove_watch_snapshot "$source_snapshot"; remove_watch_snapshot "$snapshot"
      log "WATCH reload blocked: remote composite verification failed path=$relative source_commit=$source_oid"
      return 1
    fi
  done
  if ! cp -R "$source_snapshot" "$source_root/shepherd" "$snapshot_root"; then
    remove_watch_snapshot "$source_snapshot"; remove_watch_snapshot "$snapshot"
    log "WATCH reload unavailable: verified composite snapshot cannot be copied source_commit=$source_oid"
    return 1
  fi
  remove_watch_snapshot "$source_snapshot"
  blob="$(compute_shepherd_identity "$snapshot" "$snapshot_root/shepherd" 2>/dev/null)" || blob=""
  if [[ ! "$blob" =~ ^[0-9a-f]{40}$ ]]; then
    remove_watch_snapshot "$snapshot"
    log "WATCH reload unavailable path=$SCRIPT_PATH source_commit=$source_oid"; return 1
  fi
  if [[ -n "$WATCH_LOADED_BLOB" && "$WATCH_LOADED_BLOB" != "$blob" ]]; then
    log "WATCH SCRIPT CHANGED previous_blob=$WATCH_LOADED_BLOB current_blob=$blob source_commit=$source_oid"
  fi
  export PR_SHEPHERD_CANONICAL_SCRIPT="$SCRIPT_PATH" PR_SHEPHERD_ROOT="$ROOT"
  export PR_SHEPHERD_WATCH_LOADED_BLOB="$blob" PR_SHEPHERD_WATCH_PREVIOUS_SCRIPT="$LOADED_SCRIPT_PATH"
  export PR_SHEPHERD_WATCH_PROCESS_START="$WATCH_PROCESS_START" PR_SHEPHERD_WATCH_CYCLE="$next_cycle"
  export PR_SHEPHERD_WATCH_OWNER_PID="$$" PR_SHEPHERD_WATCH_OWNER_START="$WATCH_PROCESS_START"
  export PR_SHEPHERD_WATCH_INTERVAL="$interval" PR_SHEPHERD_WATCH_MAX_CYCLES="$max"
  if exec /bin/bash "$snapshot" watch "$interval" "$max"; then return 0; else rc=$?; fi
  rm -f "$snapshot" 2>/dev/null || true
  log "WATCH reload exec failed path=$snapshot exit=$rc"; return "$rc"
}
bootstrap_watch_exit_cleanup() {
  local rc=$? now
  terminate_active_bounded_tree
  if [[ "$WATCH_OWNS_LEASE" == 1 ]]; then
    WATCH_STATE_OWNER_PID="$$"; WATCH_STATE_OWNER_START="$WATCH_PROCESS_START"
    WATCH_LOADED_BLOB=none; now="$(date '+%s')" || now=0
    write_watch_state terminal none bootstrap "$now" 0 "$now" bootstrap-exit "$rc" 1 \
      || log "WATCH bootstrap terminal state publication failed path=$PIDFILE exit=$rc"
  fi
  [[ -z "$WATCH_LOCK_CANDIDATE" ]] || rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
  clear_watch_reclaim || true; remove_watch_snapshot "$LOADED_SCRIPT_PATH"; return "$rc"
}
bootstrap_interrupt_watch() {
  local rc="$1"
  terminate_active_bounded_tree; exit "$rc"
}
bootstrap_watch() {
  local interval="${1:-60}" max="${2:-360}"
  [[ "$interval" =~ ^(0|[1-9][0-9]*)$ && "$max" =~ ^[1-9][0-9]*$ ]] \
    || { log "WATCH invalid interval or max_cycles (interval=$interval max_cycles=$max)"; return 2; }
  WATCH_STATE_INTERVAL="$interval"; WATCH_STATE_MAX="$max"
  trap bootstrap_watch_exit_cleanup EXIT
  trap 'bootstrap_interrupt_watch 143' TERM
  trap 'bootstrap_interrupt_watch 130' INT
  acquire_watch_lease || return
  reload_watch "$interval" "$max" 1
}
