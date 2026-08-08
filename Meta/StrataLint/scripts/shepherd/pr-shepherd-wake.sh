#!/usr/bin/env bash
# Checkless PR wake state machine, sourced only by the canonical pr-shepherd entrypoint.

WAKE_STATE_HEAD=""
WAKE_STATE_COUNT=""
WAKE_STATE_NEXT_AT=""
WAKE_STATE_TERMINAL=""

load_wake_state() {
  local marker="$1" line schema="" head="" count="" next_at="" terminal=""
  local seen_schema=0 seen_head=0 seen_count=0 seen_next_at=0 seen_terminal=0
  while IFS= read -r line || [[ -n "$line" ]]; do
    case "$line" in
      schema=*) [[ "$seen_schema" == "0" ]] || return 1; schema="${line#schema=}"; seen_schema=1 ;;
      head=*) [[ "$seen_head" == "0" ]] || return 1; head="${line#head=}"; seen_head=1 ;;
      count=*) [[ "$seen_count" == "0" ]] || return 1; count="${line#count=}"; seen_count=1 ;;
      next_at=*) [[ "$seen_next_at" == "0" ]] || return 1; next_at="${line#next_at=}"; seen_next_at=1 ;;
      terminal=*) [[ "$seen_terminal" == "0" ]] || return 1; terminal="${line#terminal=}"; seen_terminal=1 ;;
      *) return 1 ;;
    esac
  done < "$marker" 2>/dev/null || return 1
  [[ "$schema" == "pr-wake-state-v1" \
      && "$head" =~ ^[0-9a-f]{40}$ \
      && "$count" =~ ^(0|[1-9][0-9]*)$ \
      && "$next_at" =~ ^(0|[1-9][0-9]*)$ \
      && "$terminal" =~ ^[01]$ ]] || return 1
  WAKE_STATE_HEAD="$head"
  WAKE_STATE_COUNT="$count"
  WAKE_STATE_NEXT_AT="$next_at"
  WAKE_STATE_TERMINAL="$terminal"
}
write_wake_state() {
  local marker="$1" head="$2" count="$3" next_at="$4" terminal="$5"
  local temporary="$marker.next.$$.$RANDOM"
  if ! (umask 077; {
      printf 'schema=pr-wake-state-v1\n'
      printf 'head=%s\n' "$head"
      printf 'count=%s\n' "$count"
      printf 'next_at=%s\n' "$next_at"
      printf 'terminal=%s\n' "$terminal"
    } > "$temporary") \
      || ! mv "$temporary" "$marker"; then
    rm -f "$temporary" 2>/dev/null || true
    return 1
  fi
}
wake_delay_for_count() {
  local count="$1" delay="$WAKE_BACKOFF_BASE_SECONDS" index=0
  while [[ "$index" -lt "$count" ]]; do
    delay=$((delay * 4))
    index=$((index + 1))
  done
  printf '%s\n' "$delay"
}
validate_wake_config() {
  local num="$1"
  if [[ ! "$WAKE_BACKOFF_BASE_SECONDS" =~ ^[1-9][0-9]{0,4}$ \
      || ! "$WAKE_SLEEP_SECONDS" =~ ^(0|[1-9][0-9]*)$ \
      || ! "$WAKE_REOPEN_RETRY_SLEEP_SECONDS" =~ ^(0|[1-9][0-9]*)$ ]]; then
    log "ALERT #$num WAKE_CONFIG_INVALID base=$WAKE_BACKOFF_BASE_SECONDS max=$WAKE_MAX_ATTEMPTS terminal=OPEN"
    return 1
  fi
}
reconcile_wake_head() {
  local num="$1" head="$2" marker="$3"
  load_wake_state "$marker" || {
    log "ALERT #$num WAKE_STATE_INVALID path=$marker terminal=OPEN"
    return 1
  }
  [[ "$WAKE_STATE_HEAD" != "$head" ]] || return 0
  if write_wake_state "$marker" "$head" 0 0 0; then
    log "SWEEP #$num WAKE_RESET old_head=$WAKE_STATE_HEAD head=$head count=0"
  else
    log "ALERT #$num WAKE_STATE_WRITE_FAILED path=$marker terminal=OPEN"
    return 1
  fi
}
handle_checkless_wake() {
  local num="$1" head="$2" marker="$3" now delay next_at count terminal wake_result
  validate_wake_config "$num" || return 0
  now="$(date '+%s')"
  if [[ ! "$now" =~ ^[0-9]+$ ]]; then
    log "ALERT #$num WAKE_CLOCK_INVALID terminal=OPEN"
    return 0
  fi
  if [[ ! -f "$marker" ]]; then
    delay="$(wake_delay_for_count 0)"
    next_at=$((now + delay))
    if write_wake_state "$marker" "$head" 0 "$next_at" 0; then
      log "SWEEP #$num head=$head 无 checks,WAKE_BACKOFF count=0 next_at=$next_at"
    else
      log "ALERT #$num WAKE_STATE_WRITE_FAILED path=$marker terminal=OPEN"
    fi
    return 0
  fi
  if ! load_wake_state "$marker"; then
    log "ALERT #$num WAKE_STATE_INVALID path=$marker terminal=OPEN"
    return 0
  fi
  if [[ "$WAKE_STATE_HEAD" != "$head" ]]; then
    delay="$(wake_delay_for_count 0)"
    next_at=$((now + delay))
    if write_wake_state "$marker" "$head" 0 "$next_at" 0; then
      log "SWEEP #$num WAKE_RESET old_head=$WAKE_STATE_HEAD head=$head count=0 next_at=$next_at"
    else
      log "ALERT #$num WAKE_STATE_WRITE_FAILED path=$marker terminal=OPEN"
    fi
    return 0
  fi
  count="$WAKE_STATE_COUNT"
  next_at="$WAKE_STATE_NEXT_AT"
  terminal="$WAKE_STATE_TERMINAL"
  if [[ "$terminal" == "1" || "$count" -ge "$WAKE_MAX_ATTEMPTS" ]]; then
    if [[ "$terminal" != "1" ]]; then
      write_wake_state "$marker" "$head" "$count" 0 1 \
        || { log "ALERT #$num WAKE_STATE_WRITE_FAILED path=$marker terminal=OPEN"; return 0; }
    fi
    log "ALERT #$num WAKE_CAP head=$head count=$count max=$WAKE_MAX_ATTEMPTS terminal=OPEN"
    return 0
  fi
  if [[ "$next_at" == "0" ]]; then
    delay="$(wake_delay_for_count "$count")"
    next_at=$((now + delay))
    write_wake_state "$marker" "$head" "$count" "$next_at" 0 \
      || { log "ALERT #$num WAKE_STATE_WRITE_FAILED path=$marker terminal=OPEN"; return 0; }
  fi
  if [[ "$now" -lt "$next_at" ]]; then
    log "SWEEP #$num WAKE_BACKOFF head=$head count=$count next_at=$next_at now=$now"
    return 0
  fi

  count=$((count + 1))
  if [[ "$count" -ge "$WAKE_MAX_ATTEMPTS" ]]; then
    next_at=0
    terminal=1
  else
    delay="$(wake_delay_for_count "$count")"
    next_at=$((now + delay))
    terminal=0
  fi
  write_wake_state "$marker" "$head" "$count" "$next_at" "$terminal" \
    || { log "ALERT #$num WAKE_STATE_WRITE_FAILED path=$marker terminal=OPEN"; return 0; }
  if wake_pr "$num"; then wake_result=success; else wake_result=failure; fi
  if [[ "$terminal" == "1" ]]; then
    log "ALERT #$num WAKE_CAP head=$head count=$count max=$WAKE_MAX_ATTEMPTS terminal=OPEN wake=$wake_result"
  else
    log "SWEEP #$num WAKE_STATE head=$head count=$count next_at=$next_at wake=$wake_result"
  fi
}
