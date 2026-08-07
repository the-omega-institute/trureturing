#!/usr/bin/env bash
# Derived PR lease and FIFO sweep support, sourced by pr-shepherd.sh.

WAKE_STATE_HEAD=""
WAKE_STATE_COUNT=""
WAKE_STATE_NEXT_AT=""
WAKE_STATE_TERMINAL=""
RECALC_STATE_HEAD_OID=""
RECALC_STATE_DEV_OID=""
RECALC_STATE_SCRIPT_BLOB=""
RECALC_STATE_FAILURE_CLASS=""
RECALC_STATE_FAILURE_EXIT=""
RECALC_STATE_CLASS_ATTEMPTS=""
RECALC_STATE_TOTAL_ATTEMPTS=""
RECALC_STATE_NEXT_AT=""
RECALC_STATE_TERMINAL=""
INFRA_STATE_FAILURE_CLASS=""
INFRA_STATE_ATTEMPTS=""
INFRA_STATE_NEXT_AT=""

pr_has_derived_changes() {
  local num="$1" out path
  if ! GH_CAPTURE out pr-diff pr diff "$num" --repo "$REPO" --name-only; then
    set_bounded_failure pr-diff
    log "ALERT #$num PR file classification=UNKNOWN; skip this sweep: $(printf '%s' "$out" | head -c 100)"
    return 2
  fi
  while IFS= read -r path || [[ -n "$path" ]]; do
    is_derived_conflict "$path" && return 0
  done <<< "$out"
  return 1
}

derived_lease_mtime() {
  local mtime
  mtime="$(stat -f '%m' "$1" 2>/dev/null || true)"
  if [[ "$mtime" =~ ^[0-9]+$ ]]; then
    printf '%s\n' "$mtime"
    return 0
  fi
  mtime="$(stat -c '%Y' "$1" 2>/dev/null || true)"
  [[ "$mtime" =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "$mtime"
}
load_derived_lease() {
  local directory="$1" line schema="" pr="" acquired_at="" token=""
  while IFS= read -r line || [[ -n "$line" ]]; do
    case "$line" in
      schema=*) schema="${line#schema=}" ;;
      pr=*) pr="${line#pr=}" ;;
      acquired_at=*) acquired_at="${line#acquired_at=}" ;;
      token=*) token="${line#token=}" ;;
      *) return 1 ;;
    esac
  done < "$directory/owner" 2>/dev/null || return 1
  [[ "$schema" == "derived-fifo-lease-v1" \
      && "$pr" =~ ^[1-9][0-9]*$ \
      && "$acquired_at" =~ ^[0-9]+$ \
      && -n "$token" ]] || return 1
  DERIVED_LEASE_PR="$pr"
  DERIVED_LEASE_ACQUIRED_AT="$acquired_at"
  DERIVED_LEASE_TOKEN="$token"
}
create_derived_lease() {
  local num="$1" acquired_at="$2" directory="$STATE_DIR/derived-fifo.lease"
  local token="$$-$acquired_at-$RANDOM" temporary="$directory/owner.next.$$.$RANDOM"
  mkdir "$directory" 2>/dev/null || return 1
  if ! (umask 077; {
      printf 'schema=derived-fifo-lease-v1\n'
      printf 'pr=%s\n' "$num"
      printf 'acquired_at=%s\n' "$acquired_at"
      printf 'token=%s\n' "$token"
    } > "$temporary") \
      || ! mv "$temporary" "$directory/owner"; then
    rm -f "$temporary" "$directory/owner" 2>/dev/null || true
    rmdir "$directory" 2>/dev/null || true
    return 1
  fi
  DERIVED_LEASE_PR="$num"
  DERIVED_LEASE_ACQUIRED_AT="$acquired_at"
  DERIVED_LEASE_TOKEN="$token"
  log "FIFO LEASE acquired pr=#$num acquired_at=$acquired_at ttl=${DERIVED_LEASE_TTL}s"
}
acquire_derived_lease() {
  local num="$1" directory="$STATE_DIR/derived-fifo.lease" now acquired_at age
  local observed_pr observed_at observed_token stale moved_at changed=0 observed_valid=0
  [[ "$DERIVED_LEASE_TTL" =~ ^[1-9][0-9]*$ ]] \
    || { log "FIFO LEASE invalid ttl=$DERIVED_LEASE_TTL"; return 1; }
  now="$(date '+%s')"
  [[ "$now" =~ ^[0-9]+$ ]] || { log "FIFO LEASE clock unavailable"; return 1; }
  if [[ "$DRYRUN" == "1" ]]; then
    DERIVED_LEASE_PR="$num"
    DERIVED_LEASE_ACQUIRED_AT="$now"
    DERIVED_LEASE_TOKEN="dry-run"
    log "FIFO LEASE acquired pr=#$num acquired_at=$now ttl=${DERIVED_LEASE_TTL}s dry-run"
    return 0
  fi
  mkdir -p "$STATE_DIR"
  create_derived_lease "$num" "$now" && return 0

  DERIVED_LEASE_PR=""
  DERIVED_LEASE_ACQUIRED_AT=""
  DERIVED_LEASE_TOKEN=""
  if load_derived_lease "$directory"; then
    observed_valid=1
    acquired_at="$DERIVED_LEASE_ACQUIRED_AT"
  else
    acquired_at="$(derived_lease_mtime "$directory" || true)"
    [[ "$acquired_at" =~ ^[0-9]+$ ]] || {
      log "FIFO LEASE unreadable path=$directory"
      return 1
    }
    DERIVED_LEASE_PR="unknown"
    DERIVED_LEASE_ACQUIRED_AT="$acquired_at"
    DERIVED_LEASE_TOKEN="invalid"
  fi
  age=$((now - acquired_at))
  [[ "$age" -ge "$DERIVED_LEASE_TTL" ]] || return 1

  observed_pr="$DERIVED_LEASE_PR"
  observed_at="$DERIVED_LEASE_ACQUIRED_AT"
  observed_token="$DERIVED_LEASE_TOKEN"
  log "FIFO LEASE expired pr=#$observed_pr acquired_at=$observed_at ttl=${DERIVED_LEASE_TTL}s"
  stale="$directory.stale.$$.$RANDOM"
  if ! mv "$directory" "$stale" 2>/dev/null; then
    load_derived_lease "$directory" 2>/dev/null || true
    return 1
  fi
  DERIVED_LEASE_PR=""
  DERIVED_LEASE_ACQUIRED_AT=""
  DERIVED_LEASE_TOKEN=""
  if [[ "$observed_valid" == "1" ]]; then
    if ! load_derived_lease "$stale" \
        || [[ "$DERIVED_LEASE_PR" != "$observed_pr" \
            || "$DERIVED_LEASE_ACQUIRED_AT" != "$observed_at" \
            || "$DERIVED_LEASE_TOKEN" != "$observed_token" ]]; then
      changed=1
    fi
  else
    moved_at="$(derived_lease_mtime "$stale" || true)"
    if load_derived_lease "$stale" || [[ "$moved_at" != "$observed_at" ]]; then
      changed=1
    fi
  fi
  if [[ "$changed" == "1" ]]; then
    [[ -e "$directory" ]] || mv "$stale" "$directory" 2>/dev/null || true
    load_derived_lease "$directory" 2>/dev/null || true
    return 1
  fi
  rm -f "$stale/owner" "$stale"/owner.next.*
  if ! rmdir "$stale" 2>/dev/null; then
    log "FIFO LEASE stale state cannot be removed path=$stale"
    return 1
  fi
  create_derived_lease "$num" "$now" || {
    load_derived_lease "$directory" 2>/dev/null || true
    return 1
  }
}
release_derived_lease() {
  local directory="$STATE_DIR/derived-fifo.lease" token="$DERIVED_LEASE_TOKEN"
  local pr="$DERIVED_LEASE_PR"
  [[ "$DRYRUN" != "1" && -n "$token" ]] || return 0
  load_derived_lease "$directory" 2>/dev/null || return 0
  [[ "$DERIVED_LEASE_TOKEN" == "$token" ]] || return 0
  rm -f "$directory/owner"
  if ! rmdir "$directory" 2>/dev/null; then
    log "FIFO LEASE release incomplete pr=#$pr path=$directory"
  fi
  DERIVED_LEASE_TOKEN=""
}

recalculation_marker() { printf '%s/recalculate-%s\n' "$STATE_DIR" "$1"; }
load_recalculation_state() {
  local marker="$1" line schema="" pr="" head_oid="" dev_oid="" script_blob=""
  local failure_class="" failure_exit="" class_attempts="" total_attempts="" next_at="" terminal=""
  local seen=" " key value
  while IFS= read -r line || [[ -n "$line" ]]; do
    key="${line%%=*}"; value="${line#*=}"
    [[ "$line" == *=* && "$seen" != *" $key "* ]] || return 1
    seen+="$key "
    case "$key" in
      schema) schema="$value" ;; pr) pr="$value" ;; head_oid) head_oid="$value" ;;
      dev_oid) dev_oid="$value" ;; script_blob) script_blob="$value" ;;
      last_failure_class) failure_class="$value" ;; failure_exit) failure_exit="$value" ;;
      class_attempts) class_attempts="$value" ;; total_attempts) total_attempts="$value" ;;
      next_at) next_at="$value" ;; terminal) terminal="$value" ;; *) return 1 ;;
    esac
  done < "$marker" 2>/dev/null || return 1
  [[ "$schema" == pr-recalculation-state-v1 \
      && "$pr" =~ ^[1-9][0-9]*$ \
      && "$head_oid" =~ ^[0-9a-f]{40}$ \
      && "$dev_oid" =~ ^[0-9a-f]{40}$ \
      && "$script_blob" =~ ^[0-9a-f]{40}$ \
      && "$failure_class" =~ ^[a-z0-9-]+\.(exit|timeout)$ \
      && "$failure_exit" =~ ^(0|[1-9][0-9]{0,2})$ \
      && "$class_attempts" =~ ^[1-9][0-9]*$ \
      && "$total_attempts" =~ ^[1-9][0-9]*$ \
      && "$next_at" =~ ^(0|[1-9][0-9]*)$ \
      && "$terminal" =~ ^[01]$ ]] || return 1
  RECALC_STATE_HEAD_OID="$head_oid"
  RECALC_STATE_DEV_OID="$dev_oid"
  RECALC_STATE_SCRIPT_BLOB="$script_blob"
  RECALC_STATE_FAILURE_CLASS="$failure_class"
  RECALC_STATE_FAILURE_EXIT="$failure_exit"
  RECALC_STATE_CLASS_ATTEMPTS="$class_attempts"
  RECALC_STATE_TOTAL_ATTEMPTS="$total_attempts"
  RECALC_STATE_NEXT_AT="$next_at"
  RECALC_STATE_TERMINAL="$terminal"
}
write_recalculation_state() {
  local marker="$1" num="$2" head_oid="$3" dev_oid="$4" script_blob="$5"
  local failure_class="$6" failure_exit="$7" class_attempts="$8" total_attempts="$9"
  shift 9
  local next_at="$1" terminal="$2" temporary="$marker.next.$$.$RANDOM"
  if ! (umask 077; {
      printf 'schema=pr-recalculation-state-v1\n'
      printf 'pr=%s\n' "$num"
      printf 'head_oid=%s\n' "$head_oid"
      printf 'dev_oid=%s\n' "$dev_oid"
      printf 'script_blob=%s\n' "$script_blob"
      printf 'last_failure_class=%s\n' "$failure_class"
      printf 'failure_exit=%s\n' "$failure_exit"
      printf 'class_attempts=%s\n' "$class_attempts"
      printf 'total_attempts=%s\n' "$total_attempts"
      printf 'next_at=%s\n' "$next_at"
      printf 'terminal=%s\n' "$terminal"
    } > "$temporary") || ! mv "$temporary" "$marker"; then
    rm -f "$temporary" 2>/dev/null || true
    return 1
  fi
}
recalculation_delay() {
  local attempts="$1" delay="$FAILURE_BACKOFF_BASE_SECONDS" index=0
  while [[ "$index" -lt "$attempts" ]]; do delay=$((delay * 4)); index=$((index + 1)); done
  printf '%s\n' "$delay"
}
recalculation_is_eligible() {
  local num="$1" head_oid="$2" dev_oid="$3" script_blob="$4"
  local marker now
  marker="$(recalculation_marker "$num")"
  [[ -f "$marker" ]] || return 0
  if ! load_recalculation_state "$marker"; then
    log "ALERT #$num RECALC_STATE_INVALID path=$marker terminal=OPEN"
    return 1
  fi
  if [[ "$RECALC_STATE_HEAD_OID" != "$head_oid" \
      || "$RECALC_STATE_DEV_OID" != "$dev_oid" \
      || "$RECALC_STATE_SCRIPT_BLOB" != "$script_blob" ]]; then
    rm -f "$marker"
    log "RECALC_RESET pr=#$num reason=work-identity-changed"
    return 0
  fi
  if [[ "$RECALC_STATE_TERMINAL" == 1 ]]; then
    log "ALERT RECALC_OPEN pr=#$num failure_class=$RECALC_STATE_FAILURE_CLASS class_attempts=$RECALC_STATE_CLASS_ATTEMPTS total_attempts=$RECALC_STATE_TOTAL_ATTEMPTS terminal=OPEN"
    return 1
  fi
  now="$(date '+%s')"
  [[ "$now" =~ ^[0-9]+$ ]] \
    || { log "ALERT #$num RECALC_CLOCK_INVALID terminal=OPEN"; return 1; }
  if [[ "$now" -lt "$RECALC_STATE_NEXT_AT" ]]; then
    log "RECALC_BACKOFF pr=#$num failure_class=$RECALC_STATE_FAILURE_CLASS attempts=$RECALC_STATE_CLASS_ATTEMPTS next_at=$RECALC_STATE_NEXT_AT now=$now"
    return 1
  fi
  log "RECALC_HALF_OPEN pr=#$num failure_class=$RECALC_STATE_FAILURE_CLASS attempts=$RECALC_STATE_CLASS_ATTEMPTS"
  return 0
}
record_recalculation_failure() {
  local num="$1" head_oid="$2" dev_oid="$3" script_blob="$4" failure_class="$5" failure_exit="$6"
  local marker now class_attempts=1 total_attempts=1 delay next_at terminal=0
  marker="$(recalculation_marker "$num")"
  now="$(date '+%s')"
  [[ "$now" =~ ^[0-9]+$ ]] || now=0
  if [[ -f "$marker" ]] && load_recalculation_state "$marker" \
      && [[ "$RECALC_STATE_HEAD_OID" == "$head_oid" \
          && "$RECALC_STATE_DEV_OID" == "$dev_oid" \
          && "$RECALC_STATE_SCRIPT_BLOB" == "$script_blob" ]]; then
    total_attempts=$((RECALC_STATE_TOTAL_ATTEMPTS + 1))
    if [[ "$RECALC_STATE_FAILURE_CLASS" == "$failure_class" ]]; then
      class_attempts=$((RECALC_STATE_CLASS_ATTEMPTS + 1))
    fi
  fi
  if [[ "$class_attempts" -ge "$FAILURE_MAX_CLASS_ATTEMPTS" \
      || "$total_attempts" -ge "$FAILURE_MAX_TOTAL_ATTEMPTS" ]]; then
    terminal=1; next_at=0
  else
    delay="$(recalculation_delay "$class_attempts")"
    next_at=$((now + delay))
  fi
  if ! write_recalculation_state "$marker" "$num" "$head_oid" "$dev_oid" "$script_blob" \
      "$failure_class" "$failure_exit" "$class_attempts" "$total_attempts" "$next_at" "$terminal"; then
    log "ALERT #$num RECALC_STATE_WRITE_FAILED path=$marker terminal=OPEN"
    RECALC_STATE_TERMINAL=1
    return 1
  fi
  RECALC_STATE_TERMINAL="$terminal"
  log "RECALC_FAILURE pr=#$num failure_class=$failure_class failure_exit=$failure_exit class_attempts=$class_attempts total_attempts=$total_attempts next_at=$next_at terminal=$terminal"
  if [[ "$terminal" == 1 ]]; then
    log "ALERT #$num RECALC_OPEN failure_class=$failure_class class_attempts=$class_attempts total_attempts=$total_attempts terminal=OPEN"
  fi
}
clear_recalculation_failure() { rm -f "$(recalculation_marker "$1")"; }

load_infrastructure_state() {
  local marker="$1" line schema="" failure_class="" attempts="" next_at="" seen=" " key value
  while IFS= read -r line || [[ -n "$line" ]]; do
    key="${line%%=*}"; value="${line#*=}"
    [[ "$line" == *=* && "$seen" != *" $key "* ]] || return 1
    seen+="$key "
    case "$key" in
      schema) schema="$value" ;; failure_class) failure_class="$value" ;;
      attempts) attempts="$value" ;; next_at) next_at="$value" ;; *) return 1 ;;
    esac
  done < "$marker" 2>/dev/null || return 1
  [[ "$schema" == pr-infrastructure-state-v1 \
      && "$failure_class" =~ ^[a-z0-9-]+\.(exit|timeout)$ \
      && "$attempts" =~ ^[1-9][0-9]*$ \
      && "$next_at" =~ ^[1-9][0-9]*$ ]] || return 1
  INFRA_STATE_FAILURE_CLASS="$failure_class"
  INFRA_STATE_ATTEMPTS="$attempts"
  INFRA_STATE_NEXT_AT="$next_at"
}
write_infrastructure_state() {
  local marker="$STATE_DIR/infrastructure" failure_class="$1" attempts="$2" next_at="$3"
  local temporary="$marker.next.$$.$RANDOM"
  (umask 077; {
    printf 'schema=pr-infrastructure-state-v1\n'
    printf 'failure_class=%s\n' "$failure_class"
    printf 'attempts=%s\n' "$attempts"
    printf 'next_at=%s\n' "$next_at"
  } > "$temporary") && mv "$temporary" "$marker"
}
infrastructure_is_eligible() {
  local marker="$STATE_DIR/infrastructure" now
  [[ -f "$marker" ]] || return 0
  if ! load_infrastructure_state "$marker"; then
    log "ALERT INFRA_STATE_INVALID path=$marker"
    return 1
  fi
  now="$(date '+%s')"
  [[ "$now" =~ ^[0-9]+$ ]] || { log "ALERT INFRA_CLOCK_INVALID"; return 1; }
  if [[ "$now" -lt "$INFRA_STATE_NEXT_AT" ]]; then
    log "INFRA_BACKOFF failure_class=$INFRA_STATE_FAILURE_CLASS attempts=$INFRA_STATE_ATTEMPTS next_at=$INFRA_STATE_NEXT_AT now=$now"
    return 1
  fi
  log "INFRA_HALF_OPEN failure_class=$INFRA_STATE_FAILURE_CLASS attempts=$INFRA_STATE_ATTEMPTS now=$now"
  return 0
}
record_infrastructure_failure() {
  local failure_class="$1" marker="$STATE_DIR/infrastructure" attempts=1 now exponent=0 delay next_at
  now="$(date '+%s')"; [[ "$now" =~ ^[0-9]+$ ]] || now=0
  if [[ -f "$marker" ]] && load_infrastructure_state "$marker" \
      && [[ "$INFRA_STATE_FAILURE_CLASS" == "$failure_class" ]]; then
    attempts=$((INFRA_STATE_ATTEMPTS + 1))
  fi
  exponent=$((attempts - 1))
  [[ "$exponent" -le "$INFRA_BACKOFF_MAX_EXPONENT" ]] || exponent="$INFRA_BACKOFF_MAX_EXPONENT"
  delay="$FAILURE_BACKOFF_BASE_SECONDS"
  while [[ "$exponent" -gt 0 ]]; do delay=$((delay * 4)); exponent=$((exponent - 1)); done
  next_at=$((now + delay))
  if write_infrastructure_state "$failure_class" "$attempts" "$next_at"; then
    log "INFRA_FAILURE failure_class=$failure_class attempts=$attempts next_at=$next_at"
  else
    log "ALERT INFRA_STATE_WRITE_FAILED path=$marker"
  fi
}
clear_infrastructure_failure() { rm -f "$STATE_DIR/infrastructure"; }

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

update_pr_branch() {
  local num="$1" out
  if [[ "$DRYRUN" == "1" ]]; then
    log "DRYRUN #$num BEHIND -> update-branch(本地身份,checks 会触发)"
  elif GH_CAPTURE out update-branch api -X PUT "repos/$REPO/pulls/$num/update-branch"; then
    log "SWEEP #$num BEHIND -> update-branch(本地身份,checks 会触发)"
  else
    set_bounded_failure update-branch
    log "SWEEP #$num update-branch 失败: $(printf '%s' "$out" | head -c 100)"
    return 1
  fi
}
cleanup_lease_scope() {
  if [[ -n "${ACTIVE_BRANCH_LOCK:-}" ]]; then
    release_branch_lock "$ACTIVE_BRANCH_LOCK"
    ACTIVE_BRANCH_LOCK=""
  fi
  release_derived_lease
}
sweep() {
  local remaining floor="${PR_SHEPHERD_GRAPHQL_FLOOR:-200}" rows sorted_rows
  local dev_line dev_oid script_blob infra_failed=0
  [[ "$DRYRUN" == "1" ]] || mkdir -p "$STATE_DIR"
  if [[ "$DRYRUN" != 1 ]] && ! infrastructure_is_eligible; then return 0; fi
  remaining="$(graphql_remaining)" || remaining=""
  # An unreadable budget must not stall the shepherd: if gh is broken the sweep will
  # report that on its own, and a guard that fails closed here would lock the very
  # recalculation that unblocks the queue.
  if [[ "$remaining" =~ ^[0-9]+$ && "$floor" =~ ^[0-9]+$ && "$remaining" -lt "$floor" ]]; then
    log "SWEEP 跳过:GraphQL 余额 $remaining 低于下限 $floor,让配额恢复"
    return 0
  fi
  if ! GH_CAPTURE rows pr-list pr list --repo "$REPO" --state open --limit 1000 \
    --json number,mergeable,mergeStateStatus,autoMergeRequest,headRefName,headRefOid,baseRefOid,statusCheckRollup \
    --jq '.[] | select(.autoMergeRequest != null) | ((.statusCheckRollup | map(select(.__typename == "CheckRun" and .name == "Content-addressed dev baseline admission")) | sort_by(.startedAt // .completedAt // "") | last) // {}) as $admission | [.number,.mergeable,.mergeStateStatus,.headRefName,.headRefOid,.baseRefOid,(.statusCheckRollup|length),($admission.conclusion // "-"),($admission.detailsUrl // "-")] | @tsv'; then
    record_infrastructure_failure "pr-list.${LAST_BOUNDED_RESULT:-exit}"
    return 1
  fi
  if [[ -z "$rows" ]]; then
    [[ "$DRYRUN" == 1 ]] || clear_infrastructure_failure
    return 0
  fi
  if ! run_bounded_capture dev_line git dev-oid "$GIT_TIMEOUT_SECONDS" \
      git -C "$ROOT" ls-remote "$REMOTE" refs/heads/dev; then
    record_infrastructure_failure "dev-oid.${LAST_BOUNDED_RESULT:-exit}"
    return 1
  fi
  read -r dev_oid _ <<< "$dev_line"
  if [[ ! "$dev_oid" =~ ^[0-9a-f]{40}$ ]]; then
    record_infrastructure_failure dev-oid.exit
    log "ALERT INFRA_DEV_OID_INVALID value=$(printf '%s' "$dev_line" | head -c 100)"
    return 1
  fi
  script_blob="$(git hash-object "$LOADED_SCRIPT_PATH" 2>/dev/null || true)"
  [[ "$script_blob" =~ ^[0-9a-f]{40}$ ]] \
    || { record_infrastructure_failure script-blob.exit; log "ALERT INFRA_SCRIPT_BLOB_INVALID"; return 1; }
  sorted_rows="$(printf '%s\n' "$rows" | LC_ALL=C sort -t $'\t' -k1,1n)"
  local recalculated=" " derived_queue_head="" derived="UNKNOWN" expired=0 marker expiry_rc
  while IFS=$'\t' read -r num mergeable mstate head head_oid base_oid checks admission_conclusion admission_url; do
    [[ -n "$num" ]] || continue
    CURRENT_PR="$num"
    RECALC_STATE_TERMINAL=0
    marker="$STATE_DIR/nochecks-$num"
    if [[ "$DRYRUN" != "1" && -f "$marker" ]]; then
      reconcile_wake_head "$num" "$head_oid" "$marker" || true
    fi
    case "$mergeable:$mstate" in
      MERGEABLE:BEHIND|CONFLICTING:*)
        derived="UNKNOWN"
        expired=0
        if pr_has_derived_changes "$num"; then
          derived=1
        elif [[ "$?" == "1" ]]; then
          derived=0
        else
          if [[ "$DRYRUN" != 1 ]]; then
            record_infrastructure_failure "${LAST_FAILURE_CLASS:-pr-diff.exit}"
            infra_failed=1
          fi
          continue
        fi
        if [[ "$mergeable" == "MERGEABLE" ]]; then
          if has_expiry_fingerprint "$admission_conclusion" "$admission_url"; then
            expired=1
          else
            expiry_rc=$?
            if [[ "$expiry_rc" == 2 ]]; then
              if [[ "$DRYRUN" != 1 ]]; then
                record_infrastructure_failure "${LAST_FAILURE_CLASS:-run-view.exit}"
                infra_failed=1
              fi
              continue
            fi
          fi
        fi
        if [[ "$DRYRUN" != 1 && ( "$mergeable" == "CONFLICTING" || "$expired" == 1 ) ]] \
            && ! recalculation_is_eligible "$num" "$head_oid" "$dev_oid" "$script_blob"; then
          continue
        fi
        if [[ "$derived" == "1" && ( "$mergeable" == "MERGEABLE" || "$mstate" == "DIRTY" ) ]]; then
          if [[ -n "$derived_queue_head" ]]; then
            log "SWEEP #$num derived FIFO waiting head=#$derived_queue_head"
            continue
          fi
          derived_queue_head="$num"
          if ! acquire_derived_lease "$num"; then
            log "SWEEP #$num derived FIFO waiting lease_pr=#${DERIVED_LEASE_PR:-unknown} acquired_at=${DERIVED_LEASE_ACQUIRED_AT:-unknown}"
            continue
          fi
          if [[ "$mergeable" == "CONFLICTING" || "$expired" == "1" ]]; then
            recalculated+="$num "
            if recalculate_pr "$num" "$head" "$head_oid"; then
              clear_recalculation_failure "$num"
            else
              case "$LAST_FAILURE_DISPOSITION" in
                retry) RECALC_STATE_TERMINAL=0; log "RECALC_RETRY pr=#$num reason=identity-or-concurrency-change" ;;
                infra)
                  record_infrastructure_failure "${LAST_FAILURE_CLASS:-recalculate.exit}"
                  infra_failed=1; RECALC_STATE_TERMINAL=0
                  ;;
                *)
                  [[ -n "$LAST_FAILURE_CLASS" ]] || set_exit_failure recalculate
                  record_recalculation_failure "$num" "$head_oid" "$dev_oid" "$script_blob" \
                    "$LAST_FAILURE_CLASS" "${LAST_FAILURE_EXIT:-1}" || true
                  ;;
              esac
            fi
          else
            if ! update_pr_branch "$num"; then
              record_infrastructure_failure "${LAST_FAILURE_CLASS:-update-branch.exit}"
              infra_failed=1
            fi
          fi
          cleanup_lease_scope
          if [[ "$RECALC_STATE_TERMINAL" == 1 ]]; then derived_queue_head=""; fi
        elif [[ "$mergeable" == "CONFLICTING" || "$expired" == "1" ]]; then
          if [[ "$recalculated" == *" $num "* ]]; then
            log "SWEEP #$num 本轮已重算一次,跳过重复项"
            continue
          fi
          recalculated+="$num "
          if recalculate_pr "$num" "$head" "$head_oid"; then
            clear_recalculation_failure "$num"
          else
            case "$LAST_FAILURE_DISPOSITION" in
              retry) RECALC_STATE_TERMINAL=0; log "RECALC_RETRY pr=#$num reason=identity-or-concurrency-change" ;;
              infra)
                record_infrastructure_failure "${LAST_FAILURE_CLASS:-recalculate.exit}"
                infra_failed=1; RECALC_STATE_TERMINAL=0
                ;;
              *)
                [[ -n "$LAST_FAILURE_CLASS" ]] || set_exit_failure recalculate
                record_recalculation_failure "$num" "$head_oid" "$dev_oid" "$script_blob" \
                  "$LAST_FAILURE_CLASS" "${LAST_FAILURE_EXIT:-1}" || true
                ;;
            esac
          fi
        else
          if ! update_pr_branch "$num"; then
            record_infrastructure_failure "${LAST_FAILURE_CLASS:-update-branch.exit}"
            infra_failed=1
          fi
        fi
        ;;
      *)
        # BLOCKED/UNKNOWN 且 head 无任何 check:多为 bot push 死锁。
        # 持久 next_at 给 checks 留出挂载时间;每次尝试后扩大退避并受硬上限约束。
        if [[ "$DRYRUN" == "1" ]]; then
          if [[ "$checks" == "0" && ( "$mstate" == "BLOCKED" || "$mstate" == "UNKNOWN" ) ]]; then
            log "DRYRUN #$num head=$head_oid 无 checks -> 观察/唤醒均抑制"
          fi
          continue
        fi
        if [[ "$checks" == "0" && ( "$mstate" == "BLOCKED" || "$mstate" == "UNKNOWN" ) ]]; then
          handle_checkless_wake "$num" "$head_oid" "$marker"
        fi
        ;;
    esac
  done <<< "$sorted_rows"
  CURRENT_PR=none
  if [[ "$infra_failed" == 1 ]]; then return 0; fi
  [[ "$DRYRUN" == 1 ]] || clear_infrastructure_failure
}
