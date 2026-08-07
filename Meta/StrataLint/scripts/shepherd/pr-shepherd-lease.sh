#!/usr/bin/env bash
# Derived PR lease and FIFO sweep support, sourced by pr-shepherd.sh.

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
INFRA_PROBE_REPOSITORY=""
INFRA_PROBE_REF=""
INFRA_PROBE_OID=""
INFRA_PROBE_TOKEN=""
INFRA_PROBE_FAILURE_CLASS=""
INFRA_PROBE_ATTEMPTS=""
INFRA_PROBE_NEXT_AT=""
INFRA_PROBE_EXPIRES_AT=""

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
  DERIVED_LEASE_OBSERVED_TOKEN="$token"
}
write_derived_lease_receipt() {
  local num="$1" token="$2" receipt="${PR_SHEPHERD_LEASE_RECEIPT:-}" temporary
  [[ -n "$receipt" ]] || return 0
  temporary="$receipt.next.$$.$RANDOM"
  (umask 077; {
    printf 'schema=derived-fifo-receipt-v1\n'
    printf 'pr=%s\n' "$num"
    printf 'token=%s\n' "$token"
  } > "$temporary") && mv "$temporary" "$receipt"
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
  if ! write_derived_lease_receipt "$num" "$token"; then
    release_derived_lease
    return 1
  fi
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
  DERIVED_LEASE_OBSERVED_TOKEN=""
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
    DERIVED_LEASE_OBSERVED_TOKEN="invalid"
  fi
  age=$((now - acquired_at))
  [[ "$age" -ge "$DERIVED_LEASE_TTL" ]] || return 1

  observed_pr="$DERIVED_LEASE_PR"
  observed_at="$DERIVED_LEASE_ACQUIRED_AT"
  observed_token="$DERIVED_LEASE_OBSERVED_TOKEN"
  log "FIFO LEASE expired pr=#$observed_pr acquired_at=$observed_at ttl=${DERIVED_LEASE_TTL}s"
  stale="$directory.stale.$$.$RANDOM"
  if ! mv "$directory" "$stale" 2>/dev/null; then
    load_derived_lease "$directory" 2>/dev/null || true
    return 1
  fi
  DERIVED_LEASE_PR=""
  DERIVED_LEASE_ACQUIRED_AT=""
  DERIVED_LEASE_OBSERVED_TOKEN=""
  if [[ "$observed_valid" == "1" ]]; then
    if ! load_derived_lease "$stale" \
        || [[ "$DERIVED_LEASE_PR" != "$observed_pr" \
            || "$DERIVED_LEASE_ACQUIRED_AT" != "$observed_at" \
            || "$DERIVED_LEASE_OBSERVED_TOKEN" != "$observed_token" ]]; then
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
release_derived_lease_token() {
  local token="$1" pr="$2" directory="$STATE_DIR/derived-fifo.lease"
  [[ "$DRYRUN" != "1" && -n "$token" ]] || return 0
  DERIVED_LEASE_OBSERVED_TOKEN=""
  load_derived_lease "$directory" 2>/dev/null || return 0
  [[ "$DERIVED_LEASE_OBSERVED_TOKEN" == "$token" ]] || return 0
  rm -f "$directory/owner"
  if ! rmdir "$directory" 2>/dev/null; then
    log "FIFO LEASE release incomplete pr=#$pr path=$directory"
  fi
}
release_derived_lease() {
  local token="$DERIVED_LEASE_TOKEN" pr="$DERIVED_LEASE_PR"
  [[ -n "$token" ]] || return 0
  release_derived_lease_token "$token" "$pr"
  DERIVED_LEASE_TOKEN=""
  if [[ -n "${PR_SHEPHERD_LEASE_RECEIPT:-}" ]]; then
    rm -f "$PR_SHEPHERD_LEASE_RECEIPT" 2>/dev/null || true
  fi
}
release_derived_lease_receipt() {
  local receipt="$1" line schema="" pr="" token="" seen=" " key value
  [[ -f "$receipt" && -r "$receipt" ]] || return 0
  while IFS= read -r line || [[ -n "$line" ]]; do
    key="${line%%=*}"; value="${line#*=}"
    [[ "$line" == *=* && "$seen" != *" $key "* ]] || return 1
    seen+="$key "
    case "$key" in
      schema) schema="$value" ;; pr) pr="$value" ;; token) token="$value" ;; *) return 1 ;;
    esac
  done < "$receipt"
  [[ "$schema" == derived-fifo-receipt-v1 && "$pr" =~ ^[1-9][0-9]*$ && -n "$token" ]] \
    || return 1
  release_derived_lease_token "$token" "$pr"
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
load_infrastructure_probe() {
  local path="$1" line schema="" token="" failure_class="" attempts="" next_at="" expires_at=""
  local seen=" " key value
  while IFS= read -r line || [[ -n "$line" ]]; do
    key="${line%%=*}"; value="${line#*=}"
    [[ "$line" == *=* && "$seen" != *" $key "* ]] || return 1
    seen+="$key "
    case "$key" in
      schema) schema="$value" ;; token) token="$value" ;; failure_class) failure_class="$value" ;;
      attempts) attempts="$value" ;; next_at) next_at="$value" ;; expires_at) expires_at="$value" ;;
      *) return 1 ;;
    esac
  done < "$path" 2>/dev/null || return 1
  [[ "$schema" == pr-infrastructure-probe-v1 && -n "$token" \
      && "$failure_class" =~ ^[a-z0-9-]+\.(exit|timeout)$ \
      && "$attempts" =~ ^[1-9][0-9]*$ && "$next_at" =~ ^[1-9][0-9]*$ \
      && "$expires_at" =~ ^[1-9][0-9]*$ ]] || return 1
  INFRA_PROBE_TOKEN="$token"
  INFRA_PROBE_FAILURE_CLASS="$failure_class"
  INFRA_PROBE_ATTEMPTS="$attempts"
  INFRA_PROBE_NEXT_AT="$next_at"
  INFRA_PROBE_EXPIRES_AT="$expires_at"
}
acquire_infrastructure_probe() {
  local failure_class="$1" attempts="$2" next_at="$3" now="$4"
  local repository="$STATE_DIR/infrastructure-probe.git" ref=refs/trureturing/half-open
  local candidate candidate_oid old_oid zero=0000000000000000000000000000000000000000
  local observed expires_at token="$$-$now-$RANDOM" attempt
  candidate="$(mktemp "${TMPDIR:-/tmp}/pr-shepherd-infra-probe.XXXXXXXX")" || return 1
  expires_at=$((now + SWEEP_TIMEOUT_SECONDS + KILL_GRACE_SECONDS + 1))
  (umask 077; {
    printf 'schema=pr-infrastructure-probe-v1\n'
    printf 'token=%s\n' "$token"
    printf 'failure_class=%s\n' "$failure_class"
    printf 'attempts=%s\n' "$attempts"
    printf 'next_at=%s\n' "$next_at"
    printf 'expires_at=%s\n' "$expires_at"
  } > "$candidate") || { rm -f "$candidate"; return 1; }
  git init --bare -q "$repository" 2>/dev/null \
    || { rm -f "$candidate"; log "ALERT INFRA_PROBE_STORE_INVALID path=$repository"; return 1; }
  candidate_oid="$(git -C "$repository" hash-object -w "$candidate" 2>/dev/null)" \
    || candidate_oid=""
  [[ "$candidate_oid" =~ ^[0-9a-f]{40}$ ]] \
    || { rm -f "$candidate"; return 1; }
  for attempt in 1 2 3; do
    if old_oid="$(git -C "$repository" rev-parse --verify --quiet "$ref" 2>/dev/null)"; then
      observed="$candidate.observed"
      if ! git -C "$repository" cat-file blob "$old_oid" > "$observed" 2>/dev/null \
          || ! load_infrastructure_probe "$observed"; then
        rm -f "$observed" "$candidate"
        log "ALERT INFRA_PROBE_INVALID ref=$ref"
        return 1
      fi
      rm -f "$observed"
      if [[ "$now" -lt "$INFRA_PROBE_EXPIRES_AT" ]]; then
        rm -f "$candidate"
        return 1
      fi
    else
      old_oid="$zero"
    fi
    if git -C "$repository" update-ref "$ref" "$candidate_oid" "$old_oid" 2>/dev/null; then
      rm -f "$candidate"
      INFRA_PROBE_REPOSITORY="$repository"
      INFRA_PROBE_REF="$ref"
      INFRA_PROBE_OID="$candidate_oid"
      INFRA_PROBE_TOKEN="$token"
      INFRA_PROBE_FAILURE_CLASS="$failure_class"
      INFRA_PROBE_ATTEMPTS="$attempts"
      INFRA_PROBE_NEXT_AT="$next_at"
      INFRA_PROBE_EXPIRES_AT="$expires_at"
      return 0
    fi
  done
  rm -f "$candidate"
  return 1
}
release_infrastructure_probe() {
  if [[ -n "$INFRA_PROBE_REPOSITORY" && -n "$INFRA_PROBE_REF" && -n "$INFRA_PROBE_OID" ]]; then
    git -C "$INFRA_PROBE_REPOSITORY" update-ref -d \
      "$INFRA_PROBE_REF" "$INFRA_PROBE_OID" 2>/dev/null || true
  fi
  INFRA_PROBE_REPOSITORY=""; INFRA_PROBE_REF=""; INFRA_PROBE_OID=""
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
  if ! acquire_infrastructure_probe "$INFRA_STATE_FAILURE_CLASS" \
      "$INFRA_STATE_ATTEMPTS" "$INFRA_STATE_NEXT_AT" "$now"; then
    log "INFRA_HALF_OPEN_BUSY failure_class=$INFRA_STATE_FAILURE_CLASS attempts=$INFRA_STATE_ATTEMPTS"
    return 1
  fi
  if ! load_infrastructure_state "$marker" \
      || [[ "$INFRA_STATE_FAILURE_CLASS" != "$INFRA_PROBE_FAILURE_CLASS" \
          || "$INFRA_STATE_ATTEMPTS" != "$INFRA_PROBE_ATTEMPTS" \
          || "$INFRA_STATE_NEXT_AT" != "$INFRA_PROBE_NEXT_AT" ]]; then
    release_infrastructure_probe
    log "INFRA_HALF_OPEN_STALE path=$marker"
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
  release_infrastructure_probe
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
  script_blob="$(compute_shepherd_identity "$LOADED_SCRIPT_PATH" "$SHEPHERD_MODULE_DIR" 2>/dev/null || true)"
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
          release_derived_lease
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
