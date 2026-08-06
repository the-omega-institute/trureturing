#!/usr/bin/env bash
# Derived PR lease and FIFO sweep support, sourced by pr-shepherd.sh.

pr_has_derived_changes() {
  local num="$1" out path
  if ! out="$(GH pr diff "$num" --repo "$REPO" --name-only 2>&1)"; then
    log "ALERT #$num PR file classification=UNKNOWN; skip this sweep: $(printf '%s' "$out" | head -c 100)"
    return 2
  fi
  while IFS= read -r path || [[ -n "$path" ]]; do
    is_derived_conflict "$path" && return 0
  done <<< "$out"
  return 1
}

derived_lease_mtime() {
  stat -f '%m' "$1" 2>/dev/null || stat -c '%Y' "$1" 2>/dev/null
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

update_pr_branch() {
  local num="$1" out
  if [[ "$DRYRUN" == "1" ]]; then
    log "DRYRUN #$num BEHIND -> update-branch(本地身份,checks 会触发)"
  elif out="$(GH api -X PUT "repos/$REPO/pulls/$num/update-branch" 2>&1)"; then
    log "SWEEP #$num BEHIND -> update-branch(本地身份,checks 会触发)"
  else
    log "SWEEP #$num update-branch 失败: $(printf '%s' "$out" | head -c 100)"
    return 1
  fi
}
sweep() {
  local remaining floor="${PR_SHEPHERD_GRAPHQL_FLOOR:-200}"
  remaining="$(graphql_remaining)" || remaining=""
  # An unreadable budget must not stall the shepherd: if gh is broken the sweep will
  # report that on its own, and a guard that fails closed here would lock the very
  # recalculation that unblocks the queue.
  if [[ "$remaining" =~ ^[0-9]+$ && "$floor" =~ ^[0-9]+$ && "$remaining" -lt "$floor" ]]; then
    log "SWEEP 跳过:GraphQL 余额 $remaining 低于下限 $floor,让配额恢复"
    return 0
  fi
  [[ "$DRYRUN" == "1" ]] || mkdir -p "$STATE_DIR"
  local recalculated=" " derived_queue_head="" derived="UNKNOWN" expired=0
  GH pr list --repo "$REPO" --state open --limit 1000 \
    --json number,mergeable,mergeStateStatus,autoMergeRequest,headRefName,headRefOid,baseRefOid,statusCheckRollup \
    --jq '.[] | select(.autoMergeRequest != null) | ((.statusCheckRollup | map(select(.__typename == "CheckRun" and .name == "Content-addressed dev baseline admission")) | sort_by(.startedAt // .completedAt // "") | last) // {}) as $admission | [.number,.mergeable,.mergeStateStatus,.headRefName,.headRefOid,.baseRefOid,(.statusCheckRollup|length),($admission.conclusion // "-"),($admission.detailsUrl // "-")] | @tsv' |
  LC_ALL=C sort -t $'\t' -k1,1n |
  while IFS=$'\t' read -r num mergeable mstate head head_oid base_oid checks admission_conclusion admission_url; do
    case "$mergeable:$mstate" in
      MERGEABLE:BEHIND|CONFLICTING:*)
        derived="UNKNOWN"
        expired=0
        if pr_has_derived_changes "$num"; then
          derived=1
        elif [[ "$?" == "1" ]]; then
          derived=0
        else
          continue
        fi
        if [[ "$mergeable" == "MERGEABLE" ]] \
          && has_expiry_fingerprint "$admission_conclusion" "$admission_url"; then
          expired=1
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
            recalculate_pr "$num" "$head" "$head_oid" || true
          else
            update_pr_branch "$num" || true
          fi
          release_derived_lease
        elif [[ "$mergeable" == "CONFLICTING" || "$expired" == "1" ]]; then
          if [[ "$recalculated" == *" $num "* ]]; then
            log "SWEEP #$num 本轮已重算一次,跳过重复项"
            continue
          fi
          recalculated+="$num "
          recalculate_pr "$num" "$head" "$head_oid" || true
        else
          update_pr_branch "$num" || true
        fi
        ;;
      *)
        # BLOCKED/UNKNOWN 且 head 无任何 check:多为 bot push 死锁。
        # 同一 head 连续两轮观察为空才唤醒,防 checks 挂载延迟误触。
        if [[ "$DRYRUN" == "1" ]]; then
          if [[ "$checks" == "0" && ( "$mstate" == "BLOCKED" || "$mstate" == "UNKNOWN" ) ]]; then
            log "DRYRUN #$num head=$head_oid 无 checks -> 观察/唤醒均抑制"
          fi
          continue
        fi
        marker="$STATE_DIR/nochecks-$num"
        if [[ "$checks" == "0" && ( "$mstate" == "BLOCKED" || "$mstate" == "UNKNOWN" ) ]]; then
          if [[ -f "$marker" && "$(cat "$marker")" == "$head_oid" ]]; then
            wake_pr "$num" && rm -f "$marker"
          else
            printf '%s' "$head_oid" > "$marker"
            log "SWEEP #$num head=$head_oid 无 checks,标记观察(下轮仍空即唤醒)"
          fi
        else
          rm -f "$marker" 2>/dev/null || true
        fi
        ;;
    esac
  done
}
