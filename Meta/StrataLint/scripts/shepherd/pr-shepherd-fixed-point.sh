#!/usr/bin/env bash
# Truth-graph fixed-point helpers for the pr-shepherd derived lane.
# Sourced by pr-shepherd.sh; relies on its environment (log, credentialless, commit subject).

converge_truth_graph() {
  local num="$1" workspace="$2" isolated_home="$3" round max_rounds=3
  for ((round = 1; round <= max_rounds; round++)); do
    if [[ "$round" -gt 1 ]] && ! credentialless "$isolated_home" \
      make -C "$workspace" --no-print-directory emit; then
      log "SWEEP #$num emit 失败,不 push"
      return 1
    fi
    git -C "$workspace" add -A
    if git -C "$workspace" diff --cached --quiet; then
      return 0
    fi
    if ! git -C "$workspace" \
      -c core.hooksPath=/dev/null \
      -c user.name=pr-shepherd \
      -c user.email=pr-shepherd@users.noreply.github.com \
      commit -m "$COMMIT_SUBJECT" >/dev/null; then
      log "SWEEP #$num truth graph 第 $round 轮 commit 失败,不 push"
      return 1
    fi
  done
  log "ALERT #$num truth graph $max_rounds 轮未收敛,不 push"
  return 1
}
