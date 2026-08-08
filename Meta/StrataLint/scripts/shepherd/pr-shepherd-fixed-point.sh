#!/usr/bin/env bash
# Truth-graph fixed-point helpers for the pr-shepherd derived lane.
# Sourced by pr-shepherd.sh; relies on its bounded build/git helpers and commit subject.

converge_truth_graph() {
  local num="$1" workspace="$2" isolated_home="$3" round changed max_rounds=3
  for ((round = 1; round <= max_rounds; round++)); do
    if [[ "$round" -gt 1 ]] && ! run_credentialless_bounded emit "$isolated_home" \
      make -C "$workspace" --no-print-directory emit; then
      set_bounded_failure emit
      log "SWEEP #$num emit 失败,不 push"
      return 1
    fi
    if ! run_git_bounded add "$workspace" add -A; then
      set_bounded_failure add
      log "SWEEP #$num truth graph 第 $round 轮 add 失败,不 push"
      return 1
    fi
    if ! run_git_bounded_capture changed fixed-point-diff "$workspace" \
        diff --cached --name-only; then
      set_bounded_failure fixed-point-diff
      log "SWEEP #$num truth graph 第 $round 轮 diff 失败,不 push"
      return 1
    fi
    if [[ -z "$changed" ]]; then
      return 0
    fi
    if ! run_git_bounded commit "$workspace" \
      -c core.hooksPath=/dev/null \
      -c user.name=pr-shepherd \
      -c user.email=pr-shepherd@users.noreply.github.com \
      commit -m "$COMMIT_SUBJECT" >/dev/null; then
      set_bounded_failure commit
      log "SWEEP #$num truth graph 第 $round 轮 commit 失败,不 push"
      return 1
    fi
  done
  set_exit_failure fixed-point-nonconvergent
  log "ALERT #$num truth graph $max_rounds 轮未收敛,不 push"
  return 1
}
