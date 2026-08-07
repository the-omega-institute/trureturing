#!/usr/bin/env bash
# Frozen-ledger reconciliation helpers for the pr-shepherd derived lane.
# Sourced by pr-shepherd.sh; relies on its environment (log, worktree paths).

run_ledger_cli() {
  local workspace="$1" isolated_home="$2" command="$3"
  (cd "$workspace" && credentialless "$isolated_home" dotnet run \
    --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
    --configuration Release -- "$command" \
    --candidate-lean-report .lake/build/stratalint/raw-lean-report.json)
}
reconcile_frozen_ledger() {
  local num="$1" workspace="$2" isolated_home="$3" candidate_revision
  candidate_revision="$(git -C "$workspace" rev-parse HEAD)" || {
    log "SWEEP #$num candidate revision 读取失败,不 push"; return 1
  }
  if ! install_revision_file \
      "$workspace" "$REMOTE/dev" "$TRURETURING_ROOT_PATH"; then
    log "SWEEP #$num base Trureturing 恢复失败,不 push"; return 1
  fi
  if ! credentialless "$isolated_home" \
      make -C "$workspace" --no-print-directory lean-report; then
    log "SWEEP #$num base lean-report 失败,不 push"; return 1
  fi
  if ! run_ledger_cli "$workspace" "$isolated_home" ledger-append; then
    log "SWEEP #$num ledger-append 失败,不 push"; return 1
  fi
  if ! install_revision_file \
      "$workspace" "$candidate_revision" "$TRURETURING_ROOT_PATH"; then
    log "SWEEP #$num candidate Trureturing 恢复失败,不 push"; return 1
  fi
  if ! credentialless "$isolated_home" \
      make -C "$workspace" --no-print-directory lean-report; then
    log "SWEEP #$num candidate lean-report 失败,不 push"; return 1
  fi
  if ! run_ledger_cli "$workspace" "$isolated_home" ledger-reattest; then
    log "SWEEP #$num ledger-reattest 失败,不 push"; return 1
  fi
}
