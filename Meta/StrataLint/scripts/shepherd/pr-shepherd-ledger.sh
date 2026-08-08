#!/usr/bin/env bash
# Frozen-ledger reconciliation helpers for the pr-shepherd derived lane.
# Sourced by pr-shepherd.sh; relies on its environment (log, worktree paths).

run_ledger_cli() {
  local workspace="$1" isolated_home="$2" command="$3"
  run_credentialless_bounded "$command" "$isolated_home" \
    /bin/bash -c 'cd "$1"; shift; exec "$@"' pr-shepherd-workspace "$workspace" \
      dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
      --configuration Release -- "$command" \
      --candidate-lean-report .lake/build/stratalint/raw-lean-report.json
}
install_revision_file() {
  local workspace="$1" revision="$2" path="$3" step="$4" temporary
  temporary="$(mktemp "${TMPDIR:-/tmp}/pr-shepherd-revision.XXXXXXXX")" || return 1
  if ! run_bounded_to_file "$temporary" git "$step" "$GIT_TIMEOUT_SECONDS" \
      git -C "$workspace" show "$revision:$path"; then
    rm -f "$temporary"
    return 1
  fi
  if ! mv "$temporary" "$workspace/$path"; then
    rm -f "$temporary"
    return 1
  fi
}
reconcile_frozen_ledger() {
  local num="$1" workspace="$2" isolated_home="$3" candidate_revision
  if ! run_git_bounded_capture candidate_revision ledger-candidate-revision "$workspace" \
      rev-parse HEAD; then
    set_bounded_failure ledger-candidate-revision
    log "SWEEP #$num candidate revision 读取失败,不 push"; return 1
  fi
  if ! install_revision_file \
      "$workspace" "$REMOTE/dev" "$TRURETURING_ROOT_PATH" ledger-base-source; then
    set_bounded_failure ledger-base-source
    log "SWEEP #$num base Trureturing 恢复失败,不 push"; return 1
  fi
  if ! run_credentialless_bounded ledger-base-report "$isolated_home" \
      make -C "$workspace" --no-print-directory lean-report; then
    set_bounded_failure ledger-base-report
    log "SWEEP #$num base lean-report 失败,不 push"; return 1
  fi
  if ! run_ledger_cli "$workspace" "$isolated_home" ledger-append; then
    set_bounded_failure ledger-append
    log "SWEEP #$num ledger-append 失败,不 push"; return 1
  fi
  if ! install_revision_file \
      "$workspace" "$candidate_revision" "$TRURETURING_ROOT_PATH" ledger-candidate-source; then
    set_bounded_failure ledger-candidate-source
    log "SWEEP #$num candidate Trureturing 恢复失败,不 push"; return 1
  fi
  if ! run_credentialless_bounded ledger-candidate-report "$isolated_home" \
      make -C "$workspace" --no-print-directory lean-report; then
    set_bounded_failure ledger-candidate-report
    log "SWEEP #$num candidate lean-report 失败,不 push"; return 1
  fi
  if ! run_ledger_cli "$workspace" "$isolated_home" ledger-reattest; then
    set_bounded_failure ledger-reattest
    log "SWEEP #$num ledger-reattest 失败,不 push"; return 1
  fi
}
