maintenance_delegates_launchd_conformance_gate() (
  load_implementation || exit 1
  local root calls
  root="$(mktemp -d -t hourly-maintenance-launchd-delegate.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  write_host_contract_fixture "$root" second-host-bot integration-second-host
  calls="$root/make.calls"
  cat > "$root/bin/make" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$FKST_FAKE_MAKE_CALLS"
exit 0
SH
  chmod +x "$root/bin/make"
  sync_platform() { return 0; }
  sync_checkout() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  restart_if_needed() { return 0; }

  FKST_FAKE_MAKE_CALLS="$calls" FKST_MAKE_BIN="$root/bin/make" \
    main --host-config "$FIXTURE_HOST_CONFIG" \
    || fail "maintenance rejected a successful launchd conformance gate"
  command grep -Fxq -- \
    "-s -C $REPOSITORY_ROOT launchd-conformance-check" "$calls" \
    || fail "maintenance did not delegate launchd conformance through its Make target"
)

launchd_conformance_failure_fails_maintenance_cycle() (
  load_implementation || exit 1
  local root output enumerator
  root="$(mktemp -d -t hourly-maintenance-launchd-failure.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  write_host_contract_fixture "$root" second-host-bot integration-second-host
  output="$root/maintenance.out"
  enumerator="$root/bin/launchd-enumerator"
  cat > "$enumerator" <<'SH'
#!/usr/bin/env bash
exit 23
SH
  chmod +x "$enumerator"
  sync_platform() { return 0; }
  sync_checkout() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  restart_if_needed() { return 0; }

  if FKST_LAUNCHD_ENUMERATOR="$enumerator" FKST_MAKE_BIN=/usr/bin/make \
      main --host-config "$FIXTURE_HOST_CONFIG" >"$output" 2>&1; then
    fail "launchd conformance failure was swallowed by the maintenance cycle"
  fi
  command grep -Fq \
    'launchd-conformance-check: launchd membership enumerator failed with exit 23' \
    "$output" \
    || fail "maintenance failure did not preserve the actionable gate diagnostic: $(<"$output")"
)

missing_launchd_provider_key_fails_maintenance_cycle() (
  load_implementation || exit 1
  local root output incomplete
  root="$(mktemp -d -t hourly-maintenance-launchd-provider.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  write_host_contract_fixture "$root" second-host-bot integration-second-host
  output="$root/maintenance.out"
  incomplete="$root/incomplete-host.env"
  command grep -v '^export FKST_PYTHON_BIN=' "$FIXTURE_HOST_CONFIG" > "$incomplete"
  sync_platform() { return 0; }
  sync_checkout() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  restart_if_needed() { return 0; }

  if FKST_MAKE_BIN=/usr/bin/make \
      main --host-config "$incomplete" >"$output" 2>&1; then
    fail "maintenance accepted a host contract missing a launchd provider key"
  fi
  command grep -Fq 'required host key FKST_PYTHON_BIN is unset' "$output" \
    || fail "missing launchd provider key was not named actionably: $(<"$output")"
)
