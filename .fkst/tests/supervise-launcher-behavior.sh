#!/usr/bin/env bash
set -uo pipefail

REPOSITORY_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)"
PASSED=0
FAILED=0
SCRATCH=""

pass() {
  PASSED=$((PASSED + 1))
  printf 'ok %d - %s\n' "$((PASSED + FAILED))" "$1"
}

fail() {
  FAILED=$((FAILED + 1))
  printf 'not ok %d - %s\n' "$((PASSED + FAILED))" "$1"
}

assert_rendered_supervise_launcher() {
  local scratch="$1" host_config="$2" rendered expected package_data
  local platform_packages host_packages
  rendered="$scratch/rendered.plist"
  expected="$scratch/expected.plist"
  host_config="$(cd -- "$(dirname -- "$host_config")" && pwd -P)/$(basename -- "$host_config")"
  package_data="$(python3 - "$REPOSITORY_ROOT/.fkst/fkst.workspace.toml" <<'PY'
import sys
import tomllib
from pathlib import Path

with open(sys.argv[1], "rb") as handle:
    manifest = tomllib.load(handle)
platform = [
    source for source in manifest["external_sources"]
    if source["id"] == "fkst-packages-platform"
]
print(" ".join(platform[0]["packages"]))
print(" ".join(Path(unit).name for unit in manifest["workspace"]["units"]))
PY
)"
  platform_packages="$(printf '%s\n' "$package_data" | sed -n '1p')"
  host_packages="$(printf '%s\n' "$package_data" | sed -n '2p')"

  cat > "$expected" <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
	<key>KeepAlive</key>
	<true/>
	<key>Label</key>
	<string>local.fkst.synthetic.supervise</string>
	<key>ProcessType</key>
	<string>Background</string>
	<key>ProgramArguments</key>
	<array>
		<string>/bin/zsh</string>
		<string>-lc</string>
		<string>set -a; source "\$1"; set +a; cd "\$FKST_HOST_ROOT"; exec "\$2" "\$FKST_PLATFORM_ROOT/scripts/run.sh" supervise --project-root "\$FKST_HOST_ROOT" --platform-root "\$FKST_PLATFORM_ROOT" --platform-packages "\$3" --host-packages "\$4" --local-packages "\$FKST_HOST_ROOT/packages" --durable-root "\$FKST_DURABLE_ROOT" --runtime-root "\$FKST_RUNTIME_ROOT" --restart</string>
		<string>fkst-supervise</string>
		<string>$host_config</string>
		<string>/bin/bash</string>
		<string>$platform_packages</string>
		<string>$host_packages</string>
	</array>
	<key>RunAtLoad</key>
	<true/>
	<key>StandardErrorPath</key>
	<string>$scratch/logs/supervise-launchd.log</string>
	<key>StandardOutPath</key>
	<string>$scratch/logs/supervise-launchd.log</string>
	<key>ThrottleInterval</key>
	<integer>10</integer>
	<key>WorkingDirectory</key>
	<string>$scratch/checkout</string>
</dict>
</plist>
EOF

  if ! HOST_CONFIG="$host_config" OUTPUT="$rendered" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render; then
    return 1
  fi
  cmp -s "$expected" "$rendered"
}

assert_template_uses_repository_package_placeholders() {
  local template="$REPOSITORY_ROOT/.fkst/launchd/supervise.plist.in"
  grep -Fq '@@FKST_PLATFORM_PACKAGES@@' "$template" \
    && grep -Fq '@@FKST_HOST_PACKAGES@@' "$template" \
    && ! grep -Fq -- '--platform-packages "github-proxy ' "$template" \
    && ! grep -Fq -- '--host-packages "theory-selfgrowth"' "$template"
}

assert_supervise_launcher_conformance() {
  local scratch="$1" host_config="$2" deployed output
  deployed="$scratch/deployed.plist"
  output="$scratch/check.out"
  cp "$scratch/rendered.plist" "$deployed"

  HOST_CONFIG="$host_config" DEPLOYED_LAUNCHER="$deployed" \
    make -s -C "$REPOSITORY_ROOT" supervise-launcher-check > "$output" 2>&1 \
    || return 1
  grep -Fq "supervise-launcher-check: conformant: $deployed" "$output" \
    || return 1

  printf '\n' >> "$deployed"
  if HOST_CONFIG="$host_config" DEPLOYED_LAUNCHER="$deployed" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-check > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "supervise-launcher-check: deployed launcher differs from tracked render: $deployed" \
    "$output"
}

assert_missing_supervise_host_key_is_rejected() {
  local scratch="$1" host_config="$2" incomplete output
  incomplete="$scratch/incomplete-host.env"
  output="$scratch/incomplete.out"
  grep -v '^FKST_SUPERVISE_LAUNCHER_LOG=' "$host_config" > "$incomplete"

  if HOST_CONFIG="$incomplete" OUTPUT="$scratch/incomplete.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "host-contract: required host key FKST_SUPERVISE_LAUNCHER_LOG is unset" \
    "$output"
}

assert_shell_data_is_parameterized() {
  local scratch="$1" host_config="$2" special_config bash_bin rendered arguments_file
  local canonical_special_config injected_marker
  special_config="$scratch/host.env; touch $scratch/injected/marker"
  bash_bin="$scratch/bin/bash wrapper;not-code"
  rendered="$scratch/metachar-rendered.plist"
  arguments_file="$scratch/supervise.arguments"
  injected_marker="$scratch/injected/marker"
  mkdir -p \
    "$(dirname -- "$special_config")" \
    "$(dirname -- "$bash_bin")" \
    "$scratch/injected"
  grep -v '^FKST_BASH_BIN=' "$host_config" > "$special_config"
  printf 'FKST_BASH_BIN="%s"\n' "$bash_bin" >> "$special_config"
  canonical_special_config="$(cd -- "$(dirname -- "$special_config")" && pwd -P)/$(basename -- "$special_config")"
  cat > "$bash_bin" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$SUPERVISE_ARGUMENTS_FILE"
SH
  chmod +x "$bash_bin"

  HOST_CONFIG="$special_config" OUTPUT="$rendered" \
    make -s -C "$REPOSITORY_ROOT" supervise-launcher-render >/dev/null 2>&1 \
    || return 1
  SUPERVISE_ARGUMENTS_FILE="$arguments_file" \
    python3 - "$rendered" "$canonical_special_config" "$bash_bin" "$injected_marker" <<'PY'
import os
import plistlib
import subprocess
import sys

with open(sys.argv[1], "rb") as handle:
    arguments = plistlib.load(handle)["ProgramArguments"]
completed = subprocess.run(
    arguments,
    check=False,
    env={**os.environ, "SUPERVISE_ARGUMENTS_FILE": os.environ["SUPERVISE_ARGUMENTS_FILE"]},
)
if completed.returncode != 0:
    raise SystemExit(f"rendered command exited {completed.returncode}")
if os.path.exists(sys.argv[4]):
    raise SystemExit("host path escaped the data boundary")
if len(arguments) != 8:
    raise SystemExit(f"expected 8 parameterized arguments, got {len(arguments)}")
if arguments[4] != sys.argv[2] or arguments[5] != sys.argv[3]:
    raise SystemExit("host path or executable did not round-trip as an argument")
if sys.argv[2] in arguments[2] or sys.argv[3] in arguments[2]:
    raise SystemExit("host data was embedded in shell source")
PY
  [[ "$?" -eq 0 ]] || return 1
  grep -Fxq "$scratch/platform/scripts/run.sh" "$arguments_file" \
    && grep -Fxq -- '--platform-packages' "$arguments_file" \
    && grep -Fxq -- '--host-packages' "$arguments_file"
}

assert_noncanonical_platform_package_is_rejected() {
  local scratch="$1" host_config="$2" fixture output
  fixture="$scratch/platform-package-fixture"
  output="$scratch/platform-package.out"
  mkdir -p "$fixture/scripts" "$fixture/launchd"
  cp "$REPOSITORY_ROOT/.fkst/scripts/render-supervise-launcher.sh" "$fixture/scripts/"
  cp "$REPOSITORY_ROOT/.fkst/scripts/host-contract.sh" "$fixture/scripts/"
  cp "$REPOSITORY_ROOT/.fkst/launchd/supervise.plist.in" "$fixture/launchd/"
  cp "$REPOSITORY_ROOT/.fkst/host-contract.schema" "$fixture/"
  cp "$REPOSITORY_ROOT/.fkst/deploy.env" "$fixture/"
  sed '1,/"github-proxy"/s/"github-proxy"/"invalid package;id"/' \
    "$REPOSITORY_ROOT/.fkst/fkst.workspace.toml" > "$fixture/fkst.workspace.toml"

  if HOST_CONFIG="$host_config" OUTPUT="$scratch/invalid-package.plist" \
      /bin/bash "$fixture/scripts/render-supervise-launcher.sh" > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "supervise-launcher: invalid workspace package composition" "$output"
}

write_missing_runtime_config() {
  local scratch="$1" host_config="$2" missing="$3"
  grep -Ev '^(FKST_BASH_BIN|FKST_ZSH_BIN|FKST_SUPERVISE_LAUNCHER_LOG)=' \
    "$host_config" > "$missing"
  {
    printf 'FKST_BASH_BIN=%s\n' "$scratch/missing/bash"
    printf 'FKST_ZSH_BIN=%s\n' "$scratch/missing/zsh"
    printf 'FKST_SUPERVISE_LAUNCHER_LOG=%s\n' "$scratch/missing-logs/supervise.log"
  } >> "$missing"
}

assert_nonexistent_runtime_paths_are_rejected_by_renderer() {
  local scratch="$1" host_config="$2" missing output
  missing="$scratch/missing-runtime.env"
  output="$scratch/missing-runtime-render.out"
  write_missing_runtime_config "$scratch" "$host_config" "$missing"

  if HOST_CONFIG="$missing" OUTPUT="$scratch/missing-runtime.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "supervise-launcher: runtime executable is missing or not executable" "$output"
}

assert_nonexistent_runtime_paths_are_rejected_by_checker() {
  local scratch="$1" host_config="$2" missing deployed output
  missing="$scratch/missing-runtime-check.env"
  deployed="$scratch/missing-runtime-deployed.plist"
  output="$scratch/missing-runtime-check.out"
  write_missing_runtime_config "$scratch" "$host_config" "$missing"

  HOST_CONFIG="$missing" OUTPUT="$deployed" \
    make -s -C "$REPOSITORY_ROOT" supervise-launcher-render >/dev/null 2>&1 || :
  [[ -f "$deployed" ]] || printf '<plist/>\n' > "$deployed"
  if HOST_CONFIG="$missing" DEPLOYED_LAUNCHER="$deployed" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-check > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "supervise-launcher: runtime executable is missing or not executable" "$output"
}

assert_missing_runtime_deploy_config_is_rejected() {
  local scratch="$1" host_config="$2" host_root invalid output
  host_root="$scratch/checkout-without-deploy-config"
  invalid="$scratch/missing-deploy-config.env"
  output="$scratch/missing-deploy-config.out"
  mkdir -p "$host_root/packages"
  grep -v '^FKST_HOST_ROOT=' "$host_config" > "$invalid"
  printf 'FKST_HOST_ROOT=%s\n' "$host_root" >> "$invalid"

  if HOST_CONFIG="$invalid" OUTPUT="$scratch/missing-deploy-config.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "supervise-launcher: runtime deploy config is missing or unreadable" "$output"
}

assert_existing_invalid_log_path_is_rejected() {
  local scratch="$1" host_config="$2" invalid invalid_log output
  invalid="$scratch/invalid-log.env"
  invalid_log="$scratch/logs/not-a-regular-file"
  output="$scratch/invalid-log.out"
  mkdir "$invalid_log"
  grep -v '^FKST_SUPERVISE_LAUNCHER_LOG=' "$host_config" > "$invalid"
  printf 'FKST_SUPERVISE_LAUNCHER_LOG=%s\n' "$invalid_log" >> "$invalid"

  if HOST_CONFIG="$invalid" OUTPUT="$scratch/invalid-log.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "supervise-launcher: existing log path is not a writable regular file" "$output"
}

assert_second_host_config_address_is_rejected() {
  local scratch="$1" host_config="$2" second divergent output
  second="$scratch/second-host.env"
  divergent="$scratch/divergent-host.env"
  output="$scratch/divergent-host.out"
  cp "$host_config" "$second"
  grep -v '^FKST_HOST_CONFIG=' "$host_config" > "$divergent"
  printf 'FKST_HOST_CONFIG=%s\n' "$second" >> "$divergent"

  if HOST_CONFIG="$divergent" OUTPUT="$scratch/divergent.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "undeclared key FKST_HOST_CONFIG" "$output"
}

assert_nonexistent_second_host_config_address_is_rejected() {
  local scratch="$1" host_config="$2" divergent output
  divergent="$scratch/nonexistent-second-host.env"
  output="$scratch/nonexistent-second-host.out"
  grep -v '^FKST_HOST_CONFIG=' "$host_config" > "$divergent"
  printf 'FKST_HOST_CONFIG=%s\n' "$scratch/does-not-exist/host.env" >> "$divergent"

  if HOST_CONFIG="$divergent" OUTPUT="$scratch/nonexistent-second.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    return 1
  fi
  grep -Fq "undeclared key FKST_HOST_CONFIG" "$output"
}

main() {
  local scratch host_config python_bin
  scratch="$(mktemp -d -t supervise-launcher-behavior.XXXXXXXX)"
  SCRATCH="$scratch"
  trap 'rm -rf "$SCRATCH"' EXIT
  host_config="$scratch/host.env"
  python_bin="$(command -v python3)"
  mkdir -p \
    "$scratch/checkout/.fkst" \
    "$scratch/checkout/packages" \
    "$scratch/durable" \
    "$scratch/logs" \
    "$scratch/platform/scripts" \
    "$scratch/rate-pool" \
    "$scratch/report-slots" \
    "$scratch/runtime" \
    "$scratch/workflows" \
    "$scratch/worktrees"
  printf '# repository runtime fixture\n' > "$scratch/checkout/.fkst/deploy.env"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$scratch/platform/scripts/run.sh"

  cat > "$host_config" <<EOF
BIN=$scratch/fkst-framework
FKST_HOST_ROOT=$scratch/checkout
FKST_PLATFORM_ROOT=$scratch/platform
FKST_DURABLE_ROOT=$scratch/durable
FKST_RUNTIME_ROOT=$scratch/runtime
FKST_RATE_POOL_ROOT=$scratch/rate-pool
FKST_WORKFLOW_CATALOG_ROOT=$scratch/workflows
PATH=/usr/bin:/bin
FKST_GITHUB_BOT_LOGIN=synthetic-bot
FKST_DEVLOOP_MANAGED_BOT_LOGINS=synthetic-bot
FKST_DEVLOOP_INTEGRATION_BRANCH=integration-synthetic
FKST_RUN_SCRIPT=$scratch/checkout/.fkst/scripts/run.sh
FKST_MAINTENANCE_LOG=$scratch/logs/hourly-maintenance.log
FKST_MAINTENANCE_LAUNCHER_LOG=$scratch/logs/maintenance-launchd.log
FKST_WORKTREE_ROOT=$scratch/worktrees
FKST_REPORT_SLOT_ROOT=$scratch/report-slots
FKST_TIMEOUT_BIN=/usr/bin/timeout
FKST_LAUNCHD_LABEL=local.fkst.synthetic.supervise
FKST_MAINTENANCE_LAUNCHD_LABEL=local.fkst.synthetic.maintenance
FKST_MAINTENANCE_LAUNCHER_PATH=$scratch/local.fkst.synthetic.maintenance.plist
FKST_BASH_BIN=/bin/bash
FKST_ZSH_BIN=/bin/zsh
FKST_PYTHON_BIN=$python_bin
FKST_SUPERVISE_LAUNCHER_LOG=$scratch/logs/supervise-launchd.log
FKST_SUPERVISE_LAUNCHER_PATH=$scratch/local.fkst.synthetic.supervise.plist
source "\$FKST_HOST_ROOT/.fkst/deploy.env"
EOF

  if assert_rendered_supervise_launcher "$scratch" "$host_config"; then
    pass "fictional second-host supervise launcher is portable"
  else
    fail "fictional second-host supervise launcher is portable"
  fi

  if [[ -f "$scratch/rendered.plist" ]] \
      && assert_supervise_launcher_conformance "$scratch" "$host_config"; then
    pass "supervise conformance compares rendered and deployed bytes"
  else
    fail "supervise conformance compares rendered and deployed bytes"
  fi

  if assert_missing_supervise_host_key_is_rejected "$scratch" "$host_config"; then
    pass "supervise renderer rejects a consumer-required host key omission"
  else
    fail "supervise renderer rejects a consumer-required host key omission"
  fi

  if assert_template_uses_repository_package_placeholders; then
    pass "supervise package composition comes from the repository manifest"
  else
    fail "supervise package composition comes from the repository manifest"
  fi

  if assert_shell_data_is_parameterized "$scratch" "$host_config"; then
    pass "supervise host paths and package lists cross zsh as data"
  else
    fail "supervise host paths and package lists cross zsh as data"
  fi

  if assert_noncanonical_platform_package_is_rejected "$scratch" "$host_config"; then
    pass "supervise renderer applies canonical package validation symmetrically"
  else
    fail "supervise renderer applies canonical package validation symmetrically"
  fi

  if assert_nonexistent_runtime_paths_are_rejected_by_renderer "$scratch" "$host_config"; then
    pass "supervise renderer rejects nonexistent runtime paths"
  else
    fail "supervise renderer rejects nonexistent runtime paths"
  fi

  if assert_nonexistent_runtime_paths_are_rejected_by_checker "$scratch" "$host_config"; then
    pass "supervise checker rejects nonexistent runtime paths"
  else
    fail "supervise checker rejects nonexistent runtime paths"
  fi

  if assert_missing_runtime_deploy_config_is_rejected "$scratch" "$host_config"; then
    pass "supervise renderer rejects a missing runtime deploy config"
  else
    fail "supervise renderer rejects a missing runtime deploy config"
  fi

  if assert_existing_invalid_log_path_is_rejected "$scratch" "$host_config"; then
    pass "supervise renderer rejects an existing invalid log path"
  else
    fail "supervise renderer rejects an existing invalid log path"
  fi

  if assert_second_host_config_address_is_rejected "$scratch" "$host_config"; then
    pass "supervise renderer rejects a divergent second host-config address"
  else
    fail "supervise renderer rejects a divergent second host-config address"
  fi

  if assert_nonexistent_second_host_config_address_is_rejected "$scratch" "$host_config"; then
    pass "supervise renderer rejects a nonexistent second host-config address"
  else
    fail "supervise renderer rejects a nonexistent second host-config address"
  fi

  printf 'supervise launcher behavior tests: %d passed, %d failed, %d total\n' \
    "$PASSED" "$FAILED" "$((PASSED + FAILED))"
  [[ "$FAILED" -eq 0 ]]
}

main "$@"
