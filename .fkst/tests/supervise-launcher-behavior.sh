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
		<string>set -a; source $host_config; set +a; cd "\$FKST_HOST_ROOT"; exec /bin/bash "\$FKST_PLATFORM_ROOT/scripts/run.sh" supervise --project-root "\$FKST_HOST_ROOT" --platform-root "\$FKST_PLATFORM_ROOT" --platform-packages "$platform_packages" --host-packages "$host_packages" --local-packages "\$FKST_HOST_ROOT/packages" --durable-root "\$FKST_DURABLE_ROOT" --runtime-root "\$FKST_RUNTIME_ROOT" --restart</string>
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

main() {
  local scratch host_config python_bin
  scratch="$(mktemp -d -t supervise-launcher-behavior.XXXXXXXX)"
  SCRATCH="$scratch"
  trap 'rm -rf "$SCRATCH"' EXIT
  host_config="$scratch/host.env"
  python_bin="$(command -v python3)"
  mkdir -p \
    "$scratch/checkout" \
    "$scratch/durable" \
    "$scratch/logs" \
    "$scratch/platform" \
    "$scratch/rate-pool" \
    "$scratch/report-slots" \
    "$scratch/runtime" \
    "$scratch/workflows" \
    "$scratch/worktrees"

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
FKST_HOST_CONFIG=$host_config
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

  printf 'supervise launcher behavior tests: %d passed, %d failed, %d total\n' \
    "$PASSED" "$FAILED" "$((PASSED + FAILED))"
  [[ "$FAILED" -eq 0 ]]
}

main "$@"
