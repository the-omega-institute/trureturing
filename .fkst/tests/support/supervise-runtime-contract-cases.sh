materialize_pinned_host_run() {
  local scratch="$1" pin source_root destination
  pin="$(python3 - "$REPOSITORY_ROOT/.fkst/fkst.lock" <<'PY'
import sys
import tomllib

with open(sys.argv[1], "rb") as handle:
    lock = tomllib.load(handle)
sources = [
    source for source in lock.get("external_source", [])
    if source.get("id") == "fkst-packages-platform"
]
if len(sources) != 1:
    raise SystemExit("repository lock must contain exactly one fkst-packages-platform source")
resolved = sources[0].get("resolved", {})
pin = resolved.get("rev") if isinstance(resolved, dict) else None
if not isinstance(pin, str):
    raise SystemExit("repository lock platform source has no resolved.rev")
print(pin)
PY
)" || return 1
  source_root="${FKST_PLATFORM:-${FKST_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/fkst-lua-gate}/platform-$pin}"
  destination="$scratch/pinned-host_run.sh"
  if ! git -C "$source_root" cat-file -e "$pin^{commit}" 2>/dev/null; then
    printf 'pinned host_run source lacks commit %s: %s\n' "$pin" "$source_root" >&2
    return 1
  fi
  git -C "$source_root" show "$pin:scripts/host_run.sh" > "$destination" || return 1
  printf 'pinned host_run materialized: pin=%s blob=%s\n' \
    "$pin" "$(git -C "$source_root" rev-parse "$pin:scripts/host_run.sh")"
}

assert_pinned_consumer_source_identity_accepts() {
  local scratch="$1"
  (
    # host_run.sh is a sourced library. Calling its real resolver executes the
    # pinned consumer path without starting the supervise event loop.
    source "$scratch/pinned-host_run.sh"
    HOST_RUN_PROJECT_ROOT="$scratch/checkout"
    HOST_RUN_PLATFORM_ROOT="$scratch/platform"
    HOST_RUN_PLATFORM_PACKAGES="github-proxy"
    HOST_RUN_PACKAGE_ROOTS=()
    host_run_resolve_target_platform_roots
  ) > "$scratch/pinned-consumer.out" 2>&1
}

capture_source_identity_parity() {
  local scratch="$1" host_config="$2" case_id="$3"
  if assert_pinned_consumer_source_identity_accepts "$scratch"; then
    PINNED_CONSUMER_STATUS=0
  else
    PINNED_CONSUMER_STATUS=$?
  fi
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/$case_id.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render \
      > "$scratch/$case_id-preflight.out" 2>&1; then
    REPOSITORY_PREFLIGHT_STATUS=0
  else
    REPOSITORY_PREFLIGHT_STATUS=$?
  fi
  printf 'source identity parity %s: pinned=%s preflight=%s\n' \
    "$case_id" "$PINNED_CONSUMER_STATUS" "$REPOSITORY_PREFLIGHT_STATUS"
}

assert_workspace_rev_drift_is_accepted_with_consumer_parity() {
  local scratch="$1" host_config="$2" manifest backup output status
  manifest="$scratch/checkout/fkst.workspace.toml"
  backup="$manifest.workspace-rev"
  output="$scratch/workspace-rev.out"
  cp "$manifest" "$backup"
  python3 - "$manifest" <<'PY'
import re
import sys
from pathlib import Path

path = Path(sys.argv[1])
text, count = re.subn(
    r'(?m)^rev = "[0-9a-f]{40}"$',
    'rev = "1111111111111111111111111111111111111111"',
    path.read_text(encoding="utf-8"),
    count=1,
)
if count != 1:
    raise SystemExit("workspace rev fixture did not mutate exactly once")
path.write_text(text, encoding="utf-8")
PY
  status=0
  if ! assert_pinned_consumer_source_identity_accepts "$scratch"; then
    status=1
  elif ! HOST_CONFIG="$host_config" OUTPUT="$scratch/workspace-rev.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  fi
  mv "$backup" "$manifest"
  return "$status"
}
assert_lock_intent_drift_is_accepted_with_consumer_parity() {
  local scratch="$1" host_config="$2" lock backup output status
  lock="$scratch/checkout/fkst.lock"
  backup="$lock.intent"
  output="$scratch/lock-intent.out"
  cp "$lock" "$backup"
  python3 - "$lock" <<'PY'
import re
import sys
from pathlib import Path

path = Path(sys.argv[1])
text, count = re.subn(
    r'(\[external_source\.intent\]\nrev = ")[0-9a-f]{40}("\n)',
    r'\g<1>2222222222222222222222222222222222222222\g<2>',
    path.read_text(encoding="utf-8"),
    count=1,
)
if count != 1:
    raise SystemExit("lock intent fixture did not mutate exactly once")
path.write_text(text, encoding="utf-8")
PY
  status=0
  if ! assert_pinned_consumer_source_identity_accepts "$scratch"; then
    status=1
  elif ! HOST_CONFIG="$host_config" OUTPUT="$scratch/lock-intent.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  fi
  mv "$backup" "$lock"
  return "$status"
}

assert_checkout_path_identity_is_accepted_with_consumer_parity() {
  local scratch="$1" host_config="$2" manifest lock manifest_backup lock_backup output status
  manifest="$scratch/checkout/fkst.workspace.toml"
  lock="$scratch/checkout/fkst.lock"
  manifest_backup="$manifest.path-identity"
  lock_backup="$lock.path-identity"
  output="$scratch/path-identity.out"
  cp "$manifest" "$manifest_backup"
  cp "$lock" "$lock_backup"
  python3 - "$manifest" "$lock" "$scratch/platform" <<'PY'
import sys
from pathlib import Path

for name in sys.argv[1:3]:
    path = Path(name)
    text = path.read_text(encoding="utf-8")
    text = text.replace(
        'git = "https://github.com/ChronoAIProject/fkst-packages.git"',
        f'git = "{sys.argv[3]}"',
        1,
    )
    path.write_text(text, encoding="utf-8")
PY
  status=0
  if ! assert_pinned_consumer_source_identity_accepts "$scratch"; then
    status=1
  elif ! HOST_CONFIG="$host_config" OUTPUT="$scratch/path-identity.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  fi
  mv "$manifest_backup" "$manifest"
  mv "$lock_backup" "$lock"
  return "$status"
}

assert_workspace_lock_git_drift_is_rejected() {
  local scratch="$1" host_config="$2" manifest backup output original_origin status
  manifest="$scratch/checkout/fkst.workspace.toml"
  backup="$manifest.git"
  output="$scratch/workspace-lock-git.out"
  cp "$manifest" "$backup"
  sed 's#https://github.com/ChronoAIProject/fkst-packages.git#https://example.invalid/fkst-packages.git#' \
    "$backup" > "$manifest"
  original_origin="$(git -C "$scratch/platform" config --get remote.origin.url)"
  git -C "$scratch/platform" remote set-url origin https://example.invalid/fkst-packages.git
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/workspace-lock-git.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq 'supervise-launcher: target workspace source git differs from target lockfile' \
      "$output"; then
    status=1
  fi
  git -C "$scratch/platform" remote set-url origin "$original_origin"
  mv "$backup" "$manifest"
  return "$status"
}

assert_platform_head_advanced_past_lock_is_accepted() {
  local scratch="$1" host_config="$2" locked_rev platform_head output
  locked_rev="$(git -C "$scratch/platform" rev-parse HEAD)"
  printf 'advanced platform checkout\n' > "$scratch/platform/advanced.txt"
  git -C "$scratch/platform" add advanced.txt
  git -C "$scratch/platform" commit -m advanced >/dev/null
  platform_head="$(git -C "$scratch/platform" rev-parse HEAD)"
  [[ "$platform_head" != "$locked_rev" ]] || return 1

  HOST_CONFIG="$host_config" OUTPUT="$scratch/platform-head-advanced.plist" \
    make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$scratch/platform-head-advanced.out" 2>&1
}

assert_platform_origin_drift_is_rejected() {
  local scratch="$1" host_config="$2" output original_origin status
  output="$scratch/platform-origin.out"
  original_origin="$(git -C "$scratch/platform" config --get remote.origin.url)"
  git -C "$scratch/platform" remote set-url origin https://example.invalid/fkst-packages.git
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/platform-origin.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq 'supervise-launcher: trusted platform checkout identity differs from target workspace source' \
      "$output"; then
    status=1
  fi
  git -C "$scratch/platform" remote set-url origin "$original_origin"
  return "$status"
}

assert_duplicate_workspace_source_is_known_divergence() {
  local scratch="$1" host_config="$2" manifest backup status
  manifest="$scratch/checkout/fkst.workspace.toml"
  backup="$manifest.duplicate-source"
  cp "$manifest" "$backup"
  python3 - "$manifest" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
start = text.index("[[external_sources]]")
path.write_text(text + "\n" + text[start:], encoding="utf-8")
PY
  capture_source_identity_parity "$scratch" "$host_config" duplicate-workspace-source
  status=0
  if [[ "$PINNED_CONSUMER_STATUS" -ne 0 || "$REPOSITORY_PREFLIGHT_STATUS" -ne 2 ]]; then
    status=1
  fi
  mv "$backup" "$manifest"
  return "$status"
}

assert_duplicate_lock_source_is_known_divergence() {
  local scratch="$1" host_config="$2" lock backup status
  lock="$scratch/checkout/fkst.lock"
  backup="$lock.duplicate-source"
  cp "$lock" "$backup"
  python3 - "$lock" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
path.write_text(text + "\n" + text, encoding="utf-8")
PY
  capture_source_identity_parity "$scratch" "$host_config" duplicate-lock-source
  status=0
  if [[ "$PINNED_CONSUMER_STATUS" -ne 0 || "$REPOSITORY_PREFLIGHT_STATUS" -ne 2 ]]; then
    status=1
  fi
  mv "$backup" "$lock"
  return "$status"
}

assert_pinned_rejection_implies_preflight_rejection() {
  local scratch="$1" host_config="$2" manifest lock manifest_backup lock_backup
  local original_origin status=0
  manifest="$scratch/checkout/fkst.workspace.toml"
  lock="$scratch/checkout/fkst.lock"
  manifest_backup="$manifest.rejection-parity"
  lock_backup="$lock.rejection-parity"
  original_origin="$(git -C "$scratch/platform" config --get remote.origin.url)"
  cp "$manifest" "$manifest_backup"
  cp "$lock" "$lock_backup"

  sed 's#https://github.com/ChronoAIProject/fkst-packages.git#https://example.invalid/fkst-packages.git#' \
    "$manifest_backup" > "$manifest"
  git -C "$scratch/platform" remote set-url origin https://example.invalid/fkst-packages.git
  capture_source_identity_parity "$scratch" "$host_config" rejects-workspace-lock-git-drift
  if [[ "$PINNED_CONSUMER_STATUS" -eq 0 || "$REPOSITORY_PREFLIGHT_STATUS" -eq 0 ]]; then
    status=1
  fi
  cp "$manifest_backup" "$manifest"
  git -C "$scratch/platform" remote set-url origin "$original_origin"

  git -C "$scratch/platform" remote set-url origin https://example.invalid/fkst-packages.git
  capture_source_identity_parity "$scratch" "$host_config" rejects-platform-origin-drift
  if [[ "$PINNED_CONSUMER_STATUS" -eq 0 || "$REPOSITORY_PREFLIGHT_STATUS" -eq 0 ]]; then
    status=1
  fi
  git -C "$scratch/platform" remote set-url origin "$original_origin"

  python3 - "$manifest" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
path.write_text(path.read_text(encoding="utf-8") + '''

[[external_sources]]
id = "other-platform"
git = "https://example.invalid/other-platform.git"
rev = "4444444444444444444444444444444444444444"
packages = ["github-proxy"]
libraries = []
''', encoding="utf-8")
PY
  capture_source_identity_parity "$scratch" "$host_config" rejects-ambiguous-package-owner
  if [[ "$PINNED_CONSUMER_STATUS" -eq 0 || "$REPOSITORY_PREFLIGHT_STATUS" -eq 0 ]]; then
    status=1
  fi
  cp "$manifest_backup" "$manifest"

  cat >> "$lock" <<'EOF'

[[external_source]]
id = "other-source"
git = "https://example.invalid/other-source.git"

[external_source.resolved]
rev = "not-a-full-git-sha"
EOF
  capture_source_identity_parity "$scratch" "$host_config" rejects-malformed-nontarget-lock-source
  if [[ "$PINNED_CONSUMER_STATUS" -eq 0 || "$REPOSITORY_PREFLIGHT_STATUS" -eq 0 ]]; then
    status=1
  fi

  mv "$manifest_backup" "$manifest"
  mv "$lock_backup" "$lock"
  git -C "$scratch/platform" remote set-url origin "$original_origin"
  return "$status"
}

assert_lock_libraries_drift_is_rejected() {
  local scratch="$1" host_config="$2" lock backup output status
  lock="$scratch/checkout/fkst.lock"
  backup="$lock.libraries"
  output="$scratch/lock-libraries.out"
  cp "$lock" "$backup"
  sed 's/name = "devloop"/name = "different-library"/' "$backup" > "$lock"
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/lock-libraries.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq 'supervise-launcher: target workspace libraries differ from target lockfile' \
      "$output"; then
    status=1
  fi
  mv "$backup" "$lock"
  return "$status"
}

assert_ambiguous_external_source_is_rejected() {
  local scratch="$1" host_config="$2" manifest backup output status
  manifest="$scratch/checkout/fkst.workspace.toml"
  backup="$manifest.ambiguous-source"
  output="$scratch/ambiguous-source.out"
  cp "$manifest" "$backup"
  python3 - "$manifest" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
text += '''

[[external_sources]]
id = "other-platform"
git = "https://example.invalid/other-platform.git"
rev = "4444444444444444444444444444444444444444"
packages = ["github-proxy"]
libraries = []
'''
path.write_text(text, encoding="utf-8")
PY
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/ambiguous-source.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq "supervise-launcher: requested platform package github-proxy has ambiguous ownership" \
      "$output"; then
    status=1
  fi
  mv "$backup" "$manifest"
  return "$status"
}

assert_malformed_non_target_lock_source_is_rejected() {
  local scratch="$1" host_config="$2" lock backup output status
  lock="$scratch/checkout/fkst.lock"
  backup="$lock.non-target"
  output="$scratch/non-target-lock-source.out"
  cp "$lock" "$backup"
  cat >> "$lock" <<'EOF'

[[external_source]]
id = "other-source"
git = "https://example.invalid/other-source.git"

[external_source.resolved]
rev = "not-a-full-git-sha"
EOF
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/non-target-lock-source.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq \
      'supervise-launcher: target lockfile external source other-source resolved.rev is not a full git SHA' \
      "$output"; then
    status=1
  fi
  mv "$backup" "$lock"
  return "$status"
}

assert_workspace_and_external_package_ownership_is_rejected() {
  local scratch="$1" host_config="$2" renderer_root target_manifest backup output status
  renderer_root="$scratch/ownership-renderer"
  target_manifest="$scratch/checkout/fkst.workspace.toml"
  backup="$target_manifest.ownership"
  cp "$target_manifest" "$backup"
  prepare_renderer_fixture "$renderer_root"
  python3 - \
      "$renderer_root/.fkst/fkst.workspace.toml" \
      "$target_manifest" <<'PY'
import sys
from pathlib import Path

for name in sys.argv[1:]:
    path = Path(name)
    text = path.read_text(encoding="utf-8")
    text = text.replace(
        'units = ["packages/theory-selfgrowth"]',
        'units = ["packages/theory-selfgrowth", "packages/github-proxy"]',
    )
    path.write_text(text, encoding="utf-8")
PY
  mkdir -p "$scratch/checkout/packages/github-proxy"
  printf 'name = "github-proxy"\n' > "$scratch/checkout/packages/github-proxy/fkst.toml"
  output="$scratch/workspace-external-ownership.out"
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/workspace-external-ownership.plist" \
      /bin/bash "$renderer_root/.fkst/scripts/render-supervise-launcher.sh" \
      > "$output" 2>&1; then
    status=1
  elif ! grep -Fq \
      'supervise-launcher: requested platform package github-proxy has ambiguous ownership' \
      "$output"; then
    status=1
  fi
  mv "$backup" "$target_manifest"
  rm -rf "$scratch/checkout/packages/github-proxy"
  return "$status"
}

assert_same_physical_runtime_and_durable_roots_are_rejected() {
  local scratch="$1" host_config="$2" alias_config output status
  alias_config="$scratch/runtime-durable-alias.env"
  output="$scratch/runtime-durable-alias.out"
  ln -s "$scratch/durable" "$scratch/runtime-alias"
  grep -v '^FKST_RUNTIME_ROOT=' "$host_config" > "$alias_config"
  printf 'FKST_RUNTIME_ROOT=%s\n' "$scratch/runtime-alias" >> "$alias_config"

  status=0
  if HOST_CONFIG="$alias_config" OUTPUT="$scratch/runtime-durable-alias.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq \
      'supervise-launcher: runtime root and durable root resolve to the same directory' \
      "$output"; then
    status=1
  fi
  return "$status"
}

assert_unrunnable_local_test_command_is_rejected() {
  local scratch="$1" host_config="$2" renderer_root output status
  renderer_root="$scratch/local-command-renderer"
  prepare_renderer_fixture "$renderer_root"
  sed \
    's/FKST_DEVLOOP_LOCAL_TEST_COMMAND="make preflight"/FKST_DEVLOOP_LOCAL_TEST_COMMAND="missing-local-gate"/' \
    "$renderer_root/.fkst/deploy.env" > "$renderer_root/.fkst/deploy.env.tmp"
  mv "$renderer_root/.fkst/deploy.env.tmp" "$renderer_root/.fkst/deploy.env"
  cp "$renderer_root/.fkst/deploy.env" "$scratch/checkout/.fkst/deploy.env"
  output="$scratch/unrunnable-local-command.out"

  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/unrunnable-local-command.plist" \
      /bin/bash "$renderer_root/.fkst/scripts/render-supervise-launcher.sh" \
      > "$output" 2>&1; then
    status=1
  elif ! grep -Fq \
      'supervise-launcher: local iteration test command is not runnable' \
      "$output"; then
    status=1
  fi
  cp "$REPOSITORY_ROOT/.fkst/deploy.env" "$scratch/checkout/.fkst/deploy.env"
  return "$status"
}
