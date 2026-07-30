assert_workspace_rev_drift_is_rejected() {
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
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/workspace-rev.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq 'supervise-launcher: target workspace source rev differs from target lockfile' \
      "$output"; then
    status=1
  fi
  mv "$backup" "$manifest"
  return "$status"
}
assert_lock_intent_drift_is_rejected() {
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
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/lock-intent.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq 'supervise-launcher: target lockfile intent.rev differs from resolved.rev' \
      "$output"; then
    status=1
  fi
  mv "$backup" "$lock"
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
  elif ! grep -Fq 'supervise-launcher: trusted platform checkout origin differs from target workspace source' \
      "$output"; then
    status=1
  fi
  git -C "$scratch/platform" remote set-url origin "$original_origin"
  return "$status"
}

assert_duplicate_lock_source_is_rejected() {
  local scratch="$1" host_config="$2" lock backup output status
  lock="$scratch/checkout/fkst.lock"
  backup="$lock.duplicate-source"
  output="$scratch/duplicate-lock-source.out"
  cp "$lock" "$backup"
  python3 - "$lock" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
path.write_text(text + "\n" + text, encoding="utf-8")
PY
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/duplicate-lock-source.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq 'supervise-launcher: target lockfile must contain exactly one fkst-packages-platform source' \
      "$output"; then
    status=1
  fi
  mv "$backup" "$lock"
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
