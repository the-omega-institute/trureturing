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

assert_lock_rev_platform_head_drift_is_rejected() {
  local scratch="$1" host_config="$2" manifest lock manifest_backup lock_backup output status
  manifest="$scratch/checkout/fkst.workspace.toml"
  lock="$scratch/checkout/fkst.lock"
  manifest_backup="$manifest.platform-head"
  lock_backup="$lock.platform-head"
  output="$scratch/platform-head.out"
  cp "$manifest" "$manifest_backup"
  cp "$lock" "$lock_backup"
  python3 - "$manifest" "$lock" <<'PY'
import re
import sys
from pathlib import Path

for name in sys.argv[1:]:
    path = Path(name)
    text = re.sub(
        r'(?m)^rev = "[0-9a-f]{40}"$',
        'rev = "3333333333333333333333333333333333333333"',
        path.read_text(encoding="utf-8"),
    )
    path.write_text(text, encoding="utf-8")
PY
  status=0
  if HOST_CONFIG="$host_config" OUTPUT="$scratch/platform-head.plist" \
      make -s -C "$REPOSITORY_ROOT" supervise-launcher-render > "$output" 2>&1; then
    status=1
  elif ! grep -Fq 'supervise-launcher: trusted platform checkout HEAD differs from target lockfile' \
      "$output"; then
    status=1
  fi
  mv "$manifest_backup" "$manifest"
  mv "$lock_backup" "$lock"
  return "$status"
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
