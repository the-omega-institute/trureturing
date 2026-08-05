# Formalization-readiness fixtures sourced by hourly-maintenance-behavior.sh.

write_ready_formalize_readiness_provider() {
  local checkout="$1" provider
  provider="$checkout/.claude/skills/fkst-monitor/scripts/status.sh"
  mkdir -p "$(dirname -- "$provider")"
  cat > "$provider" <<'SH'
#!/usr/bin/env bash
[[ "$#" -eq 1 && "$1" == "--formalize-readiness" ]] || exit 2
printf 'ready\n'
SH
}
