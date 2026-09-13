#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
exec "$ROOT/tools/lean-inspector/inspect.sh" --repository "$ROOT" \
  --output "${LEAN_REPORT:-$ROOT/.lake/build/stratalint/raw-lean-report.json}"
