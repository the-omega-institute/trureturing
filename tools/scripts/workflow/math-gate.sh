#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
exec /bin/bash "$ROOT/tools/scripts/ci-stage.sh" current
