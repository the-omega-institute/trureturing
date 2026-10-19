#!/bin/bash
# Shared environment and block resolution for brief orchestration.
OP_BRIEF_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
OP_OPENPROBLEM_DIR=$(cd "$OP_BRIEF_DIR/.." && pwd -P)
if [ "${1:-}" = --selftest ]; then
  python3 "$OP_BRIEF_DIR/selftest.py" "${BASH_SOURCE[0]}"
  exit $?
fi
. "$OP_OPENPROBLEM_DIR/pipeline/common.sh"
op_init
op_scratch
op_main
export PYTHONPATH="$OP_BRIEF_DIR${PYTHONPATH:+:$PYTHONPATH}"
op_block() {
  python3 -c 'import sys; from common import Context, entry; sys.exit(entry(lambda a: print(Context().block(a[1])), minimum=1, maximum=1))' "$1"
}
op_brief_selftest() { python3 "$OP_BRIEF_DIR/selftest.py" "$1"; }
