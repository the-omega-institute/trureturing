#!/usr/bin/env python3
"""Run the preserved initial PR8899 checks from their migrated report path.

The historical script is byte-preserved as research_legacy.py. Only its runtime
root and output destination are adapted. This runner does not run Lean, and
its output must not be read as proof or as validation of the continuation modules.
"""
from __future__ import annotations
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent

def main() -> None:
    spec = importlib.util.spec_from_file_location('pr8899_initial_checks', HERE / 'research_legacy.py')
    if spec is None or spec.loader is None:
        raise RuntimeError('Cannot load the preserved PR8899 check program')
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    checks.ROOT = HERE.parents[2]
    checks.OUT = HERE / 'initial_validation_rerun.json'
    checks.main()

if __name__ == '__main__':
    main()
