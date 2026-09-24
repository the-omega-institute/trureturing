#!/usr/bin/env python3
"""Propose exact-checked retained135/125 survival duals and write their full consumer."""
import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--dependency-directory', type=Path)
    parser.add_argument('--initial-duals', type=Path,
                        help='Optional canonical branch-key bank of exact rational duals')
    args = parser.parse_args()
    if args.dependency_directory:
        sys.path.insert(0, str(args.dependency_directory.resolve()))
    spec = importlib.util.spec_from_file_location('retained135125_survival',
        args.base/'frontier/retained-transport/retained135125_survival_comparison.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    io = helper.module('retained135125_survival_writer', args.base/'certificate_io.py')
    proposal = helper.module('retained135125_survival_proposal', args.base/'frontier/retained-transport/propose_retained135_duals.py')
    bank = None if args.initial_duals is None else json.loads(io.read_artifact_bytes(args.initial_duals))
    if bank is not None:
        helper.require(isinstance(bank, dict), 'Initial complete exact dual bank')
    result = helper.calculate(args.base, bank, proposal.proposer(helper.require, helper.encode))
    io.write_certificate_text(args.base/helper.CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('WROTE: complete retained135/125 survival face='+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
