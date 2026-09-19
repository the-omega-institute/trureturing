#!/usr/bin/env python3
"""Suggest joint135/125 duals using223's exact independent-column repair."""
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
                        help='Optional JSON object of canonical branch hashes and exact duals')
    args = parser.parse_args()
    if args.dependency_directory:
        sys.path.insert(0, str(args.dependency_directory.resolve()))
    spec = importlib.util.spec_from_file_location('pair135125', args.base/'frontier/transport/retained135125_heavy_comparison.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    io = helper.module('pair135125_writer', args.base/'certificate_io.py')
    proposals = helper.module('pair135125_proposer', args.base/'frontier/transport/propose_retained135_duals.py')
    bank = None if args.initial_duals is None else json.loads(io.read_artifact_bytes(args.initial_duals))
    if bank is not None:
        helper.require(isinstance(bank, dict), 'Initial exact dual bank')
    result = helper.calculate(args.base, bank, proposals.proposer(helper.require, helper.encode))
    io.write_certificate_text(args.base/helper.CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('WROTE: complete retained135/125 face='+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
