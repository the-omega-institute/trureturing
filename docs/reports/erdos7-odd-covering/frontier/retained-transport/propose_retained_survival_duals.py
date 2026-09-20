#!/usr/bin/env python3
"""Propose exact repaired deletion duals for all sixteen original tests."""
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
    parser.add_argument('--seed-certificate', type=Path)
    args = parser.parse_args()
    if args.dependency_directory:
        sys.path.insert(0, str(args.dependency_directory.resolve()))
    spec = importlib.util.spec_from_file_location('retained_survival',
        args.base/'frontier/retained-transport/retained_deletion_survival_comparison.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    proposal = helper.module('retained_survival_proposal',
        args.base/'frontier/retained-transport/propose_retained_deletion_duals.py')
    io = helper.module('retained_survival_io', args.base/'certificate_io.py')
    bank = {}
    if args.seed_certificate:
        data = json.loads(io.read_artifact_bytes(args.seed_certificate))
        bank = (helper.decode_dual_bank(data['rational_duals']) if 'rational_duals' in data
                else data['bank'])
    result = helper.calculate(args.base, bank=bank,
        proposer=proposal.proposer(helper.require, helper.encode))
    io.write_certificate_text(args.base/helper.CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('WROTE: all sixteen complete tests and52-cost face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
