#!/usr/bin/env python3
"""Optional numerical proposals, accepted only after exact876-column checks."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--dependency-directory',type=Path)
    args = parser.parse_args()
    if args.dependency_directory:
        sys.path.insert(0,str(args.dependency_directory))
    checker = load('j_quadratic_checker',args.base/'frontier/j-geometry/j_face_joint_quadratic_heads.py')
    proposals = load('j_quadratic_solver',args.base/'frontier/cover-geometry/propose_j_face_joint_selected_heads.py')
    solver = [None]

    def propose(lp, objective):
        if solver[0] is None:
            solver[0] = proposals.Solver(lp)
        return solver[0].solve(objective)[1]

    result = checker.calculate(args.base,proposer=propose)
    io = load('j_quadratic_writer',args.base/'certificate_io.py')
    io.write_certificate_text(args.base/checker.CERTIFICATE,json.dumps(result,indent=2)+'\n')
    print('WROTE complete same-source J quadratic certificate.',flush=True)


if __name__=='__main__':
    main()
