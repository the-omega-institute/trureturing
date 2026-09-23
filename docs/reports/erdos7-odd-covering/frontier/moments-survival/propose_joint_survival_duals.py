#!/usr/bin/env python3
"""Propose survival duals; reuse existing exact seeds and verify every repair.

Supply --dependency-directory only when using a separately installed SciPy.
The optional location changes this process's import path, not global config.
"""
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
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    spec = importlib.util.spec_from_file_location('joint_survival', args.base/'frontier/moments-survival/joint_selected_survival_comparison.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    matrices = {}

    def propose(lp, objective):
        if id(lp) not in matrices:
            def matrix(rows):
                return csr_matrix(([float(a) for row in rows for a in row.values()],
                    ([i for i, row in enumerate(rows) for _ in row],
                     [j for row in rows for j in row])), shape=(len(rows), lp.nvars))
            matrices[id(lp)] = (matrix(lp.rows), np.array(list(map(float, lp.rhs))),
                                matrix(lp.equalities), np.ones(4))
        A, rhs, Ae, eqrhs = matrices[id(lp)]
        result = linprog(-np.array(list(map(float, objective))), A_ub=A, b_ub=rhs,
                         A_eq=Ae, b_eq=eqrhs, bounds=(0, None), method='highs')
        module.require(result.success, 'Numerical dual proposal: '+result.message)
        y = [max(F(0), F(round(float(-v)*10**12), 10**12)) for v in result.ineqlin.marginals]
        z = [F(round(float(-v)*10**12), 10**12) for v in result.eqlin.marginals]
        # First repair each free equality dual to dominate its lambda columns.
        # These repairs affect no raw-mass column.
        for group, columns in enumerate(lp.lambda_groups):
            required = max(objective[j]-sum((a*y[i] for i, a in lp.columns[j]), F(0)) for j in columns)
            z[group] = max(z[group], required)
        # A source-cap row has coefficient1 on all16 masks of exactly one cell
        # and0 on lambda columns. Its positive maximum deficit fixes that cell.
        for cell in range(25):
            deficit = max(objective[j]-sum((a*y[i] for i, a in lp.columns[j]), F(0))
                          for j in range(16*cell, 16*(cell+1)))
            y[cell] += max(F(0), deficit)
        record = module.encode({'nonzero_inequality_duals': {str(i): v for i, v in enumerate(y) if v},
            'equality_duals': z,
            'raw_objective_upper': sum((a*v for a, v in zip(lp.rhs, y)), F(0))+sum(z)})
        lp.check_dual(objective, record)
        return record

    io = module.module('joint_survival_seed_io', args.base/'certificate_io.py')
    seed = {}
    if args.seed_certificate:
        data = json.loads(io.read_artifact_bytes(args.seed_certificate))
        seed = (module.flatten_dual_buckets(data['rational_dual_buckets']) if 'rational_dual_buckets' in data
                else data.get('bank', data.get('rational_dual_certificates', {})))
    result = module.calculate(args.base, bank=seed, proposer=propose)
    io = module.module('joint_selected_writer', args.base/'certificate_io.py')
    io.write_certificate_text(args.base/module.CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('WROTE: exact feasible duals, complete branch scan and52-cost face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
