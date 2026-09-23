#!/usr/bin/env python3
"""Numerical branch proposals with exact repair for the selected-deletion mask LP."""
import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True


def proposer(require, encode):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    matrices = {}

    def propose(lp, objective):
        if id(lp) not in matrices:
            def matrix(rows):
                return csr_matrix(([float(a) for row in rows for a in row.values()],
                    ([i for i, row in enumerate(rows) for _ in row], [k for row in rows for k in row])),
                    shape=(len(rows), lp.nvars))
            matrices[id(lp)] = (matrix(lp.rows), np.array(list(map(float, lp.rhs))),
                               matrix(lp.equalities), np.array(list(map(float, lp.erhs))))
        A, b, Ae, be = matrices[id(lp)]
        result = linprog(-np.array(list(map(float, objective))), A_ub=A, b_ub=b,
                        A_eq=Ae, b_eq=be, bounds=(0, None), method='highs')
        require(result.success, 'Numerical proposal '+result.message)
        y = [max(F(0), F(round(float(-v)*10**12), 10**12)) for v in result.ineqlin.marginals]
        z = [F(round(float(-v)*10**12), 10**12) for v in result.eqlin.marginals]

        def deficit(k):
            return objective[k]-sum((a*y[i] for i, a in lp.columns[k]), F(0))\
                -sum((a*z[i] for i, a in lp.eqcolumns[k]), F(0))

        for slot in range(5):
            z[6+slot] += max(F(0), deficit(825+slot), deficit(830+slot))
        for c in range(5):
            z[11+c] += max([F(0)]+[deficit(850+5*c+slot) for slot in range(5)])
        for k, row in lp.e3_zero.items():
            y[row] += max(F(0), deficit(k))
        # A mask-link repair helps its survivor column but can lower raw slack.
        for k, row in enumerate(lp.mask_links):
            y[row] += max(F(0), deficit(875+k))
        for k, row in enumerate(lp.y_link):
            y[row] += max(F(0), deficit(425+k))
        for group, columns in enumerate(lp.lambda_groups):
            z[group] += max([F(0)]+[deficit(k) for k in columns])
        # Raw cap rows repair the last possible loss after all link corrections.
        for cell in range(25):
            y[cell] += max([F(0)]+[deficit(k) for k in range(16*cell, 16*(cell+1))])
        record = encode({'nonzero_inequality_duals': {str(i): v for i, v in enumerate(y) if v},
            'equality_duals': z,
            'raw_objective_upper': sum((a*v for a, v in zip(lp.rhs, y)), F(0))
                                  +sum((a*v for a, v in zip(lp.erhs, z)), F(0))})
        lp.check_dual(objective, record)
        return record

    return propose


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--dependency-directory', type=Path)
    args = parser.parse_args()
    if args.dependency_directory:
        sys.path.insert(0, str(args.dependency_directory.resolve()))
    spec = importlib.util.spec_from_file_location('selected_deletion_mask',
        args.base/'frontier/retained-transport/selected_deletion_mask_heavy_comparison.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    result = helper.calculate(args.base, proposer=proposer(helper.require, helper.encode))
    io = helper.module('selected_deletion_mask_writer', args.base/'certificate_io.py')
    io.write_certificate_text(args.base/helper.CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('WROTE: complete selected-deletion heavy face='+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
