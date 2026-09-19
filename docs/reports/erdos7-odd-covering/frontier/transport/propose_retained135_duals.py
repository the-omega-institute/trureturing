#!/usr/bin/env python3
"""Suggest retained135 dual prices, then repair and check every column exactly."""
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
        require(result.success, 'Numerical suggestion '+result.message)
        y = [max(F(0), F(round(float(-v)*10**12), 10**12)) for v in result.ineqlin.marginals]
        z = [F(round(float(-v)*10**12), 10**12) for v in result.eqlin.marginals]
        # Each repair row is x_k<=1 and has zero coefficients on every other column.
        for k, row in enumerate(lp.unit_rows):
            require(lp.rows[row] == {k: F(1)} and lp.rhs[row] == 1,
                    'A valid independent unit-cap repair row for every variable')
            deficit = objective[k]-sum((a*y[i] for i, a in lp.columns[k]), F(0))\
                -sum((a*z[i] for i, a in lp.eqcolumns[k]), F(0))
            y[row] += max(F(0), deficit)
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
    parser.add_argument('--initial-duals', type=Path,
                        help='Optional JSON object mapping canonical branch hashes to exact duals')
    args = parser.parse_args()
    if args.dependency_directory:
        sys.path.insert(0, str(args.dependency_directory.resolve()))
    spec = importlib.util.spec_from_file_location('retained135', args.base/'frontier/transport/retained135_heavy_comparison.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    io = helper.module('retained135_writer', args.base/'certificate_io.py')
    bank = None if args.initial_duals is None else json.loads(io.read_artifact_bytes(args.initial_duals))
    if bank is not None:
        helper.require(isinstance(bank, dict), 'Initial exact dual bank')
    result = helper.calculate(args.base, bank, proposer(helper.require, helper.encode))
    io.write_certificate_text(args.base/helper.CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('WROTE: complete retained135 face='+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
