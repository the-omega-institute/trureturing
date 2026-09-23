#!/usr/bin/env python3
"""Numerical proposals with exact rational repair for the retained-deletion LP."""
import argparse
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode = True


def proposer(require, encode):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    matrices={}
    def propose(lp, objective):
        if id(lp) not in matrices:
            def matrix(rows):
                return csr_matrix(([float(a) for row in rows for a in row.values()],
                    ([i for i,row in enumerate(rows) for _ in row], [k for row in rows for k in row])),
                    shape=(len(rows),lp.nvars))
            matrices[id(lp)]=(matrix(lp.rows),np.array(list(map(float,lp.rhs))),
                              matrix(lp.equalities),np.array(list(map(float,lp.erhs))))
        A,b,Ae,be=matrices[id(lp)]
        result=linprog(-np.array(list(map(float,objective))),A_ub=A,b_ub=b,A_eq=Ae,b_eq=be,
                       bounds=(0,None),method='highs')
        require(result.success,'Numerical proposal '+result.message)
        y=[max(F(0),F(round(float(-v)*10**12),10**12)) for v in result.ineqlin.marginals]
        z=[F(round(float(-v)*10**12),10**12) for v in result.eqlin.marginals]
        def deficit(k):
            return objective[k]-sum((a*y[i] for i,a in lp.columns[k]),F(0))-sum((a*z[i] for i,a in lp.eqcolumns[k]),F(0))
        # These independent equality rows touch only their own extra-deletion columns.
        for s in range(5): z[6+s]+=max(F(0),deficit(825+s),deficit(830+s))
        for c in range(5): z[11+c]+=max([F(0)]+[deficit(850+5*c+s) for s in range(5)])
        for k,row in lp.e3_zero.items():y[row]+=max(F(0),deficit(k))
        # Link-row repairs affect the paired raw column negatively; raw caps repair it below.
        for k,row in enumerate(lp.y_link):y[row]+=max(F(0),deficit(425+k))
        for group,columns in enumerate(lp.lambda_groups):z[group]+=max([F(0)]+[deficit(k) for k in columns])
        for cell in range(25):y[cell]+=max([F(0)]+[deficit(k) for k in range(16*cell,16*(cell+1))])
        record=encode({'nonzero_inequality_duals':{str(i):v for i,v in enumerate(y) if v},
            'equality_duals':z,
            'raw_objective_upper':sum((a*v for a,v in zip(lp.rhs,y)),F(0))+sum((a*v for a,v in zip(lp.erhs,z)),F(0))})
        lp.check_dual(objective,record)
        return record
    return propose


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--dependency-directory',type=Path)
    args=parser.parse_args()
    if args.dependency_directory:sys.path.insert(0,str(args.dependency_directory.resolve()))
    spec=importlib.util.spec_from_file_location('retained_deletion',args.base/'frontier/retained-transport/retained_deletion_heavy_comparison.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    result=module.calculate(args.base,proposer=proposer(module.require,module.encode))
    io=module.module('retained_writer',args.base/'certificate_io.py')
    io.write_certificate_text(args.base/module.CERTIFICATE,json.dumps(result,indent=2)+'\n')
    print('WROTE complete retained-deletion heavy comparison '+str(float(F(result['comparison_upper']))))


if __name__=='__main__':main()
