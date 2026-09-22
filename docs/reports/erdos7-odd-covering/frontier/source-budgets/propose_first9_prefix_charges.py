"""Optional numerical proposal; exact standard-library verification is separate."""
import argparse
from fractions import Fraction as F
from math import ceil
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode=True


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    # Optional packages are needed only when proposing new charges.
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    spec=importlib.util.spec_from_file_location('prefix_exact_model',Path(__file__).with_name('shared_first9_prefix_bound.py'))
    model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)
    require=model.require;io=model._io
    prefix='certificates/source_norms/source-budgets/'
    names=(prefix+'shared_first3_root_queries.json',prefix+'shared_first9_prefix_queries.json',
           'frontier/source-budgets/uniform_phase_capacity_input.json')
    ctx=io.Context(args.base,names,__file__)
    data={'root':ctx.fresh(names[0],'frontier/source-budgets/shared_first3_root_queries.py'),
          'queries':ctx.fresh(names[1],'frontier/source-budgets/shared_first9_prefix_queries.py'),
          'input':ctx.read(names[2])}
    labels,other,state,depth,unary,edges,nextvar=model.build_model(data)
    n=len(labels);rows=[];cols=[];values=[];rhs=[]

    def constraint(items,b):
        row=len(rhs);rhs.append(float(b))
        for col,value in items:rows.append(row);cols.append(col);values.append(value)

    sites=[[[(i,-1)] for a in state[i]] for i in range(n)]
    for i,j,ia,ib,payoff in edges:
        for a,b,w in payoff:constraint(((ia[a],-1),(ib[b],-1)),-w)
        for a,col in enumerate(ia):sites[i][a].append((col,1))
        for b,col in enumerate(ib):sites[j][b].append((col,1))
    for i in range(n):
        for a in range(len(state[i])):constraint(sites[i][a],-unary[i][a])
    objective=np.zeros(nextvar);objective[:n]=1
    matrix=coo_matrix((values,(rows,cols)),shape=(len(rhs),nextvar)).tocsr()
    solution=linprog(objective,A_ub=matrix,b_ub=np.array(rhs),bounds=(0,None),
                     method='highs',options={'time_limit':60.0})
    require(solution.success,'numerical candidate available: '+str(solution.message))
    scale=10**9
    charges=[F(max(0,ceil(float(v)*scale)),scale) for v in solution.x]
    repairs=0;records=[]
    for i,j,ia,ib,payoff in edges:
        for a,b,w in payoff:
            deficit=w-charges[ia[a]]-charges[ib[b]]
            if deficit>0:charges[ia[a]]+=deficit;repairs+=1
            require(charges[ia[a]]+charges[ib[b]]>=w,'exactly repaired payoff domination')
        records.append({'i':i,'j':j,'left':[str(charges[k]) for k in ia],
                        'right':[str(charges[k]) for k in ib]})
    witness={'schema':'shared-first9-prefix-edge-charges-input-v1','labels':labels,
             'states':[list(s) for s in state],'edge_charges':records,
             'proposal_metadata':{'method':'scipy.optimize.linprog with HiGHS',
                 'rounding_scale':scale,'rational_repairs':repairs,'numerical_objective':float(solution.fun),
                 'dimensions':{'variables':nextvar,'constraints':len(rhs),'nonzeros':len(values)}},
             'scope':'Rational witness data; numerical optimality is not claimed.'}
    model.evaluate_charges(data,witness)
    certificate_io=io.load_module('proposal_output_io',args.base/'certificate_io.py')
    certificate_io.write_certificate_text(args.output,json.dumps(witness,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'exact_charge_checks':'PASS'}))


if __name__=='__main__':
    main()
