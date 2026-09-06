"""Reproducible exact pricing and column-generation checks, seed 20260906.

SciPy and NetworkX propose data. Fraction checks admit every primal/dual/flow
certificate exactly. Nothing here is extracted from Lean, and the full canonical
LP comparisons are synthetic matched-assumption checks, not a published-data
benchmark or an independent review. Run: python verify_pricing.py [--output DIR].
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math, random, time
from fractions import Fraction as Q
from pathlib import Path
from typing import Sequence
import networkx as nx
import numpy as np
from scipy.optimize import linprog
import sympy as sp

SEED=20260906
ZERO=Q(0)

def dot(a,b): return sum((x*y for x,y in zip(a,b)), ZERO)
def benefit(pi, y):
    return sum((pi[i][j] for i in range(len(y)) for j in range(len(y)) if not y[i] and y[j]), ZERO)
def cut_mass(pi, y):
    return sum((pi[i][j] for i in range(len(y)) for j in range(len(y)) if y[i]!=y[j]), ZERO)
def price(pi, lam, y): return benefit(pi,y)-dot(lam,y)

def check_input(pi, color):
    n=len(color)
    if len(pi)!=n or any(len(row)!=n for row in pi): return False
    if any(x<0 for row in pi for x in row) or sum(map(sum,pi))!=1: return False
    return all(i==j or pi[i][j]==0 or color[i]!=color[j] for i in range(n) for j in range(n))

def network_data(pi,color,lam):
    n=len(color)
    field=[sum(pi[j][i] for j in range(n))-sum(pi[i])-2*lam[i] for i in range(n)]
    switched=[-g if c else g for g,c in zip(field,color)]
    source=[max(ZERO,a) for a in switched]; sink=[max(ZERO,-a) for a in switched]
    capacity=[[pi[i][j]+pi[j][i] for j in range(n)] for i in range(n)]
    offset=sum((pi[i][j] for i in range(n) for j in range(n) if i!=j),ZERO)+dot(field,color)+sum(source)
    return capacity,source,sink,offset

def cut_value(cap,source,sink,side):
    n=len(side)
    return sum((sink[i] if side[i] else source[i] for i in range(n)),ZERO)+sum(
        (cap[i][j] for i in range(n) for j in range(n) if side[i] and not side[j]),ZERO)

def check_flow(cap,source,sink,data):
    f=data['internal']; fs=data['from_source']; ft=data['to_sink']; side=data['side']; n=len(side)
    if not (len(f)==len(fs)==len(ft)==len(cap)==n and all(len(row)==n for row in f)): return False
    if not all(0<=f[i][j]<=cap[i][j] for i in range(n) for j in range(n)): return False
    if not all(0<=fs[i]<=source[i] and 0<=ft[i]<=sink[i] for i in range(n)): return False
    if not all(fs[i]+sum(f[j][i] for j in range(n))==ft[i]+sum(f[i]) for i in range(n)): return False
    return cut_value(cap,source,sink,side)==sum(fs)

def pricing_oracle(pi,color,lam):
    if not check_input(pi,color): raise ValueError('Not a bipartite off-diagonal coupling.')
    cap,source,sink,offset=network_data(pi,color,lam); n=len(color); s=n;t=n+1
    denominator=math.lcm(*(x.denominator for row in cap for x in row),*(x.denominator for x in source+sink))
    g=nx.DiGraph();g.add_nodes_from(range(n+2))
    for i in range(n):
        g.add_edge(s,i,capacity=int(source[i]*denominator));g.add_edge(i,t,capacity=int(sink[i]*denominator))
        for j in range(n):
            if i!=j and cap[i][j]:g.add_edge(i,j,capacity=int(cap[i][j]*denominator))
    residual=nx.algorithms.flow.preflow_push(g,s,t)
    reachable={s};queue=[s]
    while queue:
        u=queue.pop()
        for v,e in residual[u].items():
            if e['capacity']-e['flow']>0 and v not in reachable:reachable.add(v);queue.append(v)
    assert t not in reachable
    def flow(u,v):return Q(max(0,residual[u][v]['flow']),denominator) if residual.has_edge(u,v) else ZERO
    data={'internal':[[flow(i,j) for j in range(n)] for i in range(n)],
          'from_source':[flow(s,i) for i in range(n)],'to_sink':[flow(i,t) for i in range(n)],
          'side':[i in reachable for i in range(n)]}
    assert check_flow(cap,source,sink,data)
    y=tuple(int(z)^int(c) for z,c in zip(data['side'],color))
    value=(offset-sum(data['from_source']))/2
    assert price(pi,lam,y)==value
    data.update({'value':value,'column':y,'offset':offset,'common_denominator':denominator})
    return data

def solve_master(pi,r,columns):
    """Propose a restricted optimum; independently check all returned rationals."""
    n=len(r); costs=[benefit(pi,c) for c in columns]
    a=np.array([[1]*len(columns)]+[[c[i] for c in columns] for i in range(n)],dtype=float)
    rhs=[Q(1)]+r
    res=linprog(-np.array(costs,dtype=float),A_eq=a,b_eq=np.array(rhs,dtype=float),bounds=(0,None),method='highs-ds', options={'dual_feasibility_tolerance':1e-10, 'primal_feasibility_tolerance':1e-10})
    if not res.success:raise RuntimeError(res.message)
    weights=[Q(float(x)).limit_denominator(10**9) for x in res.x]
    def valid_weights(w):return all(x>=0 for x in w) and sum(w)==1 and all(sum(w[k]*columns[k][i] for k in range(len(w)))==r[i] for i in range(n))
    if not valid_weights(weights):
        active=[k for k,x in enumerate(res.x) if x>1e-9]
        mat=sp.Matrix([[int(v) for v in a[:,k]] for k in active]).T
        rhsq=sp.Matrix([sp.Rational(x.numerator,x.denominator) for x in rhs])
        sol,params=mat.gauss_jordan_solve(rhsq)
        if params.rows:raise RuntimeError('Primal proposal did not give an independent active support.')
        weights=[ZERO]*len(columns)
        for k,x in zip(active,sol):weights[k]=Q(int(x.p),int(x.q))
    dual=[Q(-float(x)).limit_denominator(10**9) for x in res.eqlin.marginals]
    assert valid_weights(weights)
    objective=dot(weights,costs)
    def valid_dual(d):
        return all(d[0]+dot(d[1:],c)>=cost for c,cost in zip(columns,costs)) and objective==dot(d,rhs)
    if not valid_dual(dual):
        # Floating residuals only propose active equalities. Solve them exactly,
        # then require every restricted inequality and primal/dual equality.
        numeric=-np.asarray(res.eqlin.marginals)
        reconstructed=None
        for eps in (1e-7,1e-9,1e-5,1e-11):
            active=[k for k,c in enumerate(columns) if abs(float(np.dot(numeric,[1]+list(c))-float(costs[k])))<eps]
            rows=sp.Matrix([[1]+list(columns[k]) for k in active])
            independent=list(rows.T.rref()[1])
            if not independent: continue
            chosen=[active[k] for k in independent]
            matrix=sp.Matrix([[1]+list(columns[k]) for k in chosen])
            exact_rhs=sp.Matrix([sp.Rational(costs[k].numerator,costs[k].denominator) for k in chosen])
            solved,parameters,free_columns=matrix.gauss_jordan_solve(exact_rhs,freevar=True)
            # Degenerate optimal faces need not determine a unique dual vector.
            # Rationalize only the free coordinates, then solve tight rows exactly.
            substitutions={}
            for symbol,index in zip(parameters,free_columns):
                q=Q(float(numeric[index])).limit_denominator(10**6)
                substitutions[symbol]=sp.Rational(q.numerator,q.denominator)
            solved=solved.subs(substitutions)
            candidate=[Q(int(x.p),int(x.q)) for x in solved]
            if valid_dual(candidate): reconstructed=candidate;break
        if reconstructed is None:
            Path(__file__).with_name('rejected_dual.json').write_text(json.dumps(clean({'n':n,'columns':columns,'costs':costs,'r':r,'weights':weights,'objective':objective,'dual':dual,'numeric':numeric.tolist(),'res_fun':float(res.fun)}),indent=2))
            raise RuntimeError(('No exact restricted dual certificate from numeric proposal',n))
        dual=reconstructed
    assert valid_dual(dual)
    return weights,dual,objective

def initial_columns(r):
    n=len(r); columns={tuple([0]*n),tuple([1]*n)}
    columns.update(tuple(int(i==j) for i in range(n)) for j in range(n))
    # Shared-threshold coupling makes this master feasible for every supplied r.
    for level in sorted(set([ZERO,Q(1)]+r)):
        columns.add(tuple(int(level<x) for x in r))
    return sorted(columns)

def column_generation(pi,color,r):
    columns=initial_columns(r); steps=[]
    for iteration in range(2000):
        weights,dual,objective=solve_master(pi,r,columns)
        proof=pricing_oracle(pi,color,dual[1:]);gap=proof['value']-dual[0]
        assert gap>=0 # At least one positive restricted primal column is dual-tight.
        steps.append({'columns':len(columns),'objective':objective,'pricing_gap':gap})
        if gap==0:
            # This equality and the checked flow certify the full canonical LP,
            # with every original success row retained, including non-fair rows.
            assert objective==proof['value']+dot(dual[1:],r)
            return {'columns':columns,'weights':weights,'dual':dual,'objective':objective,
                    'pricing_certificate':proof,'steps':steps}
        assert proof['column'] not in columns
        columns.append(proof['column'])
    raise RuntimeError('Column generation iteration budget exhausted.')

def make_instance(n,rng,dense=False):
    color=[i%2 for i in range(n)];rng.shuffle(color)
    masses=[[rng.randrange(1,12) if (i==j or color[i]!=color[j]) and (dense or rng.random()<.65) else 0 for j in range(n)] for i in range(n)]
    if not sum(map(sum,masses)):masses[0][0]=1
    total=sum(map(sum,masses));pi=[[Q(x,total) for x in row] for row in masses]
    return pi,color

def clean(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):clean(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [clean(v) for v in x]
    return x

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path(__file__).parent)
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    rng=random.Random(SEED);counts={'pricing_instances':0,'full_column_price_checks':0,'gauge_identities':0,
      'full_master_comparisons':0,'column_generation_instances':0,'accepted_pricing_calls':0,
      'rejected_mutations':0}; runs=[]
    for n in range(1,9):
        for rep in range(6):
            pi,color=make_instance(n,rng);lam=[Q(rng.randrange(-12,13),7) for _ in range(n)]
            proof=pricing_oracle(pi,color,lam);cap,source,sink,offset=network_data(pi,color,lam)
            for y in itertools.product((0,1),repeat=n):
                z=tuple(v^c for v,c in zip(y,color))
                assert 2*price(pi,lam,y)==offset-cut_value(cap,source,sink,z)
                assert price(pi,lam,y)<=proof['value'];counts['full_column_price_checks']+=1;counts['gauge_identities']+=1
            counts['pricing_instances']+=1
            if rep<3:
                r=[Q(rng.randrange(21),20) for _ in range(n)]
                cg=column_generation(pi,color,r)
                _,_,full=solve_master(pi,r,list(itertools.product((0,1),repeat=n)))
                assert cg['objective']==full
                # Independent analytic bipartite anti-threshold upper value.
                analytic=sum((pi[i][j]*min(1-r[i],r[j]) for i in range(n) for j in range(n) if i!=j),ZERO)
                assert full==analytic
                counts['full_master_comparisons']+=1;counts['column_generation_instances']+=1
                counts['accepted_pricing_calls']+=len(cg['steps'])
                runs.append({'n':n,'canonical_columns':2**n,'generated_columns':len(cg['columns']),
                    'iterations':len(cg['steps']),'objective':full})
    # Larger problems never materialize the canonical response-table list.
    for n in (12,24,48):
        pi,color=make_instance(n,rng,dense=True);r=[Q(rng.randrange(1,20),20) for _ in range(n)]
        cg=column_generation(pi,color,r)
        print(f'completed large master n={n}: {len(cg["columns"])} columns, {len(cg["steps"])} pricing calls',flush=True)
        analytic=sum((pi[i][j]*min(1-r[i],r[j]) for i in range(n) for j in range(n) if i!=j),ZERO)
        assert cg['objective']==analytic
        counts['column_generation_instances']+=1;counts['accepted_pricing_calls']+=len(cg['steps'])
        runs.append({'n':n,'canonical_columns':2**n,'generated_columns':len(cg['columns']),
                    'iterations':len(cg['steps']),'objective':cg['objective']})
        if n==24:
            example={'pi':pi,'color':color,'probability':r,'result':cg}
    import copy
    cap,source,sink,_=network_data(example['pi'],example['color'],example['result']['dual'][1:])
    base=example['result']['pricing_certificate']
    for kind in ('capacity','conservation','negative','cut'):
        bad=copy.deepcopy(base)
        if kind=='capacity':bad['internal'][0][1]=cap[0][1]+1
        elif kind=='conservation':bad['from_source'][0]+=Q(1,999)
        elif kind=='negative':bad['to_sink'][0]=-1
        else:
            # A different cut can be another true optimum. Propose an actually
            # unequal cut value before testing rejection of failed contact.
            chosen=None
            for k in range(len(bad['side'])):
                candidate=list(base['side']);candidate[k]=not candidate[k]
                if cut_value(cap,source,sink,candidate)!=sum(base['from_source']):
                    chosen=candidate;break
            if chosen is None:raise RuntimeError('This mutation instance has no unequal one-flip cut.')
            bad['side']=chosen
        assert not check_flow(cap,source,sink,bad);counts['rejected_mutations']+=1
    # A three-cycle is outside the bipartite contract, not silently approximated.
    triangle=[[ZERO,Q(1,3),ZERO],[ZERO,ZERO,Q(1,3)],[Q(1,3),ZERO,ZERO]]
    for color in itertools.product((0,1),repeat=3):
        assert not check_input(triangle,color);counts['rejected_mutations']+=1
    results={'seed':SEED,'status':'all exact checks passed','counts':counts,'runs':runs,
       'versions':{'networkx':nx.__version__,'numpy':np.__version__,'scipy':__import__('scipy').__version__,'sympy':sp.__version__},
       'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'scope':'fixed rational mediator coupling; bipartite off-diagonal support; arbitrary outcome marginal rows and multipliers',
       'lean_compiled':False,'scribe_compiled':False,'solver_sources_extracted_from_lean':False,
       'published_dataset_benchmark':False,'independent_reviewer':False}
    (args.output/'pricing_validation.json').write_text(json.dumps(clean(results),indent=2)+'\n')
    (args.output/'pricing_certificate_example.json').write_text(json.dumps(clean(example),indent=2)+'\n')
    print(json.dumps(clean(results),indent=2))
if __name__=='__main__':main()
