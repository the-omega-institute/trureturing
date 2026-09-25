"""Exact full-tail comparison for rooted stars/triangles and an old pair graph.

All original labels remain distinct; phases and finite heights are arbitrary.
One normalized actual source uses the complete assigned bad set at each row.
This is an ordinary theorem calculation, not Lean or a selector construction.
"""
from fractions import Fraction as F
from math import prod,ceil
from itertools import combinations
from pathlib import Path
import argparse,json

P=(3,5,7,11,13,17,19)
Q=P[1:]
DEFAULT={5:F(0),7:F(1),11:F(2),13:F(4),17:F(4),19:F(6)}
E0=frozenset(((5,7),(11,19),(17,19)))
EDGES=tuple(combinations(Q,2))
NINE_EDGES=frozenset(((5,7),(5,11),(7,17),(7,19),(11,17),(11,19),
                     (13,17),(13,19),(17,19)))
NINE_THRESHOLDS={5:F(0),7:F(1),11:F(3),13:F(4),17:F(5),19:F(6)}

def require(condition,message):
    if not condition: raise ValueError(message)

def calculate(thresholds=DEFAULT, edges=E0, query_limit=12):
    edges=frozenset(tuple(sorted(e)) for e in edges)
    require(edges<=frozenset(EDGES),'pair graph domain')
    caps={3:F(2),**{p:F(p-1)/(p-2-thresholds[p]) for p in Q}}
    for p in Q:
        require(0<=thresholds[p]<p-2 and 0<caps[p]<p,'valid normalized cap '+str(p))
    def atom(p,k):
        return 1-caps[p]/p if k==0 else caps[p]*F(p-1,p**(k+1))
    def weighted_sum_low(weights,limit):
        table={0:F(1)}
        for p,weight in weights:
            require(weight>=1,'positive low-convolution weight')
            nxt={}
            for m,w in table.items():
                for k in range((limit-m)//weight+1):
                    n=m+weight*k
                    nxt[n]=nxt.get(n,F(0))+w*atom(p,k)
            table=nxt
        return table
    rows=[]
    for qi,q in enumerate(Q):
        previous=Q[:qi]
        neighbors=tuple(p for p in previous if (p,q) in edges)
        t=thresholds[q]; top=ceil(t)-1
        low={m:F(0) for m in range(top+1)}
        if top>=0:
            zero=weighted_sum_low(tuple((p,1) for p in neighbors),top)
            for m,w in zero.items():low[m]+=atom(3,0)*w
            for k3 in range(1,top+1):
                ws=tuple((p,k3+int(p in neighbors)) for p in previous)
                dist=weighted_sum_low(ws,top-k3)
                for m,w in dist.items():low[k3+m]+=atom(3,k3)*w
        mean=caps[3]/2*(1+sum((caps[p]/(p-1) for p in previous),F(0)))
        mean+=sum((caps[p]/(p-1) for p in neighbors),F(0))
        hinge=mean-t+sum(((t-m)*w for m,w in low.items()),F(0))
        charge=hinge/(q-2-t)
        require(hinge>=0 and charge>=0,'nonnegative comparison charge '+str(q))
        rows.append(dict(q=q,t=t,cap=caps[q],previous=previous,neighbors=neighbors,
                         full_mean=mean,low_atoms=low,hinge=hinge,charge=charge))
    beta=sum((r['charge'] for r in rows),F(0));s=1-beta
    lowV={1:F(1)}
    for p in P:
        out={}
        for m,w in lowV.items():
            for n in range(1,(query_limit-1)//m+1):
                out[m*n]=out.get(m*n,F(0))+w*atom(p,n-1)
        lowV=out
    meanV=prod((1+caps[p]/(p-1) for p in P),start=F(1))
    queries=[]
    for t in range(1,query_limit+1):
        hinge=meanV-t+sum(((t-m)*w for m,w in lowV.items() if m<t),F(0))
        margin=(F(566,49)-(t-1))*s-hinge
        bound=t-1+hinge/s if s>0 else None
        queries.append(dict(threshold=t,hinge=hinge,query_upper=bound,gate_margin_lower=49*margin))
    best=min(queries,key=lambda r:r['query_upper']) if s>0 else max(queries,key=lambda r:r['gate_margin_lower'])
    density=prod(caps.values(),start=F(1))
    return dict(scope=__doc__,edges=sorted(edges),thresholds=thresholds,caps=caps,rows=rows,
                beta=beta,survivor_probability_lower=s,query_low_atoms=lowV,
                query_full_mean=meanV,query_candidates=queries,best=best,
                source_density_cap=density,Haar_survivor_lower=s/density,
                passes=(s>0 and best['gate_margin_lower']>0),lean_certification=False)

def final_certificate():
    checks={}
    def need(name,condition):
        if name in checks or not condition: raise ValueError(name)
        checks[name]=True
    result=calculate(NINE_THRESHOLDS,NINE_EDGES)
    need('strictly_retain_previous_three_pair_graph',E0<NINE_EDGES)
    need('exactly_nine_pair_supports',len(NINE_EDGES)==9)
    need('fixed_six_hinge_positive_certificate',result['passes'] and result['best']['threshold']==6)
    need('source_density',result['source_density_cap']==F(2304,77))
    need('full_survivor_positive',result['survivor_probability_lower']>0)
    need('target_query',result['best']['query_upper']<F(566,49))
    for row in result['rows']:
        q=row['q']
        need('low_probability_'+str(q),all(x>=0 for x in row['low_atoms'].values())
             and sum(row['low_atoms'].values(),F(0))<=1)
        need('low_first_moment_'+str(q),sum((F(m)*w for m,w in row['low_atoms'].items()),F(0))<=row['full_mean'])
    gate=result['best']['gate_margin_lower']
    density=result['source_density_cap']
    extended=gate/(616*density)
    need('positive_raw_gate',gate>0)
    need('same_law_pure23_29_continuation',extended>F(1,20000))
    need('continuation_density_cancellation',
         extended==(gate/567)/(density*F(616,567)))
    result['continuation_23_29']={
        'fresh_pure_density_factor':F(616,567),
        'surviving_submeasure_lower':gate/567,
        'Haar_survivor_lower':extended,
        'Haar_simple_lower':F(1,20000),
        'all_original_phases_and_finite_heights_arbitrary':True,
        'retains_one_actual_preconditioning_law':True}
    result['previous_pair_graph']=sorted(E0)
    result['new_pair_supports']=sorted(NINE_EDGES-E0)
    old_three=calculate(DEFAULT,E0)
    all15_default=calculate(DEFAULT,EDGES)
    all15_alternative=calculate({5:F(0),7:F(1),11:F(3),13:F(5),17:F(7),19:F(8)},EDGES)
    need('old_three_graph_passes',old_three['passes'])
    need('all15_default_estimate_fails',not all15_default['passes'])
    need('all15_alternative_estimate_fails',not all15_alternative['passes'])
    result['diagnostics']={
        'scope':'These are three fixed graph/schedule comparisons, not graph or schedule optimality claims. Failed estimates do not rule out another actual law.',
        'old_three_pairs_integrated':old_three,
        'all15_default_schedule':all15_default,
        'all15_alternative_schedule':all15_alternative}
    result['checks']=checks
    result['passed_count']=len(checks)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    result=final_certificate()
    args.output.write_text(json.dumps(result,default=str,indent=2)+'\n')
    print('PASS',result['passed_count'],'checks')
    print('edges',result['edges'])
    print('query_upper',result['best']['query_upper'],float(result['best']['query_upper']))
    print('gate_margin_lower',result['best']['gate_margin_lower'])
    print('Haar_extended_lower',result['continuation_23_29']['Haar_survivor_lower'])
