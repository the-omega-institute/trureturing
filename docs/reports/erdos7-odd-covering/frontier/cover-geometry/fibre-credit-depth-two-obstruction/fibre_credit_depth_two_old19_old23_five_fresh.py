#!/usr/bin/env python3
"""Exact common old19/23 source and five fresh arbitrary-height directions."""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations,product
from math import prod
from collections import Counter
from bisect import bisect_right
from hashlib import sha256
import argparse,importlib.util,json

D=256
LAMBDA_STEPS=4096
MAX_NODES=3000000

def need(ok,msg):
    if not ok:raise RuntimeError(msg)
require=need
def tail(p,k):
    if k==0:return F(1)
    if k==1:return F(1,p-1)
    return F(1,(p-2)*p**(k-1))
def pmf(p,k):return tail(p,k)-tail(p,k+1)
def mean(p):return 1+F(1,p-2)
def linear_tail(p,K):
    need(K>=2,'full affine geometric tail starts at2')
    return tail(p,K)*(1+K+F(1,p-1))


FIXED={'capacities': [28, 30, 36, 40, 42], 'thresholds': [1, 8, 10, 12, 16, 20, 24, 32, 40], 'unary_hinge_coefficient_numerators': [[3807, 11613, 0, 70291, 61190, 0, 0, 0, 0], [0, 16717, 0, 43538, 67999, 0, 0, 0, 0], [0, 9544, 0, 17126, 26966, 25256, 40091, 0, 0], [1054, 3672, 0, 11755, 22279, 4955, 59499, 0, 0], [0, 4058, 0, 9732, 16635, 4017, 60575, 0, 0]], 'coefficient_denominator': 100, 'Y_knots': [1, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128, 160, 192, 256, 384], 'kappa': '1/125', 'target': 18000, 'higher_coefficient': 11794}
DEPENDENCIES={'fibre_credit_depth_two_old23_full_height.json': 'ca998ef3ce5e1043cbd1a78a4f9cd4306b12cfb781b219729aa916f0ba016ede', 'fibre_credit_depth_two_old_height_subset_source.py': '86a20f7f01c4f1fb27a7b9eb3e82e4965bb5888c322228a2060c5601fb00a71e', 'fibre_credit_depth_two_old_height_subset_source.json': '2f9e9076607397d6cc49e55dd25eb2253f16db288b65865a87773dd07dc6e25f'}

def source_profile(head,source_rows):
    b={1:F(1)}
    for p in (11,13,17):
        new={}
        for a,w in b.items():
            for z,m in ((1,1-F(1,p-1)),(2,F(1,p-1))):
                new[a*z]=new.get(a*z,F(0))+w*m
        b=new
    knots=(1,8,10,12,16,20,24,32,40,48,64,80,96,128,160,192,256,384)
    cache={}
    def hinge(x,t):
        if (x,t) in cache:return cache[x,t]
        K=max(2,(t+x-1)//x-1);value=F(0)
        for a in range(K):
            y=x*(1+a);J=max(2,(t+y-1)//y-1)
            inner=sum((pmf(23,j)*max(0,y*(1+j)-t) for j in range(J)),F(0))
            need(y*(1+J)>=t,'inner full affine ray')
            inner+=y*linear_tail(23,J)-t*tail(23,J)
            value+=pmf(19,a)*inner
        need(x*(1+K)>=t,'outer full affine ray')
        value+=x*mean(23)*linear_tail(19,K)-t*tail(19,K)
        cache[x,t]=value
        return value

    gh={knots[0]:knots[0]+knots[1]}
    for i in range(1,len(knots)-1):gh[knots[i]]=knots[i+1]-knots[i-1]
    rows=[]
    for h,s in zip(head,source_rows):
        need(h['shape']==s['shape'] and s['quantile8_is_optimal'],'same actual source and top-delta cut')
        delta=F(s['delta']);law={r['value']:F(r['probability']) for r in h['comparison_law']}
        raw=lambda t:sum((w*v*hinge(y*a,t) for y,w in law.items() for a,v in b.items()),F(0))
        topmean=8+raw(8)/delta
        caps={t:(topmean-t if t<=8 else raw(t)/delta) for t in knots}
        eg=1+sum(c*caps[t] for t,c in gh.items())
        rows.append(dict(shape=h['shape'],mean=str(topmean),hinges={str(t):str(c) for t,c in caps.items()},
                         chord_expectation=str(eg),chord_expectation_decimal=float(eg)))
    need(all(F(row['mean'])<=F(rows[0]['mean']) for row in rows),'first shape dominates first moment')
    need(all(F(row['chord_expectation'])<=F(rows[0]['chord_expectation']) for row in rows),'first shape dominates chord fee')
    need(all(F(row['hinges'][str(t)])<=F(rows[0]['hinges'][str(t)]) for row in rows for t in knots),'first shape dominates every hinge')
    out=dict(scope='Exact candidate hinge budgets from the two-full-height comparison laws; no new gate.',
             knots=list(knots),first_shape_dominates_all_listed_costs=True,rows=rows)
    return out

def verify_gate(fixed):
    R=tuple(fixed['capacities']);thresholds=tuple(fixed['thresholds']);coeffs=tuple(tuple(row) for row in fixed['unary_hinge_coefficient_numerators']);knots=tuple(fixed['Y_knots'])
    require(fixed['kappa']=='1/125' and fixed['coefficient_denominator']==100 and fixed['target']==18000,'fixed rational candidate')
    require(R==(28,30,36,40,42) and len(coeffs)==5 and all(len(row)==len(thresholds) for row in coeffs),'five unary penalties')
    require(all(c>=0 for row in coeffs for c in row),'convex nondecreasing unary penalties')
    TARGET=18000;E=125*LAMBDA_STEPS
    slopes=tuple(a+b for a,b in zip(knots,knots[1:]));comps=tuple(combinations(range(5),3));corners=tuple(product((0,1),repeat=5))
    active_terms=tuple(tuple((t,c) for t,c in zip(thresholds,row) if c) for row in coeffs)
    def unary_num(a,den):return sum(c*max(a[i]-t*den,0) for i in range(5) for t,c in active_terms[i])
    def bdata(u):
        P=prod(u)
        if min(u)>0:return P,tuple(P//u[i]//u[j] for i,j in combinations(range(5),2))
        return P,tuple(prod(u[i] for i in J) for J in comps)
    def pair_selection(T,bs,den):return tuple(knots[bisect_right(slopes,(T*b)//(E*den**3))] for b in bs)
    def center_lambda(center):
        den=2*D;u=tuple(R[i]*den-center[i] for i in range(5));P,bs=bdata(u)
        def derivative(T):
            vv=pair_selection(T,bs,den)
            return P-den**2*sum(b*v for b,v in zip(bs,vv))
        if derivative(0)<=0:return 0
        if derivative(LAMBDA_STEPS)>=0:return LAMBDA_STEPS
        lo=0;hi=LAMBDA_STEPS
        while hi-lo>1:
            md=(lo+hi)//2
            if derivative(md)>0:lo=md
            else:hi=md
        def value(T):
            vv=pair_selection(T,bs,den)
            return T*(P-den**2*sum(b*v for b,v in zip(bs,vv)))+E*den**5*sum(v*v for v in vv)
        return max((lo,hi),key=value)
    nodes=0;leaves=0;volume=0;depth_counts=Counter();branch_counts=Counter()
    stack=[((D,)*5,tuple(r*D for r in R),0)]
    E_D5=E*D**4;E_D6=E*D**5;rhs=TARGET*100*E_D6
    while stack:
        low,high,depth=stack.pop();nodes+=1
        if unary_num(low,D)+1000*D>=TARGET*100*D:
            accepted=True;branch='unary-and-lambda-zero'
        else:
            center=tuple(low[i]+high[i] for i in range(5));T=center_lambda(center)
            # Choose one actual affine piece at the center; it supports the convex unary penalty globally.
            unary_slopes=tuple(sum(c for t,c in active_terms[i] if center[i]>=t*2*D) for i in range(5))
            unary_intercept=-sum(c*t for i in range(5) for t,c in active_terms[i] if center[i]>=t*2*D)
            accepted=True;branch='supporting-affine-and-concave-corners'
            for bits in corners:
                a=tuple(high[i] if bits[i] else low[i] for i in range(5));u=tuple(R[i]*D-a[i] for i in range(5));P,bs=bdata(u)
                vv=pair_selection(T,bs,D)
                line=sum(unary_slopes[i]*a[i] for i in range(5))+unary_intercept*D
                lhs=line*E_D5+100*T*(P-D**2*sum(b*v for b,v in zip(bs,vv)))+100*E_D6*sum(v*v for v in vv)
                if lhs<rhs:
                    accepted=False;break
        if accepted:
            leaves+=1;volume+=prod(high[i]-low[i] for i in range(5));depth_counts[depth]+=1;branch_counts[branch]+=1
        else:
            widths=tuple(high[i]-low[i] for i in range(5));j=max(range(5),key=lambda k:widths[k]);mid=(low[j]+high[j])//2
            require(widths[j]>1,'exact grid exhausted: '+str((low,high,depth,'lambda',T,'corner',a,'lower',F(lhs,100*E_D6))))
            high1=list(high);high1[j]=mid;low2=list(low);low2[j]=mid
            stack.append((tuple(low2),high,depth+1));stack.append((low,tuple(high1),depth+1))
        require(nodes<=MAX_NODES,'node cap exceeded before full coverage')
    full_volume=prod((r-1)*D for r in R)
    require(volume==full_volume and nodes==2*leaves-1,'complete binary enclosure and exact volume')
    outside=min(F(sum(c*max(R[i]-t,0) for t,c in active_terms[i]),100)+10 for i in range(5))
    require(outside>=TARGET,'outside box follows from one unary penalty and lambda0 pair baseline')
    out={'scope':'Exact five-direction scalar gate18000 for two old arbitrary-height coordinates; source budget evaluated separately, not Lean.',
         'fixed_penalties':fixed,
         'grid_denominator':D,'lambda_steps':LAMBDA_STEPS,'target':TARGET,
         'nodes':nodes,'leaves':leaves,'depths':dict(sorted(depth_counts.items())),
         'branches':dict(branch_counts),'box_volume':prod(r-1 for r in R),
         'accepted_volume_numerator':str(volume),'full_volume_numerator':str(full_volume),
         'outside_lower':str(outside),'complete_exact_enclosure':True}
    return out

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        need(sha256((directory/name).read_bytes()).hexdigest()==digest,
             'pinned same-source dependency: '+name)
    head=json.loads((directory/'fibre_credit_depth_two_old23_full_height.json').read_text())['rows']
    path=directory/'fibre_credit_depth_two_old_height_subset_source.py'
    spec=importlib.util.spec_from_file_location('old_height_sources',path)
    need(spec is not None and spec.loader is not None,'source loader')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    source=json.loads(json.dumps(module.calculate()))
    need(source==json.loads(path.with_suffix('.json').read_text()),'recomputed actual source agrees with retained result')
    cells=next(row for row in source['subsets'] if row['full_height_axes']==[19,23])['shapes']
    source_rows=[]
    for cell,q in zip(cells,source['two_full_axis_rows']):
        delta=F(cell['retention'])
        need(cell['shape']==q['shape'] and F(q['P_Z_gt8'])<=delta<=F(q['P_Z_ge8']),
             'common source and its exact quantile')
        source_rows.append({'shape':cell['shape'],'delta':str(delta),'quantile8_is_optimal':True})
    profile=source_profile(head,source_rows)
    fixed=dict(FIXED)
    r=fixed['capacities'];kap=F(fixed['kappa'])
    higher=sum(prod(r[i]-1 for i in range(5) if i not in J)
               for size in (3,4,5) for J in combinations(range(5),size))
    need(higher==fixed['higher_coefficient']==11794,'complete higher-support inventory')
    cap=max(kap*prod(r[i]-1 for i in range(5) if i not in J) for J in combinations(range(5),2))
    need(cap==F(11193,25)<640,'same conjugate valid on all unbounded fields')
    costs=[]
    for row in profile['rows']:
        cost=sum(F(c,100)*F(row['hinges'][str(t)])
                 for coefficients in fixed['unary_hinge_coefficient_numerators']
                 for c,t in zip(coefficients,fixed['thresholds']))
        cost+=10*F(row['chord_expectation'])+kap*higher*F(row['mean'])
        need(cost<16791,'actual common-source fee below16791')
        costs.append(cost)
    need(max(costs)==costs[0],'first source shape dominates complete cost')
    gate=verify_gate(fixed)
    hmin=min(F(cell['Haar_factor']) for cell in cells)
    need(hmin==F(763798,62292165),'same paired source Haar factor')
    margin=gate['target']-16791
    density=hmin*margin/(kap*prod(r))
    need(margin==1209 and density==F(1691267,46368370944)>F(1,30000),
         'actual full survivor density')
    return {'scope':'Ordinary actual common source with old19/23 arbitrary finite heights and five fresh arbitrary finite heights; complete exact checks, not Lean or unrestricted Erdos7.',
            'dependency_hashes':DEPENDENCIES,'source_arithmetic_replayed':True,
            'profile':profile,'source_costs':list(map(str,costs)),
            'uniform_source_cost_strict_upper':16791,'max_pair_dual_argument':str(cap),
            'gate':gate,'Haar_source_factor':str(hmin),'conservative_scalar_margin':margin,
            'actual_Haar_lower':str(density),'simple_Haar_lower':'1/30000',
            'old_caps':{'3':2,'5':1,'7':1,'11':1,'13':1,'17':1,'19':'arbitrary finite','23':'arbitrary finite'},
            'fresh_prime_minima':[29,31,37,41,43],'fresh_heights':'arbitrary finite'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with old19/23 five-direction proof')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)

if __name__=='__main__':main()
