#!/usr/bin/env python3
"""Exact full old23 source arithmetic and twelve simultaneous D2 tests.

The ordinary transport proof and the separate target19100 scalar enclosure
are proof inputs. No Lean proof or unrestricted covering claim is made.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
from hashlib import sha256
import argparse,json,importlib.util

def need(ok,message):
    if not ok:raise RuntimeError(message)

H=tuple(tuple(map(F,row)) for row in (
 ('271/86','185/86','100/81','61/81','16/39','7/26','10/77','1/11','4/77','3/77','2/77','1/77'),
 ('263/85','178/85','101/84','30/41','32/79','21/79','5/39','7/78','2/39','1/26','1/39','1/78'),
 ('263/85','178/85','101/84','30/41','32/79','21/79','5/39','7/78','2/39','1/26','1/39','1/78'),
 ('3','2','89/75','11/15','2/5','4/15','2/15','7/75','4/75','1/25','2/75','1/75'),
 ('234/77','157/77','91/76','14/19','2/5','4/15','5/37','7/74','2/37','3/74','1/37','1/74'),
 ('234/77','157/77','91/76','14/19','2/5','4/15','5/37','7/74','2/37','3/74','1/37','1/74'),
))
NMIN=(77,78,78,75,74,74)
MODS=(3,5,9,15,45)
CATS=('same_other_column','other_same_column','other_other_column')
DC={t:F(c) for t,c in (
 (1,'804939/2500'),(8,'59513/100'),(10,'16198/25'),(12,'43069/25'),
 (16,'186823/100'),(20,'33157/50'),(24,'41796/25'),(32,'76293/100'),
 (40,'240'),(48,'360'),(64,'480'),(80,'480'),(96,'720'),(128,'960'),
 (160,'960'),(192,'1440'),(256,'2880'))}
CONSTANT=F(504939,2500)
def fee(x):return CONSTANT+sum(c*max(F(0),x-t) for t,c in DC.items())

def verify_hinges():
    rows=[]
    for ix,(root,cat) in enumerate(product((1,2),CATS)):
        other=3-root
        row,col={'same_other_column':(root,2),'other_same_column':(other,1),'other_other_column':(other,2)}[cat]
        a15=next(x for x in range(15) if x%3==root and x%5==1)
        a45=next(x for x in range(45) if x%9==row and x%5==col)
        originals=((3,0),(9,4),(5,0),(15,a15),(45,a45))
        points=[x for x in range(45) if all(x%m!=a for m,a in originals)]
        n=len(points)
        masks=[sorted({tuple(i for i,x in enumerate(points) if x%d==a) for a in range(d)}-{()}) for d in MODS]
        need(6*n-sum(max(map(len,g)) for g in masks)==NMIN[ix],'literal315 cardinality lower')
        layouts=[]
        for chosen in product(*masks):
            A=[1]*n
            for cylinder in chosen:
                for j in cylinder:A[j]+=1
            layouts.append(tuple(A))
        histograms=sorted(set(tuple(sorted(A)) for A in layouts))
        slacks=[]
        for t,bound in enumerate(H[ix]):
            p,q=bound.numerator,bound.denominator
            J={A:max(sum(max(a+b-t,0) for a,b in zip(A,B)) for B in histograms) for A in histograms}
            least=None
            for A in layouts:
                hA=tuple(max(a-t,0) for a in A)
                lhs=q*(5*sum(hA)+J[tuple(sorted(A))])
                lhs+=sum(max(sum(max(p-q*hA[j],0) for j in C) for C in group) for group in masks)
                slack=6*n*p-lhs
                need(slack>=0,'D2 inequality failed: '+str((ix,t,A)))
                least=slack if least is None else min(least,slack)
            slacks.append(least)
        rows.append(dict(shape=f'root{root}_{cat}',old45_survivors=n,old315_Nmin=NMIN[ix],
                         query_layouts=len(layouts),histogram_pairs=len(histograms)**2,
                         hinge_bounds=list(map(str,H[ix])),minimum_scaled_slacks=slacks))
    need(sum(r['query_layouts'] for r in rows)==27720,'complete query inventory')
    need(sum(r['histogram_pairs'] for r in rows)==141892,'complete histogram inventory')
    return rows

def auxiliary_h():
    multipliers={1:F(1)}
    for q in (11,13,17,19):
        new={}
        for b,m in multipliers.items():
            for f,p in ((1,1-F(1,q-1)),(2,F(1,q-1))):
                new[b*f]=new.get(b*f,F(0))+m*p
        multipliers=new
    need(sum(multipliers.values())==1,'shallow auxiliary probability')
    def tail(k):
        if k==0:return F(1)
        if k==1:return F(1,22)
        return F(1,21*23**(k-1))
    need(tail(1)+F(1,21*22)==F(1,21),'complete23 cylinder-cap sum')
    slope=sum(DC.values());intercept=CONSTANT-sum(t*c for t,c in DC.items())
    a=fee(8);values=[F(0)]
    for t in range(1,13):
        value=F(0)
        for b,m in multipliers.items():
            x=t*b
            cutoff=max(2,(256+x-1)//x-1)
            for k in range(cutoff):
                value+=m*(tail(k)-tail(k+1))*max(F(0),fee(x*(1+k))-a)
            mass=tail(cutoff)
            first=mass*(cutoff+F(1,22))
            need(x*(1+cutoff)>=256,'exact affine tail range')
            value+=m*(slope*x*(mass+first)+(intercept-a)*mass)
        values.append(value)
    need(values[2]>=values[1]>=0,'increasing auxiliary convex goal')
    need(all(values[t+1]-2*values[t]+values[t-1]>=0 for t in range(2,12)),
         'nonnegative coefficients of the old hinge interface')
    return values

DEPENDENCIES={'fibre_credit_depth_two_old23_gate.py': 'fe92d63ddbb096db9bb49dc8cdf7c955f99d7c68c24b06e75803dba73faeb446', 'fibre_credit_depth_two_old23_gate.json': '8263571884835d712c0b70edce8c63d6643d24c6900a43865413352389c68871', 'fibre_credit_depth_two_old_height_hinge_bridge.json': '699dbd9dd90bba1011052121b159938fdfcfe834892077085c6494ab3a411c49'}

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        need(sha256((directory/name).read_bytes()).hexdigest()==digest,
             'pinned old23 gate or unbounded-field interface: '+name)
    bridge=json.loads((directory/'fibre_credit_depth_two_old_height_hinge_bridge.json').read_text())
    need({int(t):F(c) for t,c in bridge['uniform_profile_hinge_coefficients'].items()}==DC
         and F(bridge['uniform_profile_constant'])==CONSTANT,
         'same separate-field aggregate hinge charges')
    need(bridge['capacities']==[28,30,36,40,42,46]
         and F(bridge['kappa'])==F(1,5000) and F(bridge['terminal_g_slope'])==640,
         'same unbounded-field dual coefficients')
    spec=importlib.util.spec_from_file_location('old23_exact_gate',directory/'fibre_credit_depth_two_old23_gate.py')
    need(spec is not None and spec.loader is not None,'load scalar gate')
    gate_module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gate_module)
    gate=json.loads(json.dumps(gate_module.calculate()))
    need(gate==json.loads((directory/'fibre_credit_depth_two_old23_gate.json').read_text()),
         'recomputed full scalar gate agrees with retained result')
    need(gate['target']==19100 and gate['complete_exact_enclosure'],
         'complete target19100 continuous gate')
    rows=verify_hinges();h=auxiliary_h();a=fee(8)
    zs=(F(1,10),F(1,12),F(1,16),F(1,18),F(1,21))
    ds=(F(2750479,31207680),F(3422543,30844800),F(3422543,30844800),
        F(17977,120960),F(4589,34496),F(4589,34496))
    factors=[]
    for ix,row in enumerate(rows):
        extended=H[ix]+(F(0),F(0))
        probabilities=tuple(extended[y-1]-2*extended[y]+extended[y+1] for y in range(1,13))
        need(all(p>=0 for p in probabilities) and sum(probabilities)==1,
             'each hinge table is an actual comparison probability law')
        for t in range(14):
            need(sum(p*max(y-t,0) for y,p in enumerate(probabilities,1))==extended[t],
                 'comparison law recovers every stoploss cut')
        c=H[ix][1]
        delta=c+2+sum(zs)-(c+1)*prod(1+z for z in zs)
        need(delta==ds[ix]>0,'same-shape actual mixed retention')
        R=h[1]+(h[2]-h[1])*H[ix][1]
        R+=sum((h[t+1]-2*h[t]+h[t-1])*H[ix][t] for t in range(2,12))
        need(R==sum(p*h[y] for y,p in enumerate(probabilities,1)),
             'linear functional equals reconstructed-law expectation')
        budget=a+R/delta
        need(budget<19079,'complete separate-field budget below19079')
        D=F(315,NMIN[ix])*prod(F(p,p-1) for p in (11,13,17,19))*F(23,21)
        factor=delta/D;factors.append(factor)
        row.update(relative_retention_lower=str(delta),aggregate_budget_upper=str(budget),
                   comparison_law=[{'value':y,'probability':str(p)} for y,p in enumerate(probabilities,1) if p],
                   aggregate_budget_decimal=float(budget),reference_Haar_density_cap=str(D),
                   restricted_normalized_to_Haar_factor=str(factor),
                   strict_gap_below19079=str(F(19079)-budget))
    hmin=min(factors)
    need(hmin==F(2750479,186876495),'paired source-Haar conversion')
    rho=hmin*21*5000/prod((28,30,36,40,42,46))
    need(rho==F(13752395,20796214368384)>F(1,1600000),'full actual Haar reserve')
    out=dict(scope='Ordinary actual old23 full-height source proof with exact hinge arithmetic; replays the full scalar gate19100. No new Lean verification or unrestricted noncoverage claim.',
             old_caps={'3':2,'5':1,'7':1,'11':1,'13':1,'17':1,'19':1,'23':'arbitrary finite'},
             fresh_prime_minima=[29,31,37,41,43,47],fresh_heights='arbitrary finite',
             rows=rows,convex_h_values=list(map(str,h)),constant_after_restriction=str(a),
             aggregate_budget_strict_upper=19079,required_scalar_gate=19100,
             conservative_scalar_margin=21,Haar_source_factor=str(hmin),
             full_Haar_survivor_lower=str(rho),full_Haar_survivor_decimal=float(rho),
             d2_layout_threshold_checks=12*27720,histogram_pair_threshold_checks=12*141892,
             no_auxiliary_dependent_query_max_exchange=True,no_R_monotonicity_assumption=True,
             lean_verification=False)
    out['dependency_hashes']=DEPENDENCIES
    out['scalar_gate_replayed']={'target':gate['target'],'nodes':gate['nodes'],
                                'leaves':gate['leaves'],'box_volume':gate['box_volume']}
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with full-height old23 source')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)

if __name__=='__main__':main()
