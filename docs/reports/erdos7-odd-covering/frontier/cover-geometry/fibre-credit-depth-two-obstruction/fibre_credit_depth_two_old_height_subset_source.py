#!/usr/bin/env python3
"""Exact common-source factors for subsets of arbitrary old prime heights."""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations, product
from math import prod
import argparse,json
from hashlib import sha256

def need(b,m):
    if not b:raise RuntimeError(m)

DEPENDENCIES={'fibre_credit_depth_two_old23_full_height.json': 'ca998ef3ce5e1043cbd1a78a4f9cd4306b12cfb781b219729aa916f0ba016ede', 'fibre_credit_depth_two_two_fresh_heights.json': 'eadf7f37075a16e55573ba31a7189578b56387a3aacafa4280295bcf94f94ae0'}

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        need(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned head source or two-direction gate: '+name)
    head=json.loads((directory/'fibre_credit_depth_two_old23_full_height.json').read_text())['rows']
    gate=json.loads((directory/'fibre_credit_depth_two_two_fresh_heights.json').read_text())
    need(gate['pointwise_threshold']==7750 and gate['coefficient_W']==20,'inherited two-direction scalar gate')
    for row in head:
        law={entry['value']:F(entry['probability']) for entry in row['comparison_law']}
        need(all(v>=0 for v in law.values()) and sum(law.values())==1,'same positive comparison law')
        need(all(sum(v*max(y-t,0) for y,v in law.items())==F(row['hinge_bounds'][t]) for t in range(12)),
             'retained head law recovers every inherited stoploss bound')
    primes=(11,13,17,19,23)
    c=[F(185,86),F(178,85),F(178,85),F(2),F(157,77),F(157,77)]
    nmin=(77,78,78,75,74,74)
    need([F(row['hinge_bounds'][1]) for row in head]==c
         and tuple(row['old315_Nmin'] for row in head)==nmin,
         'paired source constants match the inherited head laws')
    subsets=[tuple(s) for r in range(6) for s in combinations(primes,r)]
    subresults=[]
    for J in subsets:
        values=[]
        theta=[F(1,p-2 if p in J else p-1) for p in primes]
        mult=prod((1+t for t in theta),start=F(1))
        for i in range(6):
            delta=1-c[i]*sum(theta)-(c[i]+1)*(mult-1-sum(theta))
            den=F(315,nmin[i])*prod((F(p,p-2 if p in J else p-1) for p in primes),start=F(1))
            need(delta>0,'all five old-axis subsets have positive retention')
            values.append({'shape':head[i]['shape'],'retention':str(delta),'density_cap':str(den),'Haar_factor':str(delta/den)})
        subresults.append({'full_height_axes':list(J),'shapes':values,'min_Haar_factor':str(min(F(v['Haar_factor']) for v in values))})
    need(F(subresults[-1]['min_Haar_factor'])==F(2719,3194470),'all five unrestricted axes density')

    # Distribution of the three shallow Bernoulli count, independently convolved.
    bern=[F(1)]
    for p in (11,13,17):
        new=[F(0)]*(len(bern)+1)
        for j,v in enumerate(bern):
            new[j]+=v*F(p-2,p-1);new[j+1]+=v*F(1,p-1)
        bern=new

    def tail(p,n):
        if n==0:return F(1)
        if n==1:return F(1,p-1)
        return F(1,(p-2)*p**(n-1))
    def pmass(p,n):return tail(p,n)-tail(p,n+1)
    def moment2(p):
        return 1+F(2,p-2)+F(p*p+1,(p-2)*(p-1)**2)

    pairsource=next(s for s in subresults if s['full_height_axes']==[19,23])
    rows=[]
    for i,h in enumerate(head):
        law={entry['value']:F(entry['probability']) for entry in h['comparison_law']}
        probs=[law.get(y,F(0)) for y in range(1,13)]
        # Only a finite bounded product can have Z<=8; enumerate it exactly.
        lowmass=F(0); belowmass=F(0);low2=F(0)
        for y,py in enumerate(probs,1):
            for j,pj in enumerate(bern):
                base=y*2**j
                if base>8:continue
                for n19 in range(8//base):
                    for n23 in range(8//(base*(1+n19))):
                        z=base*(1+n19)*(1+n23)
                        prob=py*pj*pmass(19,n19)*pmass(23,n23)
                        lowmass+=prob;low2+=prob*z*z
                        if z<8:belowmass+=prob
        delta=F(pairsource['shapes'][i]['retention'])
        gt8=1-lowmass;ge8=1-belowmass
        need(gt8<=delta<=ge8,'one shared quantile is8 for every convex penalty')
        ey2=sum((py*y*y for y,py in enumerate(probs,1)),F(0))
        shallow2=sum((pj*4**j for j,pj in enumerate(bern)),F(0))
        raw2=ey2*shallow2*moment2(19)*moment2(23)
        top2=64+(raw2-low2-64*gt8)/delta
        need(top2<260,'uniform complete-query square budget below260')
        rows.append({'shape':h['shape'],'P_Z_gt8':str(gt8),'P_Z_ge8':str(ge8),'raw_second_moment':str(raw2),
                     'upper_tail_second_moment':str(top2),'second_moment_decimal':float(top2)})
    hmin=F(pairsource['min_Haar_factor'])
    need(hmin==F(763798,62292165),'two-axis actual source Haar factor')
    density=hmin*F(7750-21*260,20*28*30)
    need(density==F(12493553,7475059800) and density>F(1,600),'two fresh continuation density')
    out={'scope':'Actual root-balanced sources for every subset of five full old heights, with a two-fresh continuation for old19/23. Ordinary arithmetic, not Lean.',
         'dependency_hashes':DEPENDENCIES,'subsets':subresults,'number_source_cases':192,
         'two_full_axis_rows':rows,'all_five_full_Haar_lower':str(F(2719,3194470)),
         'two_full_axis_Haar_factor':str(hmin),'two_fresh_density':str(density),
         'old_core_caps':{'3':2,'5':1,'7':1},'outside_old_axes':list(primes),
         'two_fresh_minima':[29,31],'two_fresh_heights':'arbitrary finite',
         'head_D2_replayed':False,'two_direction_enclosure_replayed':False}
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with old-height subset source')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)

if __name__=='__main__':main()
