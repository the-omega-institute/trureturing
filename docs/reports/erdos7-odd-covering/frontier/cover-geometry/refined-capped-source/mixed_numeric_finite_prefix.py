#!/usr/bin/env python3
"""Replay the fixed K=3, N=100000 finite-prefix completed-cap certificate.

Standard library only. Imports the adjacent full-slot consumer and existing
hinge/tail implementations through explicit paths. The conclusion concerns
one fixed-weight completed-budget lower-bound method, not actual mass bounds.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import prod,lcm
from pathlib import Path
import argparse,hashlib,importlib.util,json

P=(5,7,11,13,17,19,23)
SUPPORTS=tuple(s for s in range(128) if s.bit_count()>=2)
WEIGHTS=(F(1,3),F(1,3),F(1,9),F(1,9),F(1,9))
CHECKS=0

def require(ok,msg):
    global CHECKS
    CHECKS+=1
    if not ok:
        raise ValueError(msg)

def load_module(name,path):
    require(path.is_file(),'missing required library: '+str(path))
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def tight_caps_and_response(candidate,K):
    caps=[]
    budgets=[]
    for q in P:
        z=1-sum((F(1,q**j) for j in range(1,K+1)),F(0))
        require(z==F(q-2,q-1)+F(1,(q-1)*q**K),'exact pure survivor formula')
        cap=1/z
        b=cap/(q-1)
        require(cap==F((q-1)*q**K,(q-2)*q**K+1),'exact tight cylinder cap')
        require(0<b<=F(1,q-2),'old positive sensitivity majorant remains applicable')
        for j in range(1,K+1):
            require(q**(j-1)%q**j!=0,'zero misses pure exclusion')
            require(2%q**j!=q**(j-1),'phase two misses pure exclusion')
            require(F(cap,q**j)/b==F(q-1,q**j),'normalized slots unchanged')
            for k in range(j+1,K+1):
                require(q**(k-1)%q**j!=q**(j-1),'pure exclusions pairwise disjoint')
        caps.append(cap)
        budgets.append(b)
    bD={s:prod(budgets[i] for i in range(7) if s>>i&1) for s in SUPPORTS}
    colors={}
    for s,entry in zip(SUPPORTS,candidate['support_colors']):
        parts=[(entry,F(1))] if type(entry) is int else [(j,F(a)) for j,a in entry]
        colors[s]=[sum(a*(1+int((leaf>=2)==bool(j//5))+int(leaf==j%5)) for j,a in parts) for leaf in range(5)]
    root_factors=[[1-budgets[i]*sum(F(a)*(int((leaf>=2)==bool(r))+int(leaf==t)) for a,(r,t) in parts) for leaf in range(5)] for i,parts in enumerate(candidate['stars'])]
    response=[]
    for leaf in range(5):
        @lru_cache(None)
        def matching(mask):
            if mask==0:
                return F(1)
            bit=mask&-mask
            i=bit.bit_length()-1
            return root_factors[i][leaf]*matching(mask^bit)-sum(bD[s]*colors[s][leaf]*matching(mask^s) for s in SUPPORTS if s&bit and s&mask==s)
        response.append(matching(127))
    mass=sum(w*max(x,F(0)) for w,x in zip(WEIGHTS,response))
    return caps,budgets,response,mass

def finite_tight_hinge(caps,budgets):
    r=max(sum(WEIGHTS[:2]),sum(WEIGHTS[2:]))
    v=max(WEIGHTS)
    atoms={1:F(1)}
    for axis,q in enumerate((3,)+P):
        pmf={}
        for k in range(1,28):
            if q==3:
                probability=1-r if k==1 else r-v if k==2 else 2*v/3**(k-2)
            else:
                probability=1-caps[axis-1]/q if k==1 else caps[axis-1]*F(q-1,q**k)
            require(probability>=0,'nonnegative comparator atom')
            pmf[k]=probability
        following={}
        for x,px in atoms.items():
            for y,py in pmf.items():
                if x*y<28:
                    following[x*y]=following.get(x*y,F(0))+px*py
        atoms=following
    mean=(1+r+F(3,2)*v)*prod(1+b for b in budgets)
    ratios={h:(mean-h+sum((h-x)*px for x,px in atoms.items() if x<h))/(28-h) for h in range(28)}
    threshold=min(ratios,key=ratios.get)
    require(threshold==16,'minimizing tight hinge breakpoint')
    return ratios,threshold,mean

def finite_family(slot,completion,K,N):
    mixed={c['support_mask']:c for c in slot['mixed_completions']}
    specs=dict(zip(SUPPORTS,slot['candidate']['support_colors']))
    assigned={}
    counts={}
    for support in range(1,128):
        ps=tuple(P[i] for i in range(7) if support>>i&1)
        ns=completion.finite_denominators(ps,N)
        counts[support]=len(ns)
        if len(ps)==1:
            star=slot['star_completions'][P.index(ps[0])]
            for e,n in enumerate(ns,1):
                require(n==ps[0]**e,'star exponent order')
                prefix=star['prefix_roles']
                assigned[n]=prefix[e-1] if e<=len(prefix) else star['constant_tail_role']
        elif type(specs[support]) is int:
            for n in ns:
                assigned[n]=specs[support]
        else:
            c=mixed[support]
            chosen=set(c['selected_head_denominators'])
            residual=F(c['residual'])
            for n in ns:
                if n<=c['threshold']:
                    take=n in chosen
                else:
                    a=F(prod(q-1 for q in ps),n)
                    take=residual>=a
                    if take:
                        residual-=a
                assigned[n]=c['first_role'] if take else c['second_role']
            require(residual>=0,'finite greedy residual')
    require(len(assigned)==sum(counts.values())==445,'nonunit numerical prefix count')
    require(sum(v for s,v in counts.items() if s.bit_count()>=2)==415,'no-three mixed prefix count')
    rows=[dict(kind='base',modulus=3,residue=0),dict(kind='base',modulus=9,residue=1)]
    for q in P:
        for j in range(1,K+1):
            rows.append(dict(kind='pure',modulus=q**j,residue=q**(j-1)))
    leaves=(4,7,2,5,8)
    for n,role in sorted(assigned.items()):
        for ternary,target,kind in ((3,role//5+1,'root'),(9,leaves[role%5],'leaf')):
            residue=2+n*(((target-2)*pow(n,-1,ternary))%ternary)
            require(residue%n==2 and residue%ternary==target,'single global CRT phase')
            rows.append(dict(kind=kind,modulus=ternary*n,residue=residue))
        if sum(n%q==0 for q in P)>=2:
            rows.append(dict(kind='mixed_no_three',modulus=n,residue=2))
    rows.sort(key=lambda row:row['modulus'])
    require(len(rows)==1328,'full actual family count')
    require(len({row['modulus'] for row in rows})==len(rows),'distinct numerical moduli')
    L=1
    for row in rows:
        n=row['modulus']
        require(n>1 and n%2==1 and 0<=row['residue']<n,'odd nontrivial modulus and canonical residue')
        while n%3==0:
            n//=3
        L=lcm(L,n)
    survivor=L*((4*pow(L,-1,9))%9)
    require(survivor%9==4 and survivor%L==0,'common explicit survivor CRT')
    for row in rows:
        require(survivor%row['modulus']!=row['residue'],'explicit survivor avoids every original')
    return rows,dict(nonternary_slots=445,mixed_no_three_slots=415,pure_originals=7*K,root_and_leaf_originals=890,total_originals=len(rows),nonternary_lcm=L,explicit_survivor=survivor)

def encode(x):
    if isinstance(x,F):
        return str(x)
    raise TypeError(type(x).__name__)

def calculate(args):
    config=json.loads(args.certificate.read_text())
    require(config['schema']=='e7-mixed-numeric-finite-prefix-v1','fixed companion schema')
    require(config['pure_height']==3 and config['nonternary_cutoff']==100000,'fixed K3/N100000 contract')
    require(tuple(map(F,config['weights']))==WEIGHTS,'fixed five-leaf weights')
    raw=args.slot_certificate.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==config['slot_certificate_sha256'],'fixed full-slot certificate digest')
    slot=json.loads(raw)
    completion=load_module('e7_full_numerical_completion',args.completion_library)
    baseline=completion.run(slot,128,args.hinge_library)
    tail=load_module('e7_existing_numerical_tail',args.tail_library)
    require(tuple(tail.PRIMES)==P,'tail prime window')
    tail_result=tail.calculate()
    tail_rows=[r for r in tail_result['rows'] if r['nonternary_cutoff']==100000]
    require(len(tail_rows)==1,'one complete N100000 tail result')
    tail_row=tail_rows[0]
    delta=F(tail_row['complete_error_bound'])
    K,N=config['pure_height'],config['nonternary_cutoff']
    caps,budgets,response,mass=tight_caps_and_response(slot['candidate'],K)
    ratios,h,mean=finite_tight_hinge(caps,budgets)
    gap=ratios[h]-mass
    margin=gap-delta
    require(margin>F(37,10000),'all compatible full-cap completions fail by more than 37/10000')
    rows,family=finite_family(slot,completion,K,N)
    require(tail_row['nonternary_numerical_slots']==family['nonternary_slots'],'family and complete tail enumerate same prefix size')
    observed=dict(caps=list(map(str,caps)),budgets=list(map(str,budgets)),leaf_responses=list(map(str,response)),clipped_mass=str(mass),minimizing_h=h,required_mass=str(ratios[h]),complete_tail_error=str(delta),margin=str(margin),family_count=len(rows))
    require(observed==config['expected'],'fixed exact results match companion certificate')
    if args.write_family:
        args.write_family.write_text(json.dumps(dict(schema='e7-finite-prefix-original-family-v1',pure_height=K,nonternary_cutoff=N,scope='One finite family realizing the specified prefix. It has the displayed explicit survivor and is not a cover.',summary=family,originals=rows),indent=2)+'\n')
    return dict(schema='e7-mixed-numeric-finite-prefix-result-v1',status='PASS',scope='Fixed weights, K3 actual tight pure-cylinder caps, and all prefix-compatible full-cap completions of the N100000 actual family. The error controls the specified completed-budget polynomial only. No actual survivor mass upper bound, raw-budget obstruction, different-weight obstruction, covering construction, or Lean result is claimed.',slot_certificate_sha256=config['slot_certificate_sha256'],pure_height=K,nonternary_cutoff=N,weights=list(map(str,WEIGHTS)),baseline_completion_checks=baseline['checks'],companion_checks=CHECKS,exact=observed,clipped_decimal=float(mass),required_decimal=float(ratios[h]),gap=str(gap),gap_decimal=float(gap),complete_tail_error_decimal=float(delta),margin_decimal=float(margin),strict_margin_lower_bound='37/10000',complete_mean=str(mean),all_hinge_ratios=[dict(h=t,ratio=str(ratios[t])) for t in range(28)],family=family)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).parent
    ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name(Path(__file__).stem+'_certificate.json'))
    ap.add_argument('--slot-certificate',type=Path,default=here/'mixed_numeric_slot_completion_certificate.json')
    ap.add_argument('--completion-library',type=Path,default=here/'mixed_numeric_slot_completion.py')
    ap.add_argument('--hinge-library',type=Path,default=here/'clipped_common_source_obstruction.py')
    ap.add_argument('--tail-library',type=Path,default=here/'numerical_slot_tail_control.py')
    ap.add_argument('--write-result',type=Path)
    ap.add_argument('--write-family',type=Path)
    args=ap.parse_args()
    result=calculate(args)
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained companion result matches fresh exact replay')
    print(json.dumps({k:result[k] for k in ('status','baseline_completion_checks','companion_checks','clipped_decimal','required_decimal','complete_tail_error_decimal','margin_decimal')},indent=2))

if __name__=='__main__':
    main()
