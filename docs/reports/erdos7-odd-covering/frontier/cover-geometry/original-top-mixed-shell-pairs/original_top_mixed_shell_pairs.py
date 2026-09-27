#!/usr/bin/env python3
"""Literal-source mixed top-shell intersection and joint supplier controls."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from math import gcd,lcm,prod
from pathlib import Path
import argparse,json


def require(ok,message):
    if not ok:raise ValueError(message)


def factor(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=1
    return out


def bits(mask):
    while mask:
        low=mask&-mask;yield low.bit_length()-1;mask-=low


def check(name,classes,whole_expected):
    L=lcm(*(m for m,a in classes));fac=factor(L);N=L//prod(fac)
    info=[];owners=[[] for _ in range(L)];shells={}
    for s,(m,a) in enumerate(classes):
        f=factor(m);A=tuple(p for p in fac if f.get(p,0)==fac[p]);theta={p:(a%(p**fac[p]))//p**(fac[p]-1) for p in A}
        info.append(dict(A=A,theta=theta,bar=m//prod(A)))
        for x in range(a%m,L,m):owners[x].append(s)
        for p in A:shells[s,p]=sum(1<<x for x in range(a%(m//p),L,m//p) if x%m!=a%m)
    whole=all(owners);require(whole==whole_expected,'coverage scope')
    private=[sum(1<<x for x in range(L) if owners[x]==[s]) for s in range(len(classes))]
    canonical=[min(ss,key=lambda s:(classes[s][0],s)) if ss else None for ss in owners]
    units={p:(L//(p**fac[p]))*pow(L//(p**fac[p]),-1,p**fac[p])*p**(fac[p]-1) for p in fac}
    owner_shells={}
    for (s,p),mask in shells.items():
        th=info[s]['theta'][p]
        owner_shells[s,p]=sum(1<<x for x in bits(mask) if canonical[(x+(th-(x%(p**fac[p]))//p**(fac[p]-1))*units[p])%L]==s)
    original_pair_unions=defaultdict(int);checks=0;nonzero=0;rows=[]
    for p,q in combinations(fac,2):
        table=[];raw_sum=Q(0);owner_sum=Q(0)
        for s,ds in enumerate(info):
            if p not in ds['A']:continue
            for t,dt in enumerate(info):
                if q not in dt['A']:continue
                A=set(ds['A']);B=set(dt['A']);inter=shells[s,p]&shells[t,q]
                top_ok=all(ds['theta'][r]==dt['theta'][r] for r in (A&B)-{p,q})
                top_ok=top_ok and (p not in B or ds['theta'][p]!=dt['theta'][p]) and (q not in A or ds['theta'][q]!=dt['theta'][q])
                lower_ok=(classes[s][1]-classes[t][1])%gcd(ds['bar'],dt['bar'])==0
                lower=Q(1,lcm(ds['bar'],dt['bar'])) if lower_ok else Q(0)
                expected=lower*Q((p-1 if p not in B else 1)*(q-1 if q not in A else 1),prod(A|B)) if top_ok else Q(0)
                require(Q(inter.bit_count(),L)==expected,'OB3 mixed-shell exact original CRT coefficient')
                if s==t:require(inter==0,'one original label has disjoint top-shell directions')
                else:
                    key=tuple(sorted((s,t)))
                    require(not(original_pair_unions[key]&inter),'different ordered direction pairs have disjoint regions for one unordered original pair')
                    original_pair_unions[key]|=inter
                chosen=owner_shells[s,p]&owner_shells[t,q]
                require(not(chosen&~inter),'fixed owner mixed shell stays within original shell')
                table.append((s,t,inter,chosen));raw_sum+=expected;owner_sum+=Q(chosen.bit_count(),L);checks+=1;nonzero+=bool(inter)
        coef=(p-1)*(q-1)
        require(owner_sum<=coef,'one owner per phase caps the full joint pair budget')
        D=[t for t,d in enumerate(info) if p in d['A'] and q in d['A']];U=0
        for t in D:U|=private[t]
        feasible=0;missing=0;raw_restricted=0;owner_restricted=0
        for x in bits(U):
            ok=True
            for r in (p,q):
                yp=(x%(r**fac[r]))//r**(fac[r]-1)
                for a in range(r):
                    if a==yp:continue
                    if not owners[(x+(a-yp)*units[r])%L]:ok=False
            if not ok:
                missing+=1;require(not whole,'whole cover supplies all actual mixed-direction phases');continue
            feasible+=1;rc=sum(bool(inter>>x&1) for s,t,inter,chosen in table);oc=sum(bool(chosen>>x&1) for s,t,inter,chosen in table)
            require(rc>=coef and oc==coef,'common-source actual joint rectangles and fixed-owner partition')
            raw_restricted+=rc;owner_restricted+=oc
        require(Q(feasible*coef,L)<=Q(raw_restricted,L)<=raw_sum,'raw mixed demand integrated only over feasible private region')
        require(Q(feasible*coef,L)==Q(owner_restricted,L)<=owner_sum,'same one-partition owner mixed demand')
        rows.append(dict(primes=[p,q],selected_labels=D,private_count=U.bit_count(),feasible_private_count=feasible,missing_private_count=missing,
            demand_coefficient=coef,feasible_demand=str(Q(feasible*coef,L)),raw_full_capacity=str(raw_sum),owner_full_capacity=str(owner_sum),
            raw_feasible_private_service=str(Q(raw_restricted,L)),owner_feasible_private_service=str(Q(owner_restricted,L))))
    return dict(name=name,period=L,lower_modulus=N,whole_cover=whole,numerically_distinct=len({m for m,a in classes})==len(classes),
        all_moduli_odd=all(m%2 for m,a in classes),classes=classes,uncovered_count=sum(not ss for ss in owners),
        mixed_shell_formula_checks=checks,nonzero_mixed_shell_pairs=nonzero,prime_pair_controls=rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args()
    inputs=[('six_distinct_odd_noncover',[(135,0),(5,1),(15,12),(45,18),(35,14),(55,44)],False),
            ('distinct_even_L60_whole',[(2,1),(4,2),(3,1),(6,2),(5,1),(10,2),(20,8),(15,0),(30,24)],True),
            ('repeated_modulus_15_whole',[(15,a) for a in range(15)],True)]
    out=[check(*z) for z in inputs]
    args.output.write_text(json.dumps(dict(scope='One literal uniform source per control. OB3 exact mixed-prime capacities, disjoint same-original-pair direction regions, and one fixed-owner partition. Noncover missing phases remain separate. No Lean/unrestricted conclusion.',controls=out),indent=2)+'\n')
    for r in out:print(json.dumps({k:r[k] for k in ('name','period','whole_cover','mixed_shell_formula_checks','nonzero_mixed_shell_pairs')}))


if __name__=='__main__':main()
