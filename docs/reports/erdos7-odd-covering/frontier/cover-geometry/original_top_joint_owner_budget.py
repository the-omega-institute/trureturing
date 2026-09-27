#!/usr/bin/env python3
"""Exact actual-source phase/support assignment controls. No Lean or #7 claim."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from math import gcd,lcm,prod
from pathlib import Path
import argparse,json


def require(ok,why):
    if not ok:raise ValueError(why)


def factors(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=1
    return out


def pi(r,m):
    require(m>0,'nonempty support bins for finite phase assignment')
    q,b=divmod(r,m)
    return b*q*(q+1)//2+(m-b)*q*(q-1)//2


def assignment(neighborhoods):
    """Return infeasibility explicitly; never assign zero cost to a missing phase."""
    missing=[a for a,neighbors in neighborhoods.items() if not neighbors]
    if missing:return dict(feasible=False,missing_phases=missing,phi=None)
    phases=tuple(neighborhoods);supports=tuple(sorted(set().union(*map(set,neighborhoods.values()))))
    index={s:i for i,s in enumerate(supports)}
    possible={(0,)*len(supports)}
    for a in phases:
        new=set()
        for counts in possible:
            for sup in neighborhoods[a]:
                cc=list(counts);cc[index[sup]]+=1;new.add(tuple(cc))
        possible=new
    minimum=min(sum(n*(n-1)//2 for n in cc) for cc in possible)
    hall=0;best=[]
    for r in range(1,len(phases)+1):
        for J in combinations(phases,r):
            neighbor_union=set().union(*(set(neighborhoods[a]) for a in J))
            bound=pi(len(J),len(neighbor_union))
            if bound>hall:hall=bound;best=[dict(phases=list(J),support_count=len(neighbor_union))]
            elif bound==hall:best.append(dict(phases=list(J),support_count=len(neighbor_union)))
    require(minimum>=hall>=pi(len(phases),len(supports)),'Hall lower bound and local-bin lower bound')
    return dict(feasible=True,missing_phases=[],phi=minimum,local_support_count=len(supports),
        local_bin_bound=pi(len(phases),len(supports)),hall_subset_bound=hall,hall_witness=best[0])


def analyze(name,classes,target,p,expected_whole):
    L=lcm(*(m for m,a in classes));fac=factors(L);N=L//prod(fac)
    info=[];owners=[[] for x in range(L)]
    for s,(m,a) in enumerate(classes):
        fm=factors(m);A=tuple(q for q in fac if fm.get(q,0)==fac[q]);P=prod(A)
        theta={q:(a%(q**fac[q]))//(q**(fac[q]-1)) for q in A}
        info.append(dict(label=s,modulus=m,residue=a,support=A,theta=theta,lower_index=m//P))
        for x in range(a%m,L,m):owners[x].append(s)
    require(p in info[target]['support'],'selected target reaches global top p')
    private=[x for x in range(L) if owners[x]==[target]]
    require(private,'actual private target')
    whole=all(owners);require(whole==expected_whole,'whole-cover scope')
    sig=len({d['support'] for d in info if p in d['support']})
    global_coef=pi(p-1,sig)
    shells={d['label']:{x for x in range(L) if x%(d['modulus']//p)==d['residue']%(d['modulus']//p) and x%d['modulus']!=d['residue']%d['modulus']} for d in info if p in d['support']}
    pairs=[];pair_rhs=Q(0)
    for s,t in combinations(shells,2):
        ds,dt=info[s],info[t];A=ds['support']
        if A!=dt['support'] or ds['theta'][p]==dt['theta'][p] or any(ds['theta'][q]!=dt['theta'][q] for q in A if q!=p):continue
        g=gcd(ds['lower_index'],dt['lower_index'])
        cap=Q(1,lcm(ds['lower_index'],dt['lower_index'])) if (ds['residue']-dt['residue'])%g==0 else Q(0)
        intersection=shells[s]&shells[t]
        rhs=Q(p-2,prod(A))*cap
        require(Q(len(intersection),L)==rhs,'original top shell-pair coefficient')
        pairs.append((s,t,intersection));pair_rhs+=rhs
    qpower=p**fac[p];unit=(L//qpower)*pow(L//qpower,-1,qpower)*p**(fac[p]-1)
    canonical_owner=[min(ss,key=lambda s:(classes[s][0],s)) if ss else None for ss in owners]
    owner_shells={}
    for s,sh in shells.items():
        th=info[s]['theta'][p]
        owner_shells[s]={x for x in sh if canonical_owner[(x+(th-(x%qpower)//(qpower//p))*unit)%L]==s}
    owner_pair_capacity=sum((Q(len(owner_shells[s]&owner_shells[t]),L) for s,t,inter in pairs),Q(0))
    require(owner_pair_capacity<=Q((p-1)*(p-2),2),'one canonical original owner per changedphase bounds total pair budget')
    rows=[];missing_count=0;feasible_count=0;hall_sum=local_sum=phi_sum=0;restricted_pair_sum=0;restricted_owner_pairs=0
    zero=None
    for x in private:
        phase=(x%qpower)//(qpower//p);neighbors={};literal=[]
        for a in range(p):
            if a==phase:continue
            y=(x+(a-phase)*unit)%L;ss=owners[y]
            require(y%N==x%N,'same original lower source')
            for s in ss:
                require(s in shells and x in shells[s],'actual neighbor owner supplies top shell')
                require(info[s]['theta'][p]==a,'distinct phases imply distinct original suppliers')
            neighbors[a]=tuple(sorted({info[s]['support'] for s in ss}))
            literal.append(dict(phase=a,residue=y,actual_supplier_labels=ss,actual_supplier_moduli=[classes[s][0] for s in ss],supports=neighbors[a],canonical_original_owner=canonical_owner[y]))
        result=assignment(neighbors)
        if name=='six_distinct_odd_local_Hall_noncover':
            weights={(5,):2}
            if result['feasible']:
                phase_sum=sum(min(weights.get(A,0) for A in neighbors[a]) for a in neighbors)
                penalty=sum(k*(k+1)//2 for k in weights.values())
                result['integer_weight_certificate']=dict(weights=[dict(support=A,weight=k) for A,k in weights.items()],phase_minimum_sum=phase_sum,penalty=penalty,lower_bound=phase_sum-penalty)
                require(result['phi']>=phase_sum-penalty,'PA2 actual integer-weight certificate')
            else:
                result['integer_weight_certificate']=None
        if not result['feasible']:
            missing_count+=1
            require(not whole,'whole cover cannot have missing phase at private source')
        else:
            feasible_count+=1;phi_sum+=result['phi'];local_sum+=result['local_bin_bound'];hall_sum+=result['hall_subset_bound']
            actual_pairs=sum(x in intersection for s,t,intersection in pairs)
            require(result['phi']<=actual_pairs,'source-local minimum assignment injects into actual same-support pairs')
            restricted_pair_sum+=actual_pairs
            owner_pairs=sum(x in owner_shells[s] and x in owner_shells[t] for s,t,inter in pairs)
            require(result['phi']<=owner_pairs<=actual_pairs,'canonical original owner assignment retains demand without pair reuse')
            result['canonical_owner_pair_count']=owner_pairs
            restricted_owner_pairs+=owner_pairs
        row=dict(source=x,assignment=result,neighbors=literal)
        rows.append(row)
        if x==0:zero=row
    require(Q(phi_sum,L)<=Q(restricted_pair_sum,L)<=pair_rhs,'integrated bound on explicitly feasible private subset')
    if whole:require(feasible_count==len(private),'whole-source integral has no omitted infeasible points')
    out=dict(name=name,classes=[dict(label=s,modulus=m,residue=a,private_witness=next((x for x in range(L) if owners[x]==[s]),None)) for s,(m,a) in enumerate(classes)],
        period=L,lower_modulus=N,whole_cover=whole,numerically_distinct=len({m for m,a in classes})==len(classes),
        all_moduli_odd=all(m%2 for m,a in classes),uncovered_count=sum(not row for row in owners),
        selected_target_label=target,selected_target_modulus=classes[target][0],prime=p,private_count=len(private),
        global_support_count=sig,global_coefficient=global_coef,
        feasible_private_count=feasible_count,infeasible_private_count=missing_count,
        feasible_subset_integral_phi=str(Q(phi_sum,L)),feasible_subset_integral_local_bin=str(Q(local_sum,L)),
        feasible_subset_integral_hall_subset=str(Q(hall_sum,L)),
        restricted_feasible_subset_actual_pair_sum=str(Q(restricted_pair_sum,L)),full_original_pair_capacity_rhs=str(pair_rhs),
        canonical_owner_rule='Least original numerical modulus, with original label as tie-break only for repeated-modulus controls.',
        canonical_owner_full_pair_capacity=str(owner_pair_capacity),
        feasible_subset_canonical_owner_pair_sum=str(Q(restricted_owner_pairs,L)),
        full_private_phi_integral=str(Q(phi_sum,L)) if whole or missing_count==0 else None,
        source_zero=zero,private_rows=rows)
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args()
    inputs=[('six_distinct_odd_local_Hall_noncover',[(135,0),(5,1),(15,12),(45,18),(35,14),(55,44)],0,5,False),
            ('distinct_odd_feasible_zero_Hall_star',[(15015,0),(15,6),(35,7),(55,33),(65,39)],0,5,False),
            ('distinct_even_L60_whole',[(2,1),(4,2),(3,1),(6,2),(5,1),(10,2),(20,8),(15,0),(30,24)],4,5,True),
            ('distinct_odd_lower_index_pair_reuse',[(444675,296450),(15,0),(33,0),(21,7),(25,1),(49,1),(121,1)],0,3,False),
            ('repeated_modulus_25_partition',[(25,a) for a in range(25)],0,5,True)]
    out=[analyze(*inp) for inp in inputs];x=out[0];z=x['source_zero']['assignment']
    require(x['period']==10395 and x['global_coefficient']==0 and z['local_bin_bound']==1 and z['phi']==z['hall_subset_bound']==3,'actual strict 0/1/3 hierarchy')
    require(z['integer_weight_certificate']['phase_minimum_sum']==6 and z['integer_weight_certificate']['penalty']==3 and z['integer_weight_certificate']['lower_bound']==3,'actual PA2 weights produce strict three-pair certificate')
    star=out[1];require(star['private_count']==star['feasible_private_count']==1 and star['infeasible_private_count']==0 and star['source_zero']['assignment']['phi']==0 and star['source_zero']['assignment']['local_support_count']==4,'actual p-local coverage does not force positive Hall cost')
    require(x['private_count']==77 and x['feasible_private_count']==17 and x['infeasible_private_count']==60,'missing phase scope is explicit')
    require(x['feasible_subset_integral_phi']=='17/3465' and x['feasible_subset_integral_local_bin']=='1/315','fixed uniform feasible-subset integral')
    require(all(d['private_witness'] is not None for d in x['classes']),'six-class actual irredundancy')
    reuse=out[3]
    require(reuse['period']==444675 and reuse['private_count']==reuse['feasible_private_count']==1 and all(d['private_witness'] is not None for d in reuse['classes']),'actual odd irredundant pair-reuse control')
    require(reuse['full_private_phi_integral']=='1/444675' and reuse['restricted_feasible_subset_actual_pair_sum']=='2/444675' and reuse['feasible_subset_canonical_owner_pair_sum']=='1/444675','two raw actual pairs versus one chosen original-owner pair')
    require(reuse['full_original_pair_capacity_rhs']=='16/1155','same-source lower-index cross-phase capacity')
    args.output.write_text(json.dumps(dict(scope='Original uniform mu throughout. Infeasible phase assignment is null with explicit missing-phase witnesses, never zero. Full private integral only claimed when all phases have actual suppliers. Ordinary exact controls, not Lean or unrestricted #7.',controls=out),indent=2)+'\n')
    for c in out:print(json.dumps({k:c[k] for k in('name','period','whole_cover','private_count','feasible_private_count','infeasible_private_count','global_coefficient','feasible_subset_integral_phi','full_original_pair_capacity_rhs')}))


if __name__=='__main__':main()
