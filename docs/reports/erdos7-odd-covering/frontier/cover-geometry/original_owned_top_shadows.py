#!/usr/bin/env python3
"""Exact OS1--OS3 controls on one fixed original owner partition per family.

The odd-distinct seven-label family is a NONCOVER and does not receive OS1.
The odd whole-cover control repeats modulus 15. No Lean/#7 claim is made.
"""
from collections import defaultdict
from fractions import Fraction as F
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

def choose2(n):return n*(n-1)//2

def analyze(name,classes,whole_expected):
    L=lcm(*(m for m,a in classes));fac=factor(L);R=prod(fac);N=L//R
    info=[]
    for s,(m,a) in enumerate(classes):
        fm=factor(m);A=tuple(p for p in fac if fm.get(p,0)==fac[p])
        theta=tuple((a%(p**fac[p]))//p**(fac[p]-1) for p in A)
        info.append({'support':A,'theta':theta,'phase':dict(zip(A,theta)),'bar':m//prod(A)})
    owner=[-1]*L;multiplicity=bytearray(L)
    order=sorted(range(len(classes)),key=lambda s:(classes[s][0],s))
    for s in order:
        m,a=classes[s]
        for x in range(a%m,L,m):
            multiplicity[x]+=1
            if owner[x]<0:owner[x]=s
    whole=all(multiplicity);require(whole==whole_expected,'whole-cover scope')
    owned=[set() for _ in classes];private=[[] for _ in classes];fibre_counts=[defaultdict(int) for _ in classes]
    for x,s in enumerate(owner):
        if s<0:continue
        owned[s].add(x);fibre_counts[s][x%N]+=1
        if multiplicity[x]==1:private[s].append(x)
    require(all(private),'each original label has an actual private point')
    Z=[set(c) for c in fibre_counts]
    D=[set(range(a%d['bar'],N,d['bar'])) for (m,a),d in zip(classes,info)]
    labels=[]
    for s,((m,a),d) in enumerate(zip(classes,info)):
        P=prod(d['support']);mass=F(len(owned[s]),L);shadow=F(len(Z[s]),N)
        require(Z[s]<=D[s],'owned lower shadow lies in actual lower class')
        require(all(1<=n<=R//P for n in fibre_counts[s].values()),'nonempty owner-fibre sizes')
        require(P*mass<=shadow<=R*mass,'OS2 owner-mass/shadow bounds')
        for x in owned[s]:
            require(all((x%(p**fac[p]))//p**(fac[p]-1)==d['phase'][p] for p in d['support']), 'owned cells retain original top phase')
        labels.append({'label':s,'modulus':m,'residue':a,'top_support':d['support'],'top_phase':d['theta'],
                       'lower_index':d['bar'],'raw_shadow_count':len(D[s]),'owned_shadow_count':len(Z[s]),
                       'raw_shadow_lower_residues':sorted(D[s]),'owned_shadow_lower_residues':sorted(Z[s]),
                       'owned_count':len(owned[s]),'owned_mass':str(mass),'private_count':len(private[s]),'private_witness':private[s][0],
                       'owned_shadow_mass':str(shadow),'owner_mass_lower_bound':str(P*mass),'owner_mass_upper_bound':str(R*mass)})
    by_support=defaultdict(list)
    for s,d in enumerate(info):by_support[d['support']].append(s)
    pair_rows=[];support_rows=[]
    for A,ss in sorted(by_support.items()):
        P=prod(A);raw=F(0);actual=F(0);pointwise=0;max_k=0
        for z in range(N):
            active=[s for s in ss if z in Z[s]];phases=[info[s]['theta'] for s in active]
            require(len(phases)==len(set(phases)),'OS2 at most one positive owner for each support-phase')
            require(len(active)<=P,'OS2 distinct phase count ceiling')
            pointwise+=choose2(len(active));max_k=max(max_k,len(active))
        for s,t in combinations(ss,2):
            if info[s]['theta']==info[t]['theta']:
                require(not(Z[s]&Z[t]),'same-support same-phase owned shadows are disjoint')
                continue
            rc=F(len(D[s]&D[t]),N);oc=F(len(Z[s]&Z[t]),N)
            lower_ok=(classes[s][1]-classes[t][1])%gcd(info[s]['bar'],info[t]['bar'])==0
            require(rc==(F(1,lcm(info[s]['bar'],info[t]['bar'])) if lower_ok else 0),'raw lower-shadow CRT capacity')
            require(oc<=rc,'OS1 owned pair coefficient refines raw coefficient')
            raw+=rc;actual+=oc
            pair_rows.append({'labels':[s,t],'support':A,'raw_shadow_intersection':str(rc),'owned_shadow_intersection':str(oc)})
        require(actual==F(pointwise,N)<=choose2(P),'OS2 exact pair count and phase ceiling')
        support_rows.append({'support':A,'top_cells':P,'maximum_owner_positive_labels':max_k,
                             'raw_distinct_phase_pair_sum':str(raw),'owned_distinct_phase_pair_sum':str(actual),
                             'integrated_owner_phase_pairs':str(F(pointwise,N)),'phase_pair_ceiling':choose2(P)})
    units={p:(L//p**fac[p])*pow(L//p**fac[p],-1,p**fac[p])*p**(fac[p]-1) for p in fac}
    Fs={};transport=[]
    for s,d in enumerate(info):
        for p in d['support']:
            target=d['phase'][p];points=set();m,a=classes[s]
            for y in owned[s]:
                for phase in range(p):
                    if phase==target:continue
                    x=(y+(phase-target)*units[p])%L
                    require(x%N==y%N,'owned top-shell transport keeps actual lower source')
                    require(x%(m//p)==a%(m//p) and x%m!=a%m,'transport preimage belongs to original top shell')
                    require(owner[(x+(target-phase)*units[p])%L]==s,'same canonical original owner after top change')
                    points.add(x)
            Fs[s,p]=points
            require(len(points)==(p-1)*len(owned[s]),'OS3 exact owner transport mass')
            transport.append({'label':s,'prime':p,'owner_mass':str(F(len(owned[s]),L)),'transport_mass':str(F(len(points),L))})
    prime_rows=[]
    for p in fac:
        ss=[s for s,d in enumerate(info) if p in d['support']];omega=sum((F(len(owned[s]),L) for s in ss),F(0))
        counts=bytearray(L)
        for s in ss:
            for x in Fs[s,p]:counts[x]+=1
        require(max(counts)<=p-1,'OS3 one original owner per alternative top phase')
        pair_mass=F(0);n_pairs=0
        for s,t in combinations(ss,2):
            ds,dt=info[s],info[t]
            if ds['phase'][p]==dt['phase'][p]:require(not(Fs[s,p]&Fs[t,p]),'same alternative phase has one actual owner')
            if ds['support']!=dt['support'] or ds['phase'][p]==dt['phase'][p]:continue
            if any(ds['phase'][q]!=dt['phase'][q] for q in ds['support'] if q!=p):continue
            pair_mass+=F(len(Fs[s,p]&Fs[t,p]),L);n_pairs+=1
        cap=choose2(p-1)*omega
        require(pair_mass<=cap,'OS3 common owner-mass pair ceiling')
        prime_rows.append({'prime':p,'same_support_compatible_phase_pairs':n_pairs,'owner_pair_capacity':str(pair_mass),
                           'Omega_p':str(omega),'owner_mass_ceiling':str(cap),'absolute_ceiling':choose2(p-1),
                           'maximum_chosen_suppliers_at_one_point':max(counts)})
    os1=None
    if whole:
        require(all(m%2 for m,a in classes),'OS1 is tested only with odd coordinates')
        selected_sets=[{s} for s in range(len(classes))]+[set(range(len(classes)))]
        os1=[]
        for selected in selected_sets:
            U=set().union(*(set(private[s]) for s in selected));lower={x%N for x in U};rhs=F(0)
            for z in lower:
                active=[s for s in range(len(classes)) if z in Z[s]]
                require(all(info[s]['support'] for s in active),'OS1 positive-owner fibre hyperplanes are proper')
                require(sum(fibre_counts[s].get(z,0) for s in active)==R,'OS1 owner-positive slices cover the entire actual top fibre')
                require(any(info[s]['support']==info[t]['support'] and info[s]['theta']!=info[t]['theta'] for s,t in combinations(active,2)), 'OS1 actual same-support distinct-phase collision')
            for row in pair_rows:
                if not row['support']:continue
                s,t=row['labels'];P=prod(row['support'])
                rhs+=(1-F(2-int(s in selected)-int(t in selected),P))*F(row['owned_shadow_intersection'])
            require(F(len(U),L)<=rhs,'OS1 conditional private-region comparison')
            os1.append({'selected_labels':sorted(selected),'private_mass':str(F(len(U),L)),'owned_shadow_rhs':str(rhs)})
    return {'name':name,'period':L,'lower_modulus':N,'top_size':R,'classes':labels,
            'whole_cover':whole,'all_odd':all(m%2 for m,a in classes),'numerically_distinct':len({m for m,a in classes})==len(classes),
            'uncovered_count':sum(c==0 for c in multiplicity),'owner_rule':'Least numerical modulus; original label breaks ties only in repeated-modulus control.',
            'same_support_pair_rows':pair_rows,'OS2_support_rows':support_rows,'owner_transport_rows':transport,'OS3_prime_rows':prime_rows,
            'OS1_status':'checked on singletons and full selected family under odd whole coverage' if whole else 'NOT APPLIED: family is a noncover',
            'OS1_conditional_controls':os1}

def run():
    controls=[analyze('odd_distinct_seven_label_noncover',[(444675,296450),(15,0),(33,0),(21,7),(25,1),(49,1),(121,1)],False),
              analyze('odd_repeated_modulus15_whole',[(15,a) for a in range(15)],True)]
    first=controls[0];three=next(row for row in first['OS2_support_rows'] if row['support']==(3,))
    require(first['period']==444675 and first['lower_modulus']==385 and first['uncovered_count']==355727,'reused literal source')
    require(three['raw_distinct_phase_pair_sum']=='16/385' and three['owned_distinct_phase_pair_sum']=='3/77','strict actual owner-positive shadow improvement')
    require(next(row for row in first['OS3_prime_rows'] if row['prime']==3)['owner_pair_capacity']=='74/5775','same owner partition as published original owner budget')
    repeated=controls[1]
    require(repeated['OS2_support_rows'][0]['owned_distinct_phase_pair_sum']=='105','complete phase partition saturates OS2')
    require([(row['prime'],row['owner_pair_capacity'],row['owner_mass_ceiling']) for row in repeated['OS3_prime_rows']]==[(3,'1','1'),(5,'6','6')],'complete odd repeated partition saturates OS3')
    return {'scope':'One original uniform law and one fixed least-modulus owner partition per control. OS2/OS3 and exact owner shadows on the odd-distinct NONCOVER; OS1 only on the odd repeated-modulus whole cover. Ordinary exact checks, not Lean or an unrestricted odd-covering result.','controls':controls}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args()
    out=run();args.output.write_text(json.dumps(out,indent=2)+'\n')
    for c in out['controls']:print(json.dumps({k:c[k] for k in ('name','period','whole_cover','numerically_distinct','uncovered_count','OS2_support_rows','OS3_prime_rows','OS1_status')}))
