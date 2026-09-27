#!/usr/bin/env python3
"""Exact checks for same-law query deletion and conditional-fibre boundaries.

The general all-height statements are proved in the accompanying report.
Finite congruence checks are diagnostics, not a substitute for those proofs.
No Lean or numerical LP solver is used.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd, prod
from pathlib import Path
import json

P = (3,5,7,11,13,17,19)
Q = P[1:]
checks = {}

def need(name,predicate):
    if name in checks or not predicate:
        raise ValueError(name)
    checks[name] = True

def crt_pair(a,m,b,n):
    return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)

def finite_query_profile(mu,primes,heights):
    profile = []
    for exponents in product(*(range(h+1) for h in heights)):
        modulus = prod(p**e for p,e in zip(primes,exponents))
        masses = {}
        for point,mass in mu.items():
            residue = point%modulus
            masses[residue] = masses.get(residue,F())+mass
        maximum = max(masses.values(),default=F())
        tail = prod((F(p,p-1) for p,e,h in zip(primes,exponents,heights) if e==h),start=F(1))
        profile.append(dict(modulus=modulus,maximum=maximum,tail_weight=tail))
    total = sum((r['maximum']*r['tail_weight'] for r in profile if r['modulus']>1),F())
    return profile,total


def main():
    d=prod(Q)
    need('full_Q_cofactor',d==1616615)
    families=[]
    query_checks=0
    for H in range(2,8):
        originals=[]
        for e in range(2,H+1):
            ternary=(3**(e-1)-3)//2
            residue=crt_pair(ternary,3**e,0,d)
            originals.append(dict(modulus=3**e*d,residue=residue,ternary_residue=ternary))
        need('distinct_odd_labels_'+str(H),len({r['modulus'] for r in originals})==len(originals)
             and all(r['modulus']>1 and r['modulus']%2==1 for r in originals))
        need('pairwise_disjoint_'+str(H),all(
            (a['residue']-b['residue'])%gcd(a['modulus'],b['modulus'])!=0
            for i,a in enumerate(originals) for b in originals[i+1:]))
        need('private_CRT_witnesses_'+str(H),all(
            sum((a['residue']-b['residue'])%b['modulus']==0 for b in originals)==1
            for a in originals))
        delta=sum((F(1,r['modulus']) for r in originals),F())
        need('geometric_mass_'+str(H),delta==F(1,d)*F(1-F(1,3**(H-1)),6)>0)
        for exponents in product(range(3),repeat=len(P)):
            modulus=prod(p**e for p,e in zip(P,exponents))
            if modulus==1:
                continue
            for row in originals:
                if (1-row['residue'])%gcd(modulus,row['modulus'])==0:
                    raise ValueError('phase_one_cylinder_intersects_original')
                query_checks+=1
        families.append(dict(height=H,originals=originals,deleted_mass=delta,
                             survivor_mass=1-delta))
    haar_R=prod((F(p,p-1) for p in P),start=F(1))-1
    need('bounded_phase_one_diagnostics',query_checks==45906)

    before={crt_pair(1,3,0,5):F(1,2),crt_pair(0,3,1,5):F(1,2)}
    after={crt_pair(0,3,0,5):F(1,4),crt_pair(1,3,0,5):F(1,4),
           crt_pair(0,3,1,5):F(1,2)}
    before_profile,before_R=finite_query_profile(before,(3,5),(1,1))
    after_profile,after_R=finite_query_profile(after,(3,5),(1,1))
    for name,mu in [('before',before),('after',after)]:
        need(name+'_actual_survivor',all(x%3!=2 and x%15!=1 for x in mu))
        need(name+'_probability',sum(mu.values(),F())==1)
        need(name+'_same_Q_marginal',all(sum((w for x,w in mu.items() if x%5==r),F())==F(1,2)
                                       for r in (0,1)))
    need('exact_query_increase',before_R==F(37,16) and after_R==F(43,16)
         and after_R-before_R==F(3,8))
    source_Q={0:F(1,3),1:F(2,3)}
    raw={crt_pair(t,3,x,5):F(1,2)*w for x,w in source_Q.items() for t in (0,1)
         if crt_pair(t,3,x,5)%15!=1}
    s=sum(raw.values(),F())
    need('product_delete_realization',s==F(2,3) and {x:w/s for x,w in raw.items()}==after)

    n={p:p-2 for p in Q}
    c={p:F(n[p]-1,n[p]) for p in Q}
    r={p:F(p,(p-1)*n[p]) for p in Q}
    E=prod((1+r[p] for p in Q),start=F(1))
    Fprod=prod((c[p]+r[p] for p in Q),start=F(1))
    C=prod(c.values(),start=F(1))
    w=F(3,41); R3=F(81,82)
    pure3=((3,2),(9,4),(27,19),(81,37))
    T=[t for t in range(81) if all(t%m!=a for m,a in pure3)]
    A=[t for t in T if t%27==1]
    need('actual_ternary_source',len(T)==41 and len(A)==3)
    total=F()
    for support in product((False,True),repeat=len(Q)):
        J={p for p,b in zip(Q,support) if b}
        missing=prod((c[p] for p in Q if p not in J),start=F(1))
        qweight=prod((r[p] for p in J),start=F(1))
        for e in range(5):
            mod3=3**e
            maximum=max(F(sum(t%mod3==a for t in T),41)
                        -(1-missing)*F(sum(t%mod3==a for t in A),41)
                        for a in range(mod3))
            total+=qweight*maximum*(F(3,2) if e==4 else 1)
    shared_s=1-w+w*C
    shared_R=total-shared_s
    delta=w*(1-C)
    debit=w*(E-Fprod-1+C)
    need('shared_allheight_formula',shared_R==(1+R3-w)*E+w*Fprod-shared_s)
    need('shared_exact_mass',delta==F(47063,1035045))
    need('shared_debit',shared_R==(1+R3)*E-1-debit and debit>0)
    need('shared_rate_bound',debit/delta<=E-1-prod(r.values(),start=F(1))<E-1)
    gate=566*shared_s-49*shared_R
    need('shared_joint_gate',gate>0)
    output=dict(
        scope='Two method obstructions and the existing22-original same-law profile; no unrestricted noncoverage claim and no Lean.',
        positive_mass_zero_query_debit=dict(primes=P,Q_cofactor=d,haar_query_norm=haar_R,
            families=families,bounded_congruence_checks=query_checks,
            general_claim='For every finite H>=2 and every nonunit P-smooth query modulus, phase1 has unchanged Haar mass; see the ordinary proof.'),
        fibre_uniformization=dict(originals=[dict(modulus=3,residue=2),dict(modulus=15,residue=1)],
            before=before,after=after,before_profile=before_profile,after_profile=after_profile,
            before_R=before_R,after_R=after_R,increase=after_R-before_R,
            realizing_Q_weights=source_Q,raw_survivor_mass=s),
        shared_ternary=dict(E=E,F=Fprod,C=C,ternary_mass=w,ternary_query_norm=R3,
            survivor_mass=shared_s,raw_query_norm=shared_R,normalized_query_norm=shared_R/shared_s,
            deleted_mass=delta,query_debit=debit,debit_per_deleted_mass=debit/delta,joint_gate=gate),
        checks=checks,check_count=len(checks))
    Path(__file__).with_suffix('.json').write_text(json.dumps(output,default=str,indent=2)+'\n')
    print('PASS',len(checks),'checks;',query_checks,'bounded congruence comparisons')
    print('fibre_query_norms',before_R,after_R)
    print('shared_joint_gate',gate,float(gate))


if __name__=='__main__':
    main()
