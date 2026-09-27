#!/usr/bin/env python3
"""Exact consumer for one- and two-prime pure-conditioned extensions.

Reads the retained seven-core summary; does not reconstruct its source proof.
All checks remain active under -O. No geometry, external packages, source
producer, reviewer artifact, or Lean checker is used.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import factorial, prod, isqrt
from pathlib import Path

SEED_SHA='2ff88432077332183296e76c9119791e6fa6e05cbf8476454489069c249f2e63'

def need(ok,why):
    if not ok:
        raise ValueError(why)

def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

def one(A,q):
    den=Q(q-2)-A
    need(den>0,'positive single-prime denominator')
    return ((q-1)*A+1)/den

def two_mass(A,q,r):
    return 1-A/Q(q-2)-A/Q(r-2)-(A+1)/Q((q-2)*(r-2))

def pure_density(q,r=None):
    ans=Q(q-1,q-2)
    return ans if r is None else ans*Q(r-1,r-2)

def enc(x):
    if isinstance(x,Q):
        return str(x)
    if isinstance(x,dict):
        return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):
        return [enc(v) for v in x]
    return x

def poly_add(a,b,scale=Q(1)):
    out=dict(a)
    for k,v in b.items():
        out[k]=out.get(k,Q(0))+scale*v
    return {k:v for k,v in out.items() if v}

def poly_mul(a,b):
    out={}
    for k,v in a.items():
        for j,w in b.items():
            key=tuple(x+y for x,y in zip(k,j))
            out[key]=out.get(key,Q(0))+v*w
    return {k:v for k,v in out.items() if v}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seed',type=Path,required=True)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    raw=args.seed.read_bytes()
    need(sha256(raw).hexdigest()==SEED_SHA,'seven-core seed SHA256')
    seed=json.loads(raw)
    A=Q(seed['seven_core_query_R_upper']);density=Q(seed['normalized_density_cap'])
    need(A==Q(70874,3375) and density==455625,'seed constants')
    need('One law serves all layouts at a fixed finite period.' in seed['scope'],'finite-period one-law scope')
    coarse=Q(21)
    need(A<coarse,'strict coarse simplification')

    q=101;single=one(coarse,q);exact_single=one(A,q)
    need(single==Q(2101,78) and exact_single==Q(7090775,263251) and exact_single<single<27,
         'one-prime common query bound')
    single_mass=1-coarse/Q(q-2)
    single_haar=single_mass/(density*pure_density(q))
    single_density=density*Q(q-1)/(q-2-coarse)
    need(single_haar==Q(13,7593750) and single_density==Q(7593750,13),'single-prime density')
    need(single_haar*single_density==1,'single-prime mass-density identity')
    # The rational identity is also checked independently of a derivative.
    for aq,qq,step in ((A,101,2),(coarse,101,100),(Q(1,2),5,2)):
        den0=qq-2-aq;den1=qq+step-2-aq
        need(one(aq,qq)-one(aq,qq+step)==step*(aq*aq+aq+1)/(den0*den1),'single-prime monotonic identity')

    pairs=((29,101),(31,83),(37,59),(41,53),(43,47))
    controls=((29,97),(31,79),(37,53),(41,47))
    rows=[]
    for q,r in pairs:
        need(prime(q) and prime(r) and q<r,'distinct odd prime pair')
        N=(q-23)*(r-23)-463
        m=two_mass(coarse,q,r)
        exact_m=two_mass(A,q,r)
        need(m==Q(N,(q-2)*(r-2)) and N>0,'coarse two-prime positive numerator')
        need(exact_m>m,'exact seed improves mass')
        haar=m/(density*pure_density(q,r))
        need(haar==Q(N,density*(q-1)*(r-1)),'two-prime Haar conversion')
        rows.append({'primes':[q,r],'coarse_numerator':N,'coarse_mass_lower':m,
                     'exact_seed_mass_lower':exact_m,'coarse_haar_lower':haar})
    failrows=[]
    for q,r in controls:
        need(prime(q) and prime(r) and q<r,'valid predecessor control')
        N=(q-23)*(r-23)-463
        need(N<0 and two_mass(coarse,q,r)<0 and two_mass(A,q,r)<0,'preceding-prime scalar criterion fails')
        succeeding=next(rr for qq,rr in pairs if qq==q)
        need(not any(prime(z) for z in range(r+1,succeeding)),'immediate preceding prime')
        failrows.append({'primes':[q,r],'coarse_numerator':N,
                         'exact_seed_mass_lower':two_mass(A,q,r),
                         'scope':'Failure of this scalar sufficient criterion, not a cover or all-law obstruction.'})
    need(prime(43) and prime(47) and not any(prime(z) for z in range(44,47)),
         '47 is first admissible distinct prime above43; (43,43) is not a control')

    # Exact polynomial coefficient identity after q=23+x, r=23+y.
    # N(q+a,r+b)-N(q,r)=a*y+b*x+a*b.
    x={(1,0,0,0):Q(1)};y={(0,1,0,0):Q(1)}
    a={(0,0,1,0):Q(1)};b={(0,0,0,1):Q(1)}
    delta=poly_add(poly_mul(poly_add(x,a),poly_add(y,b)),poly_mul(x,y),Q(-1))
    need(delta=={(0,1,1,0):Q(1),(1,0,0,1):Q(1),(0,0,1,1):Q(1)},
         'coordinatewise monotonic polynomial coefficients')
    need(all(v>0 for v in delta.values()),'nonnegative increment coefficients')

    # The numerator alone does not prove Haar-ratio monotonicity. Check the
    # cross-multiplied difference of N(q,r)/((q-1)*(r-1)) separately.
    # With a=q'-q: N(q',r)*(q-1)-N(q,r)*(q'-1)=a*(22*r-43).
    def pconst(n):
        return {(0,0,0,0):Q(n)}
    pq=poly_add(x,pconst(23));pr=poly_add(y,pconst(23))
    pn=poly_add(poly_mul(x,y),pconst(-463))
    pn_next=poly_add(poly_mul(poly_add(x,a),y),pconst(-463))
    ratio_difference=poly_add(
        poly_mul(pn_next,poly_add(pq,pconst(-1))),
        poly_mul(pn,poly_add(poly_add(pq,a),pconst(-1))),Q(-1))
    ratio_expected=poly_mul(a,poly_add({k:22*v for k,v in pr.items()},pconst(-43)))
    need(ratio_difference==ratio_expected,'Haar-ratio monotonic coefficient identity')
    need(all(v>0 for v in ratio_expected.values()),'positive Haar-ratio increment for q,r>23')

    anchor=next(row for row in rows if row['primes']==[43,47])
    need(anchor['coarse_mass_lower']==Q(17,1845),'43/47 mass')
    haar=anchor['coarse_haar_lower'];need(haar==Q(17,880267500),'43/47 Haar mass')
    head=(3,5,7,11,13,17,19,43,47)
    M2=prod(Q(p*(p+1),(p-1)**2) for p in head)
    need(M2==Q(1026827659,43877376),'head Haar M2 product')
    B=3000000000;ell=19
    need(B>=286 and ell>=4 and 3**ell<=B,'Chapter33 analytic applicability')
    c=Q(2*ell*ell+1,2*ell*ell-1);need(c==Q(723,721),'prime-product constant')
    terms=[Q(factorial(7),factorial(7-h)*ell**h) for h in range(8)]
    series=sum(terms,Q(0))
    tau=c**7/Q(B)*Q(B,B-3)**2*series
    loss=M2*tau;surplus=haar-loss
    need(surplus>Q(1,200000000),'Chapter33 positive whole-tail margin')

    # One actual odd period, one product law, all original labels retained.
    # 35 has q,r exponents positive and old cofactor d=1; it is mixed in the
    # two-prime extension and must not be dropped with pure q or pure r powers.
    period=105
    originals=((3,0),(5,0),(7,0),(15,1),(21,2),(35,1),(105,8))
    need(len({m for m,r in originals})==len(originals),'distinct fixture moduli')
    pure=((3,0),(5,0),(7,0));mixed=originals[3:]
    carrier=[n for n in range(period) if all(n%m!=r for m,r in pure)]
    need(len(carrier)==48,'fixed pure-conditioned product carrier')
    weight=Q(1,len(carrier))
    bad={n for n in carrier if any(n%m==r for m,r in mixed)}
    kept=[n for n in carrier if n not in bad]
    need(len(bad)==12 and len(kept)==36,'actual joint mixed deletion')
    dropped=[n for n in carrier if all(n%m!=r for m,r in mixed if m!=35)]
    need(len(dropped)==37 and set(dropped)-set(kept)=={71},'omitted joint-unit-cofactor witness')
    need(71%35==1 and all(71%m!=r for m,r in originals if m!=35),
         'literal original private witness71')
    mixed_masses={m:sum((weight for n in carrier if n%m==r),Q(0)) for m,r in mixed}
    need(mixed_masses=={15:Q(1,8),21:Q(1,12),35:Q(1,24),105:Q(1,48)},
         'original mixed cylinder masses')
    # Actual head law is uniform on nonzero mod3, with nonunit query sum1/2.
    fixture_cost=two_mass(Q(1,2),5,7)
    need(Q(len(kept),len(carrier))>=fixture_cost==Q(19,30),'same-law scalar mass control')
    divisors=[d for d in range(1,period+1) if period%d==0]
    Rfixture=sum((max(Q(sum(n%d==a for n in kept),len(kept)) for a in range(d))
                  for d in divisors if d>1),Q(0))

    out={'scope':'Exact finite arithmetic consumer of the seven-core fixed-finite-period one-law premise. General pure-conditioning, shared original mixed-deletion and Chapter33 analytic-tail proofs remain mathematical premises; no new Lean certification.',
         'seed_sha256':SEED_SHA,'seed_query_R':A,'seed_density':density,'coarse_query_R':coarse,
         'single_prime':{'prime_lower_bound':101,'R_upper':single,'exact_seed_R_at101':exact_single,
                         'gap_below27':27-single,'density_upper':single_density,'haar_lower':single_haar},
         'two_prime_formula':'N_coarse=(q-23)*(r-23)-463',
         'two_prime_rows':rows,'preceding_prime_controls':failrows,
         'last_pair_boundary':'For q=43, r=47 is the first distinct larger prime; r=43 is inadmissible.',
         'monotonic_increment_coefficients':[{'powers':list(k),'coefficient':v} for k,v in sorted(delta.items())],
         'tail':{'reference_head_primes':head,'B':B,'ell':ell,'c':c,'M2':M2,
                 'tau7_series_terms':terms,'tau7_series':series,'tau7':tau,'haar_lower':haar,
                 'tail_loss_upper':loss,'remaining_live_mass_lower':surplus,
                 'simple_strict_remaining_live_mass_lower':Q(1,200000000),
                 'scope':'Remaining mass under the constructed unnormalized tail law; not full-period Haar density.'},
         'fixture':{'period':period,'originals':[{'modulus':m,'residue':r} for m,r in originals],
                    'predeletion_support_size':len(carrier),'survivor_size':len(kept),
                    'predeletion_atom_mass':weight,'mixed_class_masses':mixed_masses,
                    'live_mass':Q(len(kept),len(carrier)),'scalar_live_mass_lower':fixture_cost,
                    'survivor_nonunit_query_sum':Rfixture,'bad_omission_witness':71,
                    'wrong_survivor_size_if_mod35_dropped':len(dropped)}}
    text=json.dumps(enc(out),indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
        print('PASS: pinned seed, one- and two-prime boundaries, exact Chapter33 tail, and actual period105 joint-label countercontrol.')
    else:
        print(text,end='')

if __name__=='__main__':
    main()
