"""Direct positive-charge decomposition with unrestricted nonternary heights.

The 187 exponent vectors are fixed; no old checker is imported or rerun.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input',required=True)
    ap.add_argument('--output',required=True)
    args=ap.parse_args()
    raw=Path(args.input).read_bytes()
    data=json.loads(raw)
    primes=data['primes']
    palette=sorted(d for d,t in data['selected_witness'] if t==1)
    checks=0
    def need(ok,message):
        nonlocal checks
        checks+=1
        if not ok:
            raise ValueError(message)
    need(primes==[5,7,11,13,17,19,23,29,31,37,41],'Reference prime indices')
    need(len(palette)==187 and len(set(palette))==187,'The actual root1 exponent palette')
    c={p:F(p-1,p-2) for p in primes}
    b={p:F(1,p-2) for p in primes}
    a=c[5]/5
    beta=b[5]
    rho=F(1,2)
    need(a==F(4,15) and beta==F(1,3) and 5*(1-beta)/c[5]==2+rho,'Unrestricted 5-axis constants')
    exponent_vectors={}
    groups={q:[] for q in primes if q!=5}
    for d in palette:
        need(d>1,'Positive nonunit mixed cofactor')
        n=d
        exp={}
        for p in primes:
            e=0
            while n%p==0:
                n//=p
                e+=1
            if e:
                exp[p]=e
        need(n==1 and len(exp)>=2,'Original exponent vector is a mixed cofactor')
        exponent_vectors[d]=exp
        if exp.get(5)==1 and len(exp)==2:
            q=next(p for p in exp if p!=5)
            groups[q].append((d,exp[q]))
    group_labels={d for values in groups.values() for d,e in values}
    remainder=[d for d in palette if d not in group_labels]
    need(len(group_labels)==28 and len(remainder)==159,'Exact same grouped/remaining mixed palette')
    T={q:b[q]+c[q]*sum((F(1,q**e) for d,e in values),F(0)) for q,values in groups.items()}
    P=F(1)
    for q,t in T.items():
        need(0<t<1,'Every all-height q-group allowance remains below one')
        P*=1-t
    r=F(53,100)
    need(P>r*r>rho*rho,'The same rational square-root threshold remains valid')

    outside_prod=F(1)
    outside_sum=F(0)
    for q in groups:
        outside_prod*=1+b[q]
        outside_sum+=b[q]
    Ege2=outside_prod-1-outside_sum
    remaining_free=Ege2+(beta-a)*outside_sum
    need(beta-a==F(1,15) and Ege2>=0,'Remaining free charge has nonnegative coefficients')
    remaining_mixed=F(0)
    mixed_terms=[]
    for d in remainder:
        exp=exponent_vectors[d]
        mass=c[5]/5**exp[5] if 5 in exp else 1-beta
        for q,e in exp.items():
            if q!=5:
                mass*=c[q]/q**e
        remaining_mixed+=mass
        mixed_terms.append([d,str(mass)])
    group_upper=a*(2-2*r)
    lower=1-beta-remaining_free-remaining_mixed-group_upper
    need(group_upper==F(94,375),'All-height rational group union upper bound')
    need(lower>F(4,125),'All-height direct comparison still exceeds four over125')
    C=F(3)
    for p in primes:
        C*=c[p]
    need(C<8 and lower/C>F(1,250),'Haar density margin survives all nonternary heights')
    M2=F(1)
    for p in [3]+primes:
        M2*=F(p*(p+1),(p-1)**2)
    need(M2==F(17517439415203,525533184000),'Same full geometric second moment for the transported head')
    B=100000
    ell=10
    c_ell=F(201,199)
    moment_sum=F(0)
    falling=1
    for j in range(8):
        if j:
            falling*=8-j
        moment_sum+=F(falling,ell**j)
    tau=c_ell**7/B*F(B,B-3)**2*moment_sum
    final_mass=F(1,250)-M2*tau
    need(final_mass==F(964282896927551623215869645389,308475661132619977601166622720000)
         and final_mass>F(1,320),'Unchanged tail allowance remains available')
    with localcontext() as ctx:
        ctx.prec=60
        conv=lambda x:Decimal(x.numerator)/Decimal(x.denominator)
        exact_lower=conv(1-beta-remaining_free-remaining_mixed)-conv(a)*(2-2*conv(P).sqrt())
        decimal_formula=str(exact_lower)
    result={
        'contract':'3 and5 fixed; reference outside primes7..41; unrestricted finite nonternary heights. On one pure3-avoiding root, only5-stars and mixed cofactors from the original187 exponent palette. Other roots arbitrary at ternary height<=1. No original phases or labels are changed.',
        'input_sha256':sha256(raw).hexdigest(),'checks':checks,
        'pure_caps':{str(p):str(c[p]) for p in primes},'beta':str(beta),'a':str(a),'rho':str(rho),
        'group_exponents':{str(q):[e for d,e in values] for q,values in groups.items()},
        'group_budgets':{str(q):str(t) for q,t in T.items()},'P':str(P),'P_decimal':float(P),
        'remaining_free':str(remaining_free),'remaining_mixed':str(remaining_mixed),
        'remaining_mixed_terms':mixed_terms,'group_union_upper':str(group_upper),
        'direct_rational_lower':str(lower),'direct_rational_lower_decimal':float(lower),
        'direct_square_root_lower_decimal':decimal_formula,
        'haar_cap':str(C),'haar_cap_decimal':float(C),
        'haar_density_rational_lower':str(lower/C),'haar_density_rational_lower_decimal':float(lower/C),
        'M2':str(M2),'tail_tau':str(tau),'tail_final_mass_lower':str(final_mass),
        'tail_final_mass_lower_decimal':float(final_mass),
        'boundaries':['The one-root187 exponent-palette restriction remains.',
                      'Other actual head primes may replace reference primes componentwise only via an injective prime map fixing3 and5.',
                      'Every actual support prime outside the designated head must exceed100000; head primes may be larger, using the inherited head-first exposure order.',
                      'No unrestricted Erdos7 or Lean verification is claimed.']
    }
    Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ('checks','P','P_decimal','direct_rational_lower','direct_rational_lower_decimal',
          'direct_square_root_lower_decimal','haar_cap','haar_cap_decimal','haar_density_rational_lower_decimal',
          'tail_final_mass_lower_decimal')},sort_keys=True))


if __name__=='__main__':
    main()
