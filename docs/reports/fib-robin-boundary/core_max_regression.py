#!/usr/bin/env python3
from fractions import Fraction
from decimal import Decimal,localcontext
from itertools import combinations_with_replacement
import sys
sys.dont_write_bytecode = True

import argparse
import copy
import hashlib
import json
from pathlib import Path
from core_max import build
from core_max_check import check

PROFILE = [21,13,9,7,6]
CORE_PRIMES = [2,3,5,7,11]


def product(values):
    out = 1
    for x in values:
        out *= x
    return out


def z_of_core_multiple(t):
    # Merge exponents: Z(M*t) is NOT computed as Z(M)*Z(t).
    exponents = dict(zip(CORE_PRIMES,PROFILE))
    residue = t
    p = 2
    while p*p <= residue:
        while residue%p==0:
            exponents[p] = exponents.get(p,0)+1
            residue //= p
        p += 1
    if residue > 1:
        exponents[residue] = exponents.get(residue,0)+1
    return product(Fraction(p**(a+1)-1,(p-1)*p**a) for p,a in exponents.items())


def reject(cert,label):
    try:
        check(cert)
    except (ValueError,KeyError):
        return label
    raise AssertionError('bad certificate accepted: '+label)


def factors(n):
    result = []
    p = 2
    while p*p <= n:
        a = 0
        while n%p==0:
            a += 1
            n //= p
        if a:
            result.append((p,a))
        p += 1
    if n>1:
        result.append((n,1))
    return result


def check_nonmonotone():
    rows = []
    canonical = []
    for n in range(150,1201,150):
        # Direct divisor enumeration, independent of product-formula code.
        value = Fraction(sum(d for d in range(1,n+1) if n%d==0),n)
        fs = factors(n)
        support = [p for p,a in fs]
        prime_prefix = [p for p in range(2,support[-1]+1)
                        if all(p%d for d in range(2,p))]
        is_canonical = support==prime_prefix and all(a>=b for (_,a),(_,b) in zip(fs,fs[1:]))
        row = {'n':n,'value':[value.numerator,value.denominator],
               'factorization':fs,'canonical':is_canonical}
        rows.append(row)
        if is_canonical:
            canonical.append((value,n))
    global_best = max((Fraction(*r['value']),r['n']) for r in rows)
    canonical_best = max(canonical)
    assert global_best==(Fraction(961,300),1200)
    assert canonical==[(Fraction(2821,900),900)]
    assert global_best[0]-canonical_best[0]==Fraction(31,450)
    assert 720%150!=0
    result = {'status':'PASS','core':150,'profile':[1,1,2],'bound':1200,
              'all_feasible_integers':rows,'actual_maximizer':1200,
              'actual_maximum':[961,300],'canonical_maximizer':900,
              'canonical_maximum':[2821,900],'lost_gap':[31,450],
              'invalid_swap':{'from':1200,'to':720,'reason':'5 exponent drops below mandatory 2'}}
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True,help='results and certificate directory')
    OUT = ap.parse_args().out
    OUT.mkdir(parents=True,exist_ok=True)
    core = product(p**a for p,a in zip(CORE_PRIMES,PROFILE))
    large = []
    certs = []
    for multiplier in [1,2,10,1000]:
        cert = build(PROFILE,core*multiplier)
        certs.append(cert)
        path = OUT/f'certificate-core-times-{multiplier}.json'
        raw = (json.dumps(cert,separators=(',',':'))+'\n').encode()
        path.write_bytes(raw)
        result = check(json.loads(raw))
        direct = max((z_of_core_multiple(t),-t) for t in range(1,multiplier+1))
        assert Fraction(*result['maximum'])==direct[0]
        assert result['witness']==core*(-direct[1])
        result['budget_multiplier'] = multiplier
        result['attaining_core_multiplier'] = -direct[1]
        result['direct_all_multiples_checked'] = multiplier
        with localcontext() as ctx:
            ctx.prec=35
            result['maximum_decimal_display'] = str(Decimal(direct[0].numerator)/direct[0].denominator)
        result['certificate_path'] = path.name
        result['certificate_sha256'] = hashlib.sha256(raw).hexdigest()
        large.append(result)

    limit = 180
    sigma = [0]*(limit+1)
    for d in range(1,limit+1):
        for n in range(d,limit+1,d):
            sigma[n] += d
    profiles = [[]]
    for length in range(1,4):
        profiles.extend(list(reversed(a)) for a in combinations_with_replacement(range(1,4),length))
    count = 0
    infeasible = 0
    for profile in profiles:
        m = product(p**a for p,a in zip(CORE_PRIMES,profile))
        best = None
        for bound in range(1,limit+1):
            if bound%m==0:
                candidate = Fraction(sigma[bound],bound)
                best = candidate if best is None else max(best,candidate)
            result = check(build(profile,bound))
            found = None if result['maximum'] is None else Fraction(*result['maximum'])
            assert found==best,(profile,bound,found,best)
            if best is None:
                infeasible += 1
            else:
                assert result['witness']%m==0
                assert Fraction(sigma[result['witness']],result['witness'])==best
            count += 1

    base = certs[-1]
    root_index = next(i for i,s in enumerate(base['states']) if s['key']==base['root'])
    rejected = []
    bad = copy.deepcopy(base)
    bad['profile'] = [13,21,9,7,6]
    rejected.append(reject(bad,'nonmonotone profile'))
    bad = copy.deepcopy(base)
    bad['states'][root_index]['infeasible']='remaining-core-budget'
    bad['states'][root_index]['value']=None
    bad['states'][root_index]['witness']=None
    rejected.append(reject(bad,'false infeasible root'))
    bad = copy.deepcopy(base)
    branch = next(b for b in bad['states'][root_index]['branches'] if 'child' in b)
    del branch['child']
    branch['pruned']='remaining-core-budget'
    rejected.append(reject(bad,'false remaining-core pruning'))
    bad = copy.deepcopy(base)
    bad['states'][root_index]['branches'].pop()
    rejected.append(reject(bad,'missing allowed branch'))
    bad = copy.deepcopy(base)
    bad['states'][root_index]['value']=[1,1]
    bad['states'][root_index]['witness']=1
    rejected.append(reject(bad,'illegal empty suffix before required core'))
    bad = copy.deepcopy(base)
    bad['core_suffix'][1] -= 1
    rejected.append(reject(bad,'altered remaining core product'))

    result = {'status':'PASS','core':core,'profile':PROFILE,
              'mandatory_core_results':large,
              'small_exhaustive_profiles':profiles,'small_exhaustive_bound':limit,
              'nonmonotone_counterexample':check_nonmonotone(),
              'small_exact_comparisons':count,'small_infeasible_comparisons':infeasible,
              'corruptions_rejected':rejected,
              'source_hashes':{p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest()
                               for p in ['core_max.py','core_max_check.py','core_max_regression.py']},
              'scope':'Exact finite arithmetic; no RH assertion or Lean proof.'}
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
