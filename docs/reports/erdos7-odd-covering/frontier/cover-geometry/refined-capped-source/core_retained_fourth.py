#!/usr/bin/env python3
"""Complete fourth-query bounds retaining one actual decreasing core.

Ordinary exact certificate controls, not Lean or unrestricted Erdos7.
The normalized source is lambda restricted to V=U intersect G; it is not
silently identified with lambda restricted to the entire old survivor U.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod
from pathlib import Path
import argparse
import json

Q = (5, 7, 11, 13, 17, 19, 23)
LEAVES = (4, 7, 2, 5, 8)
CHECKS = 0


def need(ok, label):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ValueError(label)


def factors(m):
    n, exponents = m, []
    for p in (3,) + Q:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        exponents.append(e)
    need(n == 1, 'old support uses only the stated eight primes')
    return exponents


def core(leaf, hits):
    return hits == 0 if leaf % 3 == 1 else hits.bit_count() <= 1


def responses(t, removed):
    zero, one = F(1), F(0)
    for i, p in enumerate(t):
        if removed >> i & 1:
            continue
        zero, one = zero * (1-p), one * (1-p) + zero * p
    need(type(zero) is F and type(one) is F and 0 <= zero <= zero+one <= 1,
         'exact no-hit and at-most-one-hit responses')
    return zero, zero+one


def a4(p):
    z = F(1, p-1)
    return 15*z + 50*z*z + 60*z**3 + 24*z**4


def query_hinge(weights, caps, h):
    r, v = max(sum(weights[:2]), sum(weights[2:])), max(weights)
    atoms = {1: F(1)}
    for axis, p in enumerate((3,) + Q):
        def tail(j):
            if j == 1:
                return F(1)
            if axis == 0:
                return r if j == 2 else v / 3**(j-3)
            return caps[axis-1] / p**(j-1)
        following = {}
        for n, mass in atoms.items():
            for j in range(1, (h-1)//n+1):
                atom = tail(j)-tail(j+1)
                need(atom >= 0, 'nonnegative auxiliary query atom')
                following[n*j] = following.get(n*j,F(0)) + mass*atom
        atoms = following
    mean = (1+r+3*v/2)*prod((1+c/(p-1) for p,c in zip(Q,caps)), start=F(1))
    hinge = mean-h+sum(((h-n)*mass for n,mass in atoms.items()),F(0))
    need(hinge > 0, 'complete hinge includes its full infinite tail')
    return hinge, mean


def tail_charge(cutoff, ell):
    delta, growth = F(2,7), 21
    need(type(cutoff) is int and type(ell) is int and cutoff >= 286 and ell >= 4
         and 3**ell <= cutoff and 4*ell >= growth, 'complete analytic tail range')
    need(all(F(x)/(1-delta) <= comb(growth,j)
             for j,x in enumerate((15,50,60,24),1)), 'quartic growth domination')
    return (F(27,256)/(3*delta**3*(1-delta))
            *F(2*ell*ell+1,2*ell*ell-1)**growth*F(cutoff,(cutoff-1)**4)
            *sum((F(factorial(growth),factorial(growth-j)*(3*ell)**j)
                  for j in range(growth+1)),F(0)))


def literal_query_control():
    """All independently phased numerical queries on an actual period45 source."""
    points=[]
    leaf_weights=dict(zip(LEAVES,(3,3,2,2,2)))
    for x in range(45):
        leaf=x%9
        if leaf not in leaf_weights or (leaf%3 == 1 and x%5 == 0):
            continue
        points.append((x,leaf_weights[leaf]))
    moduli=(3,5,9,15,45)
    menus=[tuple(tuple(int(x%m == a) for x,_ in points) for a in range(m)) for m in moduli]
    empty=F(9,10)+15*F(1,2)+65*F(1,5)
    active=3*(1+15*F(1,2)+65*F(1,4))
    bound=empty+active
    full=4*(1+15*F(1,2)+65*F(1,4))
    largest,chosen,count=-1,None,0
    for phases in product(*(range(m) for m in moduli)):
        columns=[menu[a] for menu,a in zip(menus,phases)]
        score=sum(w*(1+sum(column[i] for column in columns))**4 for i,(_,w) in enumerate(points))
        need(score <= 60*bound, 'literal independent-phase query obeys retained-core moment')
        if score > largest:
            largest,chosen=score,phases
        count+=1
    actual=F(largest,60)
    need(count == 91125 and actual == F(1883,20) and bound == F(1913,20) and bound < full == 99,
         'literal query maximum and strict core improvement')
    return dict(period=45,layout_count=count,retained_source_mass=str(F(sum(w for _,w in points),60)),
                maximum_raw_fourth=str(actual),maximizing_phases=list(chosen),
                retained_core_upper=str(bound),uncut_upper=str(full))


def calculate(cert):
    global CHECKS
    CHECKS = 0
    need(cert['schema'] == 'core-retained-fourth-v1', 'certificate schema')
    need(tuple(cert['primes']) == Q and tuple(cert['leaves']) == LEAVES,
         'declared prime and leaf coordinates')
    need(cert['source_definition'] == 'V=U intersect G; nu=lambda|V/lambda(V)',
         'explicit core-restricted source')
    need(cert['core'] == 'short:no hits; long:at most one hit', 'one shared decreasing core')
    need(cert['reference_digits'] == [0]*7, 'one common reference digit per prime')
    caps = tuple(F(p-1,p-2) for p in Q)
    selected = cert['selected_labels']
    need(len(selected) == len(set(selected)), 'distinct selected numerical labels')
    beta = tuple(prod((caps[i]/(p-1) for i,p in enumerate(Q) if d >> i & 1),start=F(1))
                 for d in range(128))
    residual = [[beta[d] if d and (j > 0 or d.bit_count() >= 2) else F(0)
                 for d in range(128)] for j in range(3)]
    for m in selected:
        need(type(m) is int and m > 1 and m % 2 == 1, 'odd nonunit selected label')
        es = factors(m)
        j, d = es[0], sum(1 << i for i,e in enumerate(es[1:]) if e)
        need(j <= 2 and d and (j > 0 or d.bit_count() >= 2), 'selected shallow mixed label')
        residual[j][d] -= prod((caps[i] for i in range(7) if d >> i & 1),start=F(1))/ (m//3**j)
    need(all(x >= 0 for row in residual for x in row), 'nonnegative complete remaining inventories')
    family = cert['actual_family']
    need(len({row['modulus'] for row in family}) == len(family), 'distinct actual numerical moduli')
    null_labels = []
    for row in family:
        m, a = row['modulus'], row['phase']
        need(type(m) is int and m > 1 and m % 2 == 1
             and type(a) is int and 0 <= a < m, 'canonical actual odd class')
        es = factors(m)
        if m in (3,9):
            need(a == int(m == 9), 'one common pure3/9 normalization')
        if m not in selected:
            continue
        for leaf in LEAVES:
            for hits in range(128):
                meets = (not es[0] or leaf % 3**min(es[0],2) == a % 3**min(es[0],2))
                meets = meets and all(not e or bool(hits >> i & 1) == (a % p == 0)
                                      for i,(p,e) in enumerate(zip(Q,es[1:])))
                need(not (core(leaf,hits) and meets), 'selected actual class is pointwise core-null')
        null_labels.append(m)
    for leaf in LEAVES:
        for hits in range(128):
            for removed in range(128):
                need(not core(leaf,hits) or core(leaf,hits & ~removed),
                     'erasing queried hit coordinates enlarges the same core')
    need(3**4-2**4 == 65 and 9*(a4(3)-F(15,3)) == 216,
         'complete ternary maximum-depth coefficients')
    need(9*(a4(3)-F(15,3))-65 == 151, 'all ternary heights above two retained')
    coeff = tuple(prod((caps[i]*a4(p) for i,p in enumerate(Q) if d >> i & 1),start=F(1))
                  for d in range(128))
    T29 = 1+F(28,27)*a4(29)
    cases = []
    for case in cert['cases']:
        weights = tuple(map(F,case['weights']))
        need(len(weights) == 5 and all(w >= 0 for w in weights) and sum(weights) == 1,
             'one fixed normalized five-leaf law')
        h = case['fixed_threshold']
        need(type(h) is int and 1 <= h < 28, 'one global complete-query threshold')
        mode = case['source_mode']
        need(mode in ('box','haar'), 'declared pure-q source regime')
        if mode == 'haar':
            need(not any(factors(row['modulus'])[0] == 0 and sum(e>0 for e in factors(row['modulus'])[1:]) == 1
                         for row in family), 'empty actual pure-q inventories for Haar source')
        root0,root1 = sum(weights[:2]),sum(weights[2:])
        leaf0,leaf1 = max(weights[:2]),max(weights[2:])
        oldK = (1+15*max(root0,root1)+216*max(weights))*prod((1+c*a4(p) for p,c in zip(Q,caps)),start=F(1))
        H,mean = query_hinge(weights,caps,h)

        def values(t):
            fs=[]
            for d in range(128):
                A,B = responses(t,d)
                fs.append((root0*A+root1*B,max(root0*A,root1*B),max(leaf0*A,leaf1*B)))
            mass=fs[0][0]
            high=sum((beta[d]*fs[d][2]/2 for d in range(128)),F(0))
            low=sum((residual[j][d]*fs[d][j] for j in range(3) for d in range(128)),F(0))
            K=sum((coeff[d]*(fs[d][0]+15*fs[d][1]+216*fs[d][2]) for d in range(128)),F(0))
            need(0 < K <= oldK, 'retaining the core weakens no quartic cap')
            return dict(source_lower=str(mass-high-low),core_mass=str(mass),high_loss=str(high),
                        shallow_loss=str(low),core_fourth=str(K))

        vertices=[]
        for mask in range(128):
            t=tuple(c/p if mask >> i & 1 else F(0) for i,(p,c) in enumerate(zip(Q,caps)))
            vertices.append(dict(mask=mask,**values(t)))
        haar=values(tuple(F(1,p) for p in Q))
        used=vertices if mode == 'box' else [dict(mask='haar',**haar)]
        least=min(F(v['source_lower']) for v in used)
        need(least > 0 and least == F(case['expected_source_lower']), 'retained positive V source bound')
        tails=[]
        for spec in case['tails']:
            tau=tail_charge(spec['cutoff'],spec['ell'])
            eps=F(spec['mass_floor'])
            need(0 <= eps < F(28-h,27), 'positive coefficient for separately concave floor slack')
            rows=[]
            for v in used:
                L,K=F(v['source_lower']),F(v['core_fourth'])*T29
                slack=(28-h-27*eps)*L-H-27*K*tau
                reserve=F(28-h,27)-(H/27+K*tau)/L
                rows.append(dict(mask=v['mask'],floor_slack=str(slack),reserve=str(reserve),
                                 reserve_decimal=float(reserve)))
            worst=min(rows,key=lambda v:F(v['reserve']))
            min_slack=min(F(v['floor_slack']) for v in rows)
            need((min_slack > 0) == spec['expected_pass'], 'declared same-source continuation outcome')
            need(worst['mask'] == spec['expected_worst_mask'], 'declared continuation worst endpoint')
            if spec['expected_pass']:
                need(all(F(v['reserve']) > eps for v in rows), 'all declared endpoint floors hold strictly')
            tails.append(dict(cutoff=spec['cutoff'],ell=spec['ell'],fixed_threshold=h,
                              mass_floor=str(eps),passes=min_slack > 0,tau=str(tau),
                              minimum_floor_slack=str(min_slack),worst=worst,vertices=rows))
        # Exact interior controls of both convex moment and concave source envelopes.
        midpoint_controls=0
        for axis in range(7):
            t=[F(c,p) for p,c in zip(Q,caps)]
            t[axis]=F(0)
            left=values(tuple(t))
            t[axis]=caps[axis]/Q[axis]
            right=values(tuple(t))
            t[axis]/=2
            mid=values(tuple(t))
            need(2*F(mid['source_lower']) >= F(left['source_lower'])+F(right['source_lower']),
                 'coordinate source concavity control')
            need(2*F(mid['core_fourth']) <= F(left['core_fourth'])+F(right['core_fourth']),
                 'coordinate moment convexity control')
            midpoint_controls+=2
        cases.append(dict(name=case['name'],weights=list(map(str,weights)),source_mode=mode,
                          fixed_threshold=h,source_lower=str(least),complete_hinge=str(H),
                          complete_comparator_mean=str(mean),uncut_fourth=str(oldK),
                          vertices=vertices,haar=haar,midpoint_controls=midpoint_controls,tails=tails))
    literal=literal_query_control()
    return dict(schema='core-retained-fourth-result-v1',check_count=CHECKS,
                scope='One fixed lambda per case, restricted to V=U intersect G and normalized once; complete arbitrary-phase queries, all old heights and the stated29/prime tails. Not unrestricted Erdos7 or Lean.',
                selected_labels=selected,actual_null_labels=sorted(null_labels),
                ternary_coefficients=dict(depth1=15,depth2=65,above2=151,at_least2=216),
                pure29_factor=str(T29),support_coefficients=list(map(str,coeff)),
                literal_query_control=literal,cases=cases)


def main():
    here=Path(__file__)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=here.with_name(here.stem+'_certificate.json'))
    parser.add_argument('--result',type=Path,default=here.with_suffix('.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=calculate(json.loads(args.certificate.read_text()))
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:
        need(result==json.loads(args.result.read_text()),'retained exact result replay')
    print(json.dumps(dict(check_count=result['check_count'],cases=[dict(name=c['name'],
                           tails=[dict(cutoff=t['cutoff'],passes=t['passes'],reserve=t['worst']['reserve_decimal'])
                                  for t in c['tails']]) for c in result['cases']])))


if __name__=='__main__':
    main()
