#!/usr/bin/env python3
"""A second actual first-digit colour repairs a retained-core phase conflict.

Ordinary exact arithmetic, complete numerical inventories and prime tails.
No Lean verification or unrestricted Erdos7 conclusion. Standard library only.
"""
from fractions import Fraction as F
from math import comb, factorial, isqrt, lcm, prod
from pathlib import Path
import argparse
import json

Q = (5, 7, 11, 13, 17, 19, 23)
LEAVES = (4, 7, 2, 5, 8)
CHECKS = 0


def need(ok, message):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ValueError(message)


def factors(m):
    h, n = 0, m
    while n % 3 == 0:
        n //= 3
        h += 1
    rest, D = n, 0
    for i, q in enumerate(Q):
        if rest % q == 0:
            D |= 1 << i
            while rest % q == 0:
                rest //= q
    need(rest == 1, 'declared old prime support')
    return h, n, D


def core(leaf_index, x5, other_hits):
    hits = other_hits.bit_count() + int(x5 == 0)
    return hits == 0 if leaf_index < 2 else hits <= 1 and (leaf_index != 2 or x5 != 1)


def responses(t, u, removed):
    zero, one = F(1), F(0)
    for i in range(1, 7):
        if not removed >> i & 1:
            zero, one = zero * (1 - t[i]), one * (1 - t[i]) + zero * t[i]
    atmost = zero + one
    if removed & 1:
        return (zero, zero, atmost, atmost, atmost)
    # The two named colours at5 are mutually exclusive, not independent bits.
    v = t[0]
    need(v >= 0 and u >= 0 and v + u <= 1, 'one categorical first-digit law')
    short = (1 - v) * zero
    long = (1 - v) * atmost + v * zero
    leaf2 = (1 - v - u) * atmost + v * zero
    return (short, short, leaf2, long, long)


def a4(p):
    z = F(1, p - 1)
    return 15*z + 50*z*z + 60*z**3 + 24*z**4


def query(weights, caps, h):
    r, v = max(sum(weights[:2]), sum(weights[2:])), max(weights)
    atoms = {1: F(1)}
    for axis, p in enumerate((3,) + Q):
        def tail(e):
            if e == 0:
                return F(1)
            if p == 3:
                return r if e == 1 else v / 3**(e-2)
            return caps[axis-1] / p**e
        following = {}
        for n, mass in atoms.items():
            for j in range(1, (h-1)//n + 1):
                term = tail(j-1)-tail(j)
                need(term >= 0, 'nonnegative complete-query comparator atom')
                following[n*j] = following.get(n*j, F(0)) + mass*term
        atoms = following
    mean = (1+r+3*v/2)*prod((1+c/(q-1) for c,q in zip(caps,Q)), start=F(1))
    hinge = mean-h+sum(((h-n)*mass for n,mass in atoms.items()), F(0))
    K = (1+15*r+216*v)*prod((1+c*a4(q) for c,q in zip(caps,Q)), start=F(1))*(1+F(28,27)*a4(29))
    return hinge, K, mean


def prime_bridge(spec):
    need((spec['lower'], spec['upper'], spec['ell'], spec['growth'], F(spec['delta']), spec['scale'])
         == (1600, 3000, 7, 21, F(2,7), 10**30), 'fixed complete prime-bridge parameters')
    B, ell, growth, delta, scale = 3000, 7, 21, F(2,7), 10**30
    primes = [n for n in range(1601, 3001) if all(n%d for d in range(2,isqrt(n)+1))]
    need(primes == spec['primes'] and len(primes) == 179, 'all179 interval primes retained')
    need(B >= 286 and ell >= 4 and 3**ell <= B and 4*ell >= growth, 'analytic tail range')
    coeffs = (F(1),) + tuple(F(x)/(1-delta) for x in (15,50,60,24))
    need(all(c <= comb(growth,i) for i,c in enumerate(coeffs)), 'complete quartic growth domination')
    C = F(27,256)/(delta**3*(1-delta))
    def analytic(cutoff, log_lower):
        series = sum((F(factorial(growth),factorial(growth-j)*(3*log_lower)**j)
                      for j in range(growth+1)), F(0))
        return C/3*F(2*log_lower**2+1,2*log_lower**2-1)**growth*F(cutoff,(cutoff-1)**4)*series
    upper = analytic(B, ell)
    rows = []
    for p in reversed(primes):
        raw = C/(p-1)**4+(1+a4(p)/(1-delta))*upper
        rounded = F(-((-raw.numerator*scale)//raw.denominator),scale)
        need(0 <= rounded-raw < F(1,scale), 'outward rounding of full-tail transfer')
        rows.append(dict(prime=p, next=str(upper), previous=str(rounded)))
        upper = rounded
    need(upper == F(spec['expected_upper']), 'declared complete bridge allowance')
    return upper, analytic(1600,6), rows


def calculate(cert):
    global CHECKS
    CHECKS = 0
    need(cert['schema'] == 'second-reference-colour-v1', 'certificate schema')
    need(tuple(cert['primes']) == Q and tuple(cert['leaves']) == LEAVES, 'declared head and ternary interface')
    weights = tuple(map(F,cert['weights']))
    need(weights == (F(1,4),F(1,4),F(1,6),F(1,6),F(1,6)), 'one fixed quarter-law')
    h = cert['threshold']
    need(type(h) is int and h == 16, 'one threshold across every source comparison')
    selected = cert['selected_labels']
    need(len(selected) == len(set(selected)) == 23, 'distinct23 selected numerical labels')
    caps = tuple(F(q-1,q-2) for q in Q)
    beta = [prod((caps[i]/(q-1) for i,q in enumerate(Q) if D>>i&1),start=F(1)) for D in range(128)]
    rem = [[beta[D] if D and (j or D.bit_count()>1) else F(0) for D in range(128)] for j in range(3)]
    for m in selected:
        need(type(m) is int and m>1 and m%2==1, 'odd nonunit numerical selected label')
        j,n,D = factors(m)
        need(j<=2 and D and (j or D.bit_count()>1), 'shallow mixed selected slot')
        rem[j][D] -= prod((caps[i] for i in range(7) if D>>i&1),start=F(1))/n
    need(all(x>=0 for row in rem for x in row), 'nonnegative complete residual inventories')
    family = cert['actual_family']
    need(len({m for m,a in family}) == len(family), 'distinct actual numerical originals')
    for m,a in family:
        need(type(m) is int and type(a) is int and m>1 and m%2==1 and 0<=a<m, 'canonical odd actual original')
        j,n,D = factors(m)
        if m in (3,9):
            need(a == int(m==9), 'common actual ternary anchors')
        else:
            need(D and m in selected, 'displayed old pure-q inventory empty and remaining originals selected')
            for li,l in enumerate(LEAVES):
                if j and l%3**j != a%3**j:
                    continue
                for x5 in range(5):
                    if D&1 and x5!=a%5:
                        continue
                    for bits in range(64):
                        if any(D>>(i+1)&1 and bool(bits>>i&1)!=(a%q==0) for i,q in enumerate(Q[1:])):
                            continue
                        need(not core(li,x5,bits), 'same actual selected class is core-null')
    need(any(m==45 and a==11 for m,a in family), 'actual opposing5 phase on ternary leaf2')
    for li in range(5):
        for x5 in range(5):
            for bits in range(64):
                for D in range(128):
                    need(core(li,x5,bits) <= core(li,2 if D&1 else x5,bits&~(D>>1)),
                         'one common safe replacement enlarges every leaf core')
    period = lcm(9,*Q,*(m for m,a in family))
    x = cert['witness']
    need(type(x) is int and 0<=x<period and x%9 in LEAVES, 'resolving CRT witness')
    bits = sum((x%q==0)<<i for i,q in enumerate(Q[1:]))
    need(core(LEAVES.index(x%9),x%5,bits) and all(x%m!=a for m,a in family), 'one actual witness in the new core')

    def lower(t,u):
        multipliers=[]
        for D in range(128):
            z=tuple(w*A for w,A in zip(weights,responses(t,u,D)))
            multipliers.append((sum(z),max(sum(z[:2]),sum(z[2:])),max(z)))
        mass=multipliers[0][0]
        high=sum((beta[D]*multipliers[D][2]/2 for D in range(128)),F(0))
        low=sum((rem[j][D]*multipliers[D][j] for D in range(128) for j in range(3)),F(0))
        return dict(core=str(mass),high=str(high),low=str(low),alpha=str(mass-high-low))
    haar=lower(tuple(F(1,q) for q in Q),F(1,5))
    alpha=F(haar['alpha'])
    need(alpha == F(cert['expected_haar_alpha']) and alpha>0, 'positive declared Haar source lower bound')
    vertices=[]
    for mask in range(256):
        t=tuple(caps[i]/q if mask>>i&1 else F(0) for i,q in enumerate(Q))
        u=caps[0]/5 if mask&128 else F(0)
        vertices.append(lower(t,u))
    worst=min(range(256),key=lambda i:F(vertices[i]['alpha']))
    need(worst==cert['expected_worst_vertex'] and F(vertices[worst]['alpha'])==F(cert['expected_box_alpha'])<0,
         'retained arbitrary-pure box failure control')
    hinge,K,mean=query(weights,caps,h)
    T,direct,steps=prime_bridge(cert['tail'])
    query_upper=h+hinge/alpha
    final=(28-query_upper)/27-K*T/alpha
    need(final>F(cert['mass_floor'])>0, 'same-law complete1600 tail strict floor')
    direct_final=(28-query_upper)/27-K*direct/alpha
    need(direct_final<0, 'direct analytic1600 bound fails in this fixed control')
    # Two real pure25 survivors have identical old zero-hit probability.
    readouts=[]
    for hole in (1,2):
        survivors=[x for x in range(25) if x!=hole]
        readouts.append((F(sum(x%5==0 for x in survivors),24),F(sum(x%5==1 for x in survivors),24)))
    need(readouts==[(F(5,24),F(1,6)),(F(5,24),F(5,24))], 'same old readout different second colour')
    need(not core(2,1,0) and core(2,2,0) and (1==0)==(2==0), 'binary reference merges different actual core membership')
    return dict(schema='second-reference-colour-result-v1',check_count=CHECKS,
                scope='Ordinary conditional theorem: empty old pure-q inventories, stated23 common phase-null slots, arbitrary unlisted mixed/high3/29 and primes>1600; not arbitrary shallow phases or unrestricted Erdos7; no Lean.',
                weights=list(map(str,weights)),actual_family=family,period=period,witness=x,
                haar=haar,all256_vertices=vertices,worst_vertex=worst,
                threshold=h,complete_hinge=str(hinge),complete_mean=str(mean),fourth_with29=str(K),
                query_upper=str(query_upper),tail_bridge=str(T),bridge_steps=steps,
                final_mass=str(final),final_mass_decimal=float(final),mass_floor=cert['mass_floor'],
                direct1600_final=str(direct_final),binary_readout_counterexample=[[str(a),str(b)] for a,b in readouts])


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
        need(result==json.loads(args.result.read_text()),'retained result exact replay')
    print(json.dumps({k:result[k] for k in ('check_count','final_mass_decimal','mass_floor','worst_vertex')},indent=2))


if __name__=='__main__':
    main()
