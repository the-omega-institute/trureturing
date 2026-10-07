"""Exact actual Report529 side-comb application to the first eight odd primes.

No phase search, LP or large orbit grid is used. The low-null H=1,2 controls
enumerate their small integer periods; the main side-comb count is weighted.
The original family has all nonunit labels 3^i prod(q^e_q), i<=H, e_q<=3.
For C(p,e,a)=((a+1)p^(e-1)-1) mod p^e, its single original CRT phase is:
pure3: C(3,i,0); pureq: C(q,e,0); mixed singleton with i>0:
C(3,i,1),C(q,e,1); support k>=2: ternary C(3,i,1) when i>0,
and C(q,e,min(2k-2+epsilon,q-2)) at every q, epsilon=1[i>0].
The high-phase extension checks conditional budgets, not arbitrary families.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import prod
from pathlib import Path
import argparse
import json

Q = (5, 7, 11, 13, 17, 19, 23)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def count_sides(primes, epsilons, first_side):
    """Count exact surviving Q-coordinates in prod(q^3), with fixed phases."""
    n = len(primes)
    events = []
    for k in range(2, n + 1):
        for support in combinations(range(n), k):
            for epsilon in epsilons:
                events.append(tuple((j, min(2*k-2+epsilon, primes[j]-2))
                                    for j in support))
    visits = 0

    @lru_cache(None)
    def walk(j, live):
        nonlocal visits
        visits += 1
        require(visits <= 50000, "small-control state limit")
        # A previously fully met actual forbidden rectangle covers this fibre.
        if any(all(axis < j for axis, _ in events[i]) for i in live):
            return 0
        if j == n:
            return 1
        q = primes[j]
        side_size = q*q + q + 1
        groups = {}
        for side in tuple(range(first_side, q-1)) + (-1,):
            remaining = tuple(i for i in live if
                              all(axis != j or value == side
                                  for axis, value in events[i]))
            # The all-(q-1) depth-three prefix is the one-point tail.
            size = 1 if side == -1 else side_size
            groups[remaining] = groups.get(remaining, 0) + size
        return sum(size * walk(j+1, remaining)
                   for remaining, size in groups.items())

    count = walk(0, tuple(range(len(events))))
    return dict(count=count, states=visits, cache_hits=walk.cache_info().hits,
                mixed_side_events=len(events))


def high_phase_extension(beta, h):
    """Conditional budget; low nonpure projections must vanish under one Q law."""
    require(beta >= 1 and h >= 1, 'complete query norm and positive cut height')
    loss = (beta-1) / 3**h
    reserve = 1-loss
    require(reserve > 0, 'positive reserve required before conditioning')
    bound = 1+(2*beta-1)/reserve
    threshold = F(28*3**h+27, 2*3**h+27)
    require((bound < 28) == (beta < threshold), 'equivalent source threshold')
    return dict(low_null_through_height=h, arbitrary_mixed_from_height=h+1,
                beta_upper=str(beta), deletion_upper=str(loss),
                reserve_lower=str(reserve), complete_query_upper=str(bound),
                beta_threshold_for_28=str(threshold), below_28=bound < 28,
                margin_to_28=str(28-bound))


def low_null_control(H):
    """Actual fixed CRT inventory refuting universal economical low-null selection."""
    require(H in (1,2), 'finite control height')

    def side(p, e, a):
        return (a+1)*p**(e-1)-1

    def crt(parts):
        residue, modulus = 0, 1
        for a, m in parts:
            residue += modulus*((a-residue)*pow(modulus, -1, m) % m)
            modulus *= m
        return residue, modulus

    originals = []
    projections = []
    private = []
    p5, p7 = 5**H, 7**H
    for e, f in product(range(H+1), repeat=2):
        if e == f == 0:
            continue
        for j in range(3):
            parts = []
            x5, x7 = p5-1, p7-1
            if e:
                x5 = side(5, e, 3 if f else j)
                parts.append((x5, 5**e))
            if f:
                x7 = side(7, f, 3+j if e else j)
                parts.append((x7, 7**f))
            projections.append(crt(parts))
            originals.append(crt(parts + ([(1, 3**j)] if j else [])))
            private.append(crt([(1 if j else 0, 9), (x5,p5), (x7,p7)])[0])
    require(len(originals) == 3*(H*H+2*H), 'complete low-layer original count')
    require(len({m for _,m in originals}) == len(originals), 'distinct numerical originals')
    require(all(m > 1 and m % 2 for _,m in originals), 'odd nonunit originals')
    require(all(x % m == a and sum(x % n == b for b,n in originals) == 1
                for (a,m),x in zip(originals,private)), 'one private point per original')
    survivors = {x for x in range(p5*p7)
                 if all(x % n != a for a,n in projections)}
    def allowed(x, p, sides):
        return x % (p**H) == p**H-1 or any(
            x % (p**e) == side(p,e,a) for e in range(1,H+1) for a in sides)
    predicted = {x for x in range(p5*p7)
                 if allowed(x,5,(3,)) and allowed(x,7,(3,4,5))
                 and (x % p5 == p5-1 or x % p7 == p7-1)}
    require(survivors == predicted, 'exact common low-projection survivor')
    period = 9*p5*p7
    cheap = [x for x in range(period) if x % 3 == 0 and x % 5 == x % 7 == 1]
    require(len(cheap) == period//105, 'entire cheap product-source support')
    require(all(all(x % n != a for a,n in originals) for x in cheap),
            'cheap source avoids every actual original')
    return dict(H=H,original_count=len(originals),private_witnesses=len(private),
                projected_period=p5*p7,projected_survivors=len(survivors),
                actual_period=period,cheap_source_residues=len(cheap))


def run(primes=Q):
    # Each side is a disjoint union of cylinders of depths1,2,3.
    for rank, q in enumerate(primes, 1):
        require(q-2 >= 2*rank, 'private-point side separation')
        buckets = []
        for side in range(q-1):
            vals = set()
            for e in range(1, 4):
                residue = (side+1)*q**(e-1)-1
                part = set(range(residue, q**3, q**e))
                require(not vals.intersection(part), "one side depth disjointness")
                vals.update(part)
            require(len(vals) == q*q+q+1, "side-cylinder exact finite size")
            buckets.append(vals)
        require(sum(map(len, buckets))+1 == q**3, "all sides plus tail cover")
        require(len(set().union(*buckets)) == q**3-1, "sides pairwise disjoint")
        require(q**3-1 not in set().union(*buckets), "literal common tail")

    z = count_sides(primes, (0,), 1)
    w = count_sides(primes, (0, 1), 2)
    pure_count = prod(q**3-q*q-q-1 for q in primes)
    hz = F(z['count'], pure_count)
    hw = F(w['count'], pure_count)
    cofactor_period = prod(q**3 for q in primes)
    cofactors = [prod(q**e for q,e in zip(primes,es))
                 for es in product(range(4), repeat=len(primes))]
    require(len(cofactors) == len(set(cofactors)) == 4**len(primes),
            "all numerical cofactor labels distinct")
    require(all(n%3 and n%2 and cofactor_period%n == 0 for n in cofactors),
            "same odd ternary-free cofactor period")
    cases=[]
    for H in (4,5,6):
        power = 3**H
        # V3 consists of the T_i cylinders and the one terminal tail.
        v3_count=(power+1)//2
        t_count=(power-1)//2
        U = t_count*w['count'] + z['count']
        U0 = v3_count*z['count']
        period=power*cofactor_period
        labels=[3**i*n for i in range(H+1) for n in cofactors if 3**i*n>1]
        require(len(labels)==len(set(labels))==(H+1)*4**len(primes)-1,
                "all full original numerical labels distinct")
        require(all(m>1 and m%2 and period%m==0 for m in labels),
                "full actual labels odd nonunit divisors of the same period")
        delta=F(U,U0)
        zeta=F(2,power+1)
        require(delta==(1-zeta)*hw/hz+zeta, "same-source relative-mass identity")
        cases.append(dict(H=H,original_count=len(labels),period=str(period),
                          U_count=str(U),U0_count=str(U0),
                          six_U_minus_U0=str(6*U-U0),delta=str(delta),
                          delta_decimal=float(delta),
                          refutes_one_sixth=6*U<U0,
                          below_weaker_threshold=delta<F(21876797,136331397),
                          haar_U=str(F(U,period)),haar_U0=str(F(U0,period))))
    repaired_bound = 2*prod((1+F(1,q-1-2*r) for r,q in enumerate(primes,1)), start=F(1))
    high_phase_cases = [high_phase_extension(repaired_bound/2, h) for h in (2,4)]
    low_null_cases = [low_null_control(H) for H in (1,2)]
    cheap_bound = F(5,2)*F(9,4)*F(13,6)*prod(
        (F(p,p-1) for p in (11,13,17,19,23)), start=F(1))
    require(cheap_bound == F(1255501,73728) < 28, 'all-height cheap-source query norm')
    require(F(7) > F(31,5), 'height-six forced norm excludes low-null source threshold')
    # Reuse Report563 MT11's complete Q7 source bound; check only its new consumer.
    active_beta = F(13463054,5049311)
    active_debit = (active_beta-1)/3
    active_reserve = 1-active_debit
    require(active_reserve > 0, 'root-active positive reserve')
    active_bound = 1+(3*active_beta-1)/active_reserve
    require(active_bound == (1+8*active_beta)/(4-active_beta), 'same-law active-root budget')
    require(active_bound == F(37584581,2244730) < 28, 'active-root complete query bound')
    require(active_beta < F(37,12), 'active-root source threshold')
    if tuple(primes) == Q:
        require(z['count'] == 16540311957403355160121, 'complete Z fibre')
        require(w['count'] == 2569696844461203895339, 'complete W fibre')
        require(cases[1]['refutes_one_sixth'], 'height-five reserve refutation')
        require(cases[2]['below_weaker_threshold'], 'height-six threshold refutation')
        require(repaired_bound == F(11025,1024) < 28, 'same-family repaired query bound')
        require(high_phase_cases[0]['reserve_lower'] == '9455/18432',
                'height-two positive reserve')
        require(high_phase_cases[0]['complete_query_upper'] == '189473/9455',
                'arbitrary high phases after depth two')
        require(high_phase_cases[0]['beta_threshold_for_28'] == '31/5',
                'height-two complete source threshold')
        require(high_phase_cases[1]['reserve_lower'] == '156911/165888',
                'height-four positive reserve')
        require(high_phase_cases[1]['complete_query_upper'] == '1777073/156911',
                'arbitrary high phases after depth four')
        require(F(high_phase_cases[1]['complete_query_upper']) < 12,
                'height-four stronger query bound')
        require((repaired_bound/2-1)/3 >= 1,
                'height-one debit does not certify a positive reserve')
    return dict(primes=[3,*primes],nonternary_height=3,
                phase_source='Report529 explicit side-comb formula on the first eight odd primes',
                pure_Q_count=str(pure_count),Q_period=str(cofactor_period),
                cofactor_label_count=len(cofactors),
                Z_fibre=z,W_fibre=w,h_z=str(hz),h_w=str(hw),
                limiting_delta=str(hw/hz),cases=cases,
                repaired_query_upper=str(repaired_bound),
                arbitrary_high_phase_extension=high_phase_cases,
                low_projection_obstruction=dict(
                    controls=low_null_cases,forced_norm_formula='H+1',
                    height_six_original_count=3*(6**2+2*6),
                    height_27_original_count=3*(27**2+2*27),
                    cheap_complete_query_norm=str(cheap_bound),
                    cheap_margin_to_28=str(28-cheap_bound)),
                active_root_extension=dict(
                    cofactor_source='Report563 MT11',beta_upper=str(active_beta),
                    deletion_upper=str(active_debit),reserve_lower=str(active_reserve),
                    complete_query_upper=str(active_bound),
                    source_threshold_for_28='37/12',
                    scope='One unblocked ternary root; at most one distinct active Q phase '
                          'per nonunit cofactor through ternary depth two, including depth zero. '
                          'This checks the supplied source bound consumer, not MT11 again.'),
                scope='Exact finite controls for the relative-reserve and low-projection strategies; '
                      'neither obstructs existence of a different supported source with complete B<28. '
                      'The HP extension budgets require one Q law '
                      'annihilating every low nonpure projection, including ternary-free originals. '
                      'Arbitrary-height constructions are justified in Report529, not by enumeration. '
                      'No Lean certification claimed by this arithmetic consumer.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='write exact results to this path instead of checking the retained data')
    args=parser.parse_args()
    result=run()
    if args.output is None:
        expected=json.loads(Path(__file__).with_suffix('.json').read_text())
        require(result==expected, 'retained exact result differs from fresh computation')
    else:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
