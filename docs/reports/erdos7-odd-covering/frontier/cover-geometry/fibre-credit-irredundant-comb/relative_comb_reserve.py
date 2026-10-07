"""Exact actual Report529 side-comb application to the first eight odd primes.

No phase search, LP, integer-period enumeration or large orbit grid is used.
The original family has all nonunit labels 3^i prod(q^e_q), i<=H, e_q<=3.
For C(p,e,a)=((a+1)p^(e-1)-1) mod p^e, its single original CRT phase is:
pure3: C(3,i,0); pureq: C(q,e,0); mixed singleton with i>0:
C(3,i,1),C(q,e,1); support k>=2: ternary C(3,i,1) when i>0,
and C(q,e,min(2k-2+epsilon,q-2)) at every q, epsilon=1[i>0].
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
    if tuple(primes) == Q:
        require(z['count'] == 16540311957403355160121, 'complete Z fibre')
        require(w['count'] == 2569696844461203895339, 'complete W fibre')
        require(cases[1]['refutes_one_sixth'], 'height-five reserve refutation')
        require(cases[2]['below_weaker_threshold'], 'height-six threshold refutation')
        require(repaired_bound == F(11025,1024) < 28, 'same-family repaired query bound')
    return dict(primes=[3,*primes],nonternary_height=3,
                phase_source='Report529 explicit side-comb formula on the first eight odd primes',
                pure_Q_count=str(pure_count),Q_period=str(cofactor_period),
                cofactor_label_count=len(cofactors),
                Z_fibre=z,W_fibre=w,h_z=str(hz),h_w=str(hw),
                limiting_delta=str(hw/hz),cases=cases,
                repaired_query_upper=str(repaired_bound),
                scope='Actual finite-family counterexample only to the relative-reserve candidate. '
                      'No phase optimization and no obstruction to existence of a different '
                      'supported source with complete B<28. No Lean certification claimed here.')


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
