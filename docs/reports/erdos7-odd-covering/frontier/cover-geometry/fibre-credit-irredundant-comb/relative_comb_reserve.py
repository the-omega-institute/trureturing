"""Exact actual Report529 side-comb application to the first eight odd primes.

No phase search, LP or large orbit grid is used. The low-null H=1,2 controls
enumerate their small integer periods; the main side-comb count is weighted.
The original family has all nonunit labels 3^i prod(q^e_q), i<=H, e_q<=3.
For C(p,e,a)=((a+1)p^(e-1)-1) mod p^e, its single original CRT phase is:
pure3: C(3,i,0); pureq: C(q,e,0); mixed singleton with i>0:
C(3,i,1),C(q,e,1); support k>=2: ternary C(3,i,1) when i>0,
and C(q,e,min(2k-2+epsilon,q-2)) at every q, epsilon=1[i>0].
The high-phase extension checks conditional budgets, not arbitrary families.
The auxiliary-root control reuses the existing clique-polynomial consumer.
The active-leaf control checks the supplied MT11 consumer and actual inventories.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import gcd, prod
from pathlib import Path
import argparse
import json
import runpy

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


def extra_five_guard():
    """Actual finite auxiliary support and the inherited shared-scalar consumer."""
    helper = Path(__file__).resolve().parents[1] / 'prefix-free-later-four-shearer' / 'mixed_tower_inventory.py'
    inherited = runpy.run_path(str(helper))
    support_polynomials = inherited['support_polynomials']
    query_numerator = inherited['query_numerator']
    other_weights = tuple(F(1, p-2) for p in Q[1:])

    def evaluate(t, positive=True):
        weights = (t,) + other_weights
        rho, _, _ = support_polynomials('extra_five_guard', weights, positive)
        return rho, query_numerator(rho, weights)

    rho0, n0 = evaluate(F(0), False)
    rho1, n1 = evaluate(F(1), False)
    target = F(37, 12)
    gap0 = target*rho0[-1]-n0
    slope = target*(rho1[-1]-rho0[-1])-(n1-n0)
    threshold = -gap0/slope
    require(gap0 == F(35597719,31808700) and slope == -F(81525298,31808700),
            'same-weight affine numerator gap')
    require(threshold == F(35597719,81525298), 'shared scalar threshold')
    rho_star, n_star = evaluate(threshold)
    require(target*rho_star[-1] == n_star, 'threshold equality')
    profiles = []
    for name, t, first5, higher_density, expected_rho, expected_bound, expected_max in (
        ('normalized_haar', F(5,11), F(4,11), F(20,11), F(489631,883575),
         F(51157586,16157823), F(9088732,16157823)),
        ('balanced_roots', F(4,9), F(1,3), F(20,9), F(2676139,4771305),
         F(41733953,13380695), F(6816549,13380695))):
        require(t == first5+higher_density*F(1,25)/(1-F(1,5)) and
                first5 >= higher_density/25, 'one-law cap total and monotone depth bounds')
        rho, numerator = evaluate(t)
        require(rho[-1] == expected_rho and numerator/rho[-1] == expected_bound > target,
                'positive polynomial but insufficient shared scalar bound')
        require(target*rho[-1]-numerator == gap0+slope*t,
                'profile matches inherited affine gap')
        first = (first5,) + tuple(F(p-1,p*(p-2)) for p in Q[1:])
        full = len(rho)-1
        caps = [prod((first[i] for i in range(len(Q)) if mask >> i & 1), start=F(1))
                * rho[full ^ mask]/rho[full] for mask in range(1, full+1)]
        require(len(caps) == 127 and max(caps) == caps[0] == expected_max < 1,
                'every nonempty first-depth query bound is already below one')
        profiles.append(dict(name=name,shared_weight=str(t),first_depth_cap=str(first5),
                             higher_depth_density=str(higher_density),rho=str(rho[-1]),
                             complete_query_upper=str(expected_bound),
                             gap_to_target=str(target-expected_bound),
                             nonempty_supports=len(caps),maximum_query_cap=str(max(caps)),
                             maximum_label=5,clipping_improvement='0'))

    forbidden = ((0,5),(1,5),(2,25),(7,125),(32,625))
    require(all((a-b) % gcd(m,n) for i,(a,m) in enumerate(forbidden)
                for b,n in forbidden[:i]), 'five auxiliary holes are pairwise disjoint')
    survivors = {n for n in range(625) if all(n % m != a for a,m in forbidden)}
    require({n % 5 for n in survivors} == {2,3,4}, 'three actual remaining first roots')
    root2 = {n for n in survivors if n % 5 == 2}
    counts = []
    for m, expected in ((25,4),(125,19),(625,94)):
        prefixes = {r for r in range(m) if r % 5 == 2 and
                    all(r % h != a for a,h in forbidden if h <= m)}
        require(prefixes == {n % m for n in root2} and len(prefixes) == expected,
                'actual root-two projection count')
        counts.append(dict(modulus=m,admissible_prefixes=len(prefixes)))
    reciprocal_sum = sum((F(1,row['admissible_prefixes']) for row in counts), F(0))
    coefficient = 1-2*reciprocal_sum
    lower = reciprocal_sum+coefficient/3
    require(reciprocal_sum == F(1119,3572) and coefficient == F(667,1786) > 0,
            'same-source pigeonhole coefficient')
    require(lower == F(4691,10716) and lower-threshold == F(485008057,436812546684) > 0,
            'finite four-layer lower bound exceeds required scalar')
    actual = ((2,3),(0,5),(6,15),(1,45),(2,25),(7,125),(32,625))
    require(len({m for _,m in actual}) == 7 and all(m > 1 and m % 2 for _,m in actual),
            'actual seven distinct odd numerical labels')
    require(actual[2][0] % 3 == 0 and actual[3][0] % 3 == 1 and
            actual[2][0] % 5 == actual[3][0] % 5 == 1,
            'both available ternary roots carry the same low five projection')
    free_leaves = sorted({n % 9 for n in range(45) if n % 3 == 1 and n % 5 == 1 and n != 1})
    require(free_leaves == [4,7], 'modulus45 blocks only one leaf inside root one')
    return dict(shared_scalar_target=str(target),gap_intercept=str(gap0),
                gap_slope=str(slope),weight_threshold=str(threshold),profiles=profiles,
                auxiliary_forbidden=[dict(residue=a,modulus=m) for a,m in forbidden],
                finite_period=625,survivor_count=len(survivors),root_two_counts=counts,
                reciprocal_sum=str(reciprocal_sum),root_max_coefficient=str(coefficient),
                four_layer_lower=str(lower),gap_above_threshold=str(lower-threshold),
                actual_originals=[dict(residue=a,modulus=m) for a,m in actual],
                unblocked_depth_two_phases=free_leaves,
                scope='The auxiliary support has two forbidden modulus5 phases. '
                      'The actual originals have distinct moduli. The obstruction excludes only '
                      'this inherited clique consumer with the same event/query scalar; '
                      'it does not exclude full-profile consumers, separate weights or joint sources.')


def active_leaf_bridge(beta, fg7):
    """Conditional depth-two consumer and actual common-prefix method controls."""
    require(1 <= beta < F(37,13) < 4, 'leaf cofactor source and positive reserve')
    reserve = 1-(beta-1)/3
    bound = 1+(4*beta-1)/reserve
    require(bound == (1+11*beta)/(4-beta) == F(10209527,448946) < 28,
            'one-law leaf budget includes the unit exactly once')
    require(reserve == F(2244730,5049311), 'leaf reserve')

    def inventory(originals, h, cut):
        rows = []
        for r in range(3**h):
            phases, legal = {}, True
            for row in originals:
                a, m = row['residue'], row['modulus']
                n, j = m, 0
                while n % 3 == 0:
                    n, j = n//3, j+1
                active = (a-r) % gcd(m,3**h) == 0
                period = m*3**h//gcd(m,3**h)
                require(active == any(x % m == a % m and x % (3**h) == r
                                      for x in range(period)),
                        'CRT activity agrees with an actual common integer')
                if n == 1 and j <= h and active:
                    legal = False
                elif n > 1 and j <= cut and active:
                    phases.setdefault(n,set()).add(a % n)
            if legal:
                rows.append(dict(prefix=r,modulus=3**h,
                                 phases=[dict(cofactor=n,residues=sorted(values))
                                         for n,values in sorted(phases.items())],
                                 single_phase=all(len(values) <= 1 for values in phases.values())))
        return rows

    roots = inventory(fg7,1,2)
    leaves = inventory(fg7,2,3)
    require([row['prefix'] for row in roots] == [0,1] and
            not any(row['single_phase'] for row in roots), 'FG7 fails both root contracts')
    passed = [row for row in leaves if row['single_phase']]
    require([row['prefix'] for row in passed] == [4,7], 'FG7 passes exactly two legal leaves')
    merged = [dict(cofactor=n,residues=[a]) for a,n in ((0,5),(2,25),(7,125),(32,625))]
    require(all(row['phases'] == merged for row in passed), 'complete numerical cofactor phases')

    actual = [dict(residue=a,modulus=m) for a,m in ((2,3),(0,5),(6,15),(0,7),(1,21))]
    private = [2,10,6,7,1]
    require(len({row['modulus'] for row in actual}) == 5 and
            all(row['modulus'] > 1 and row['modulus'] % 2 for row in actual),
            'five actual distinct odd nonunit labels')
    require(all([j for j,row in enumerate(actual) if x % row['modulus'] == row['residue']] == [i]
                for i,x in enumerate(private)), 'each actual class has a private integer')
    conflicts = inventory(actual,2,3)
    require([row['prefix'] for row in conflicts] == [0,1,3,4,6,7] and
            not any(row['single_phase'] for row in conflicts), 'all six legal leaf conflicts')
    for row in conflicts:
        n = 5 if row['prefix'] % 3 == 0 else 7
        require(dict((item['cofactor'],item['residues']) for item in row['phases'])[n] == [0,1],
                'conflict occurs already at ternary depth one')
    support = [x for x in range(105) if x % 3 == 0 and x % 5 == 2 and x % 7 != 0]
    require(support == [12,27,57,72,87,102] and
            all(all(x % row['modulus'] != row['residue'] for row in actual) for x in support),
            'one cheap product source avoids all five originals, including escape12')
    cheap = F(5,2)*F(9,4)*F(43,36)*prod((F(p,p-1) for p in Q[2:]), start=F(1))
    require(cheap == F(4152811,442368) < 28, 'complete cheap-source geometric query sum')
    return dict(cofactor_source='Report563 MT11',beta_upper=str(beta),
                pure_ternary_query_upper='4',low_null_through_height=3,
                arbitrary_mixed_from_height=4,reserve_lower=str(reserve),
                complete_query_upper=str(bound),margin_to_28=str(28-bound),
                source_threshold_for_28='37/13',
                fg7_roots=roots,fg7_leaves=leaves,
                common_prefix_obstruction=dict(
                    actual_originals=actual,private_witnesses=private,
                    finite_control_depth=2,legal_leaf_conflicts=conflicts,
                    product_support_mod105=support,escape_integer=12,
                    complete_query_norm=str(cheap),
                    scope='The finite control checks actual leaf intersections. '
                          'The all-depth argument uses persistent depth-one conflicts, '
                          'not finite enumeration. The obstruction concerns a single-phase '
                          'common-prefix supplier, not arbitrary joint survivor laws.'),
                scope='A selected mod9 leaf avoids actual pure3 and pure9 originals. '
                      'For each complete nonunit Q cofactor, all active phases at j=0,1,2,3 '
                      'must agree. Mixed originals at j>=4 and higher pure ternary originals '
                      'are unrestricted. One fixed source and one final conditioning '
                      'supply the all-height bound in Report529; this consumer is not a Lean proof.')


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
    guard = extra_five_guard()
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
                extra_five_guard=guard,
                active_leaf_extension=active_leaf_bridge(active_beta,guard['actual_originals']),
                scope='Exact finite controls for the relative-reserve, low-projection and auxiliary-root strategies; '
                      'these do not obstruct existence of a different supported source with complete B<28. '
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
