#!/usr/bin/env python3
"""Exact joint-private budget after releasing every pure-3 transport modulus.

The literal HSW source retains all original heights 1..22. Every numerical
3**e, e>=2, is freely reassignable, at most one whole-source-sound AP per
modulus. Mixed standard numerical candidates remain reserved. Additional
moduli may have arbitrary heights on P0. This is not general noncoverage.

Two algorithms reconstruct the joint private masks from the literal
constructor: row-predicate evaluation and Cartesian rectangle marking.
The final target retains |M|>=3 without renormalizing Haar measure; the
unfiltered target and its exact thresholds remain a parallel case.
Finite digit checks illustrate the general AP-containment criterion; the
unbounded-exponent statement is the elementary congruence argument in 353.
Only exact Fraction comparisons decide the reported inequalities.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import gcd, prod
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
P0 = (3, 5, 7, 11, 13, 17, 19, 23)
COFACTORS = (5, 7, 13, 17, 19)
HEIGHT = 22
EXPECTED_MASKS = {0:48186, 1:1159, 3:876, 5:5078, 7:2180,
                  9:1837, 11:2886, 13:8840, 15:11902}


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def positive_int(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(name + ' must be a positive integer')


def load_constructor():
    path = Path(__file__).resolve().with_name('hsw11_family.py')
    spec = importlib.util.spec_from_file_location('literal_hsw_pure3_source', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_family(family):
    require(family['nonpure_roots'] == [0,1,2,3], 'source roots changed')
    source = [r for r in family['normal_families'] if r['primes'] == [3]]
    require(len(source) == 1 and source[0]['digits'] == {'3':1},
            'the A_t family is not the unique pure-3 digit-1 family')
    for row in family['normal_families']:
        require(set(row['primes']) <= set(P0) and 23 not in row['primes'],
                'normal prime support changed')
        require(all(row['exponent_ranges'][str(p)] ==
                    ([1,1] if p == 11 else [1,HEIGHT]) for p in row['primes']),
                'original height box changed')
        if 3 in row['primes'] and row['primes'] != [3]:
            require(row['digits']['3'] == 2,
                    'another 3-bearing family can meet an A_t')
    closing = family['closing_families']
    require(len(closing) == 6 and {r['prime'] for r in closing} == {3,*COFACTORS},
            'closing support changed')
    require(all(r['exponent_range'] == [1,HEIGHT] and r['p_residue'] == 0
                and r['q_residue'] == 'j' and r['modulus'] == '23*p^j'
                for r in closing), 'closing source labels changed')
    require(family['shared_closing_class'] == [0,23], 'shared closing changed')
    return source[0]['id']


def masks_by_predicates(family):
    patterns = []
    for root in range(4):
        patterns.append([
            tuple((COFACTORS.index(p), row['digits'][str(p)])
                  for p in row['primes'] if p != 11)
            for row in family['normal_families']
            if 3 not in row['primes'] and
               (11 not in row['primes'] or row['digits']['11'] == root)])
    masks = bytearray()
    for digits in product(*(range(1,p) for p in COFACTORS)):
        mask = sum((not any(all(digits[k] == digit for k,digit in pattern)
                            for pattern in patterns[root])) << root
                   for root in range(4))
        masks.append(mask)
    return masks


def masks_by_rectangles(family):
    size = prod(p-1 for p in COFACTORS)
    covered = [bytearray(size) for _ in range(4)]
    for row in family['normal_families']:
        support = set(row['primes'])
        if 3 in support:
            continue
        roots = ([row['digits']['11']] if 11 in support else range(4))
        roots = [r for r in roots if r < 4]
        if not roots:
            continue
        axes = [(row['digits'][str(p)],) if p in support else range(1,p)
                for p in COFACTORS]
        for digits in product(*axes):
            offset = 0
            for p,digit in zip(COFACTORS,digits):
                offset = offset*(p-1)+digit-1
            for root in roots:
                covered[root][offset] = 1
    return bytearray(sum((not covered[root][i]) << root for root in range(4))
                     for i in range(size))


def local_bounds(mask):
    """All local root injections; no independently optimized source marginals."""
    if type(mask) is not int or not 0 <= mask < 16:
        raise ValueError('mask must encode a subset of four roots')
    counts = []
    one_new_root_max = 0
    for selected in combinations(range(4),3):
        for old_by_new in permutations(selected):
            bits = [bool(mask & (1 << old_by_new[b])) for b in range(3)]
            counts.append(sum(bits))
            one_new_root_max = max(one_new_root_max, int(bits[0]))
    lower = min(counts)
    require(lower == max(mask.bit_count()-1,0), 'three-root lower formula failed')
    require(one_new_root_max == int(mask != 0), 'one-AP root upper formula failed')
    return lower, one_new_root_max


def g(p, height):
    positive_int(p, 'base')
    positive_int(height, 'height')
    if p == 1:
        raise ValueError('base must exceed one')
    return (1-F(1,p**height))/(p-1)


def height_masses():
    terms = {j:prod((g(p,j) for p in COFACTORS),start=F(1))/23
             for j in range(1,HEIGHT+1)}
    masses = {t:sum((terms[j] for j in range(t,HEIGHT+1)),F(0))
              for t in range(1,HEIGHT+1)}
    # Separate direct finite sums check the closed geometric formula.
    direct = {j:prod((sum((F(1,p**h) for h in range(1,j+1)),F(0))
                     for p in COFACTORS),start=F(1))/23
              for j in range(1,HEIGHT+1)}
    require(terms == direct, 'height aggregation algorithms disagree')
    require(all(masses[t] > masses[t+1] > 0 for t in range(1,HEIGHT)),
            'K_t is not strictly decreasing and positive')
    return masses


def source_height_for_pure_ap(residue, exponent):
    """The only A_t that can contain this entire pure-3 AP, or None.

    Memory is old3=floor(output3/3). For exponent e>=1, the AP fixes
    old3 modulo 3**(e-1). The first nonzero old digit must be 1 and occur
    within these fixed digits. The source retains only t<=22.
    """
    if type(residue) is not int:
        raise ValueError('residue must be an integer')
    positive_int(exponent, 'exponent')
    old = (residue % (3**exponent))//3
    t = 1
    while old and old % 3 == 0:
        old //= 3
        t += 1
    return t if old % 3 == 1 and t <= HEIGHT else None


def pure_ap_private_bound(residue, exponent, masses, nonempty_count):
    t = source_height_for_pure_ap(residue,exponent)
    if t is None:
        return F(0)
    require(t+1 <= exponent, 'sound pure AP fails e>=t+1')
    return nonempty_count*masses[t]/3**exponent


def finite_containment_checks():
    checked = 0
    for t in range(1,5):
        period = 3**(t+1)
        target = {3**t+b for b in range(3)}
        for modulus in (1,3,9,27,81,243,5,15,45,135,405):
            step = gcd(modulus,period)
            for residue in range(step):
                image = set(range(residue,period,step))
                contained = image <= target
                criterion = modulus % period == 0 and residue in target
                require(contained == criterion, 'AP containment congruence failed')
                checked += 1
        # Pure-AP API checks at higher precision, by all periodic residues.
        for exponent in range(1,7):
            for residue in range(3**exponent):
                step = gcd(3**exponent,period)
                actual = set(range(residue % step,period,step)) <= target
                require(actual == (source_height_for_pure_ap(residue,exponent) == t),
                        'source-height API does not match literal containment')
    # Disjoint A_t pullbacks, including every original endpoint.
    for t in range(1,HEIGHT+1):
        for b in range(3):
            require(source_height_for_pure_ap(3**t+b,t+1) == t,
                    'original-height endpoint omitted')
            for s in range(1,t):
                require((3**t+b)//3 % (3**s) != 3**(s-1),
                        'two source height strata overlap')
    return checked


def reserved_capacity(family):
    shapes = {tuple(p for p in row['primes'] if p != 11)
              for row in family['normal_families'] if 3 in row['primes']}
    expected = {(3,)+tuple(p for p,bit in zip((5,7,19),bits) if bit)+tail
                for bits in product((0,1),repeat=3) for tail in ((),(13,),(17,))}
    require({tuple(sorted(s)) for s in shapes} ==
            {tuple(sorted(s)) for s in expected}, 'merged standard supports changed')
    qsum = g(3,HEIGHT)/3
    normal = qsum*sum((prod((g(p,HEIGHT) for p in s if p != 3),start=F(1))
                       for s in shapes),F(0))
    factored = qsum*(1+g(5,HEIGHT))*(1+g(7,HEIGHT))*(1+g(19,HEIGHT))*\
                     (1+g(13,HEIGHT)+g(17,HEIGHT))
    require(normal == factored, 'standard-pool polynomial check failed')
    reserved = normal+qsum/23
    euler = prod((F(p,p-1) for p in P0 if p != 3),start=F(1))/6
    require(euler == F(676039,1990656), 'supported Euler mass changed')
    # Explicit small complete numerical boxes check deduplication.
    for height in (1,2,3):
        actual = set()
        for row in family['normal_families']:
            if 3 not in row['primes']:
                continue
            support = [p for p in row['primes'] if p != 11]
            for exponents in product(range(1,height+1),repeat=len(support)):
                actual.add(3*prod(p**e for p,e in zip(support,exponents)))
        symbolic = {3*prod(p**e for p,e in zip(s,exponents))
                    for s in shapes
                    for exponents in product(range(1,height+1),repeat=len(s))}
        require(actual == symbolic, 'literal numerical candidate union failed')
    count = sum(HEIGHT**len(s) for s in shapes)+HEIGHT
    require(count == 12045352, 'standard-pool count changed')
    return reserved,euler,euler-reserved,count


def literal_boundary_checks(constructor, family, source_id):
    # These first-nonzero digits have private mask 15. Vary all A_t and
    # closing residues; literal active labels check the j>=t endpoint.
    digits = dict(zip(COFACTORS,(2,2,2,2,1)))
    checked = 0
    for t in range(1,HEIGHT+1):
        for j in range(23):
            for root in range(4):
                coords = {3:3**(t-1),11:root,23:j,**digits}
                active = constructor.active_classes(coords,family)
                sole = len(active) == 1 and active[0]['family'] == source_id
                require(sole == (j >= t), 'literal closing boundary changed')
                checked += 1
    # The terminal all-zero cofactor is not an uncounted private tail.
    for p in COFACTORS:
        for j in range(1,23):
            coords = {3:1,11:0,23:j,**digits,p:0}
            active = constructor.active_classes(coords,family)
            require(any(row['family'] == 'closing-'+str(p) for row in active),
                    'all-zero cofactor tail escaped closing')
            checked += 1
    return checked


def five_swap_example(masses, vacant):
    # Fixed map: old2 -> new0, old3 -> new1, old1 -> new2.
    # Keep 3 mod9 for A1. Reassign exponents3..7 from A_(e-1) to A1.
    swaps = []
    for exponent in range(3,8):
        former = 1+3**(exponent-1)
        new = 4+3**(exponent-1)
        require(source_height_for_pure_ap(former,exponent) == exponent-1,
                'former source label of swap changed')
        require(source_height_for_pure_ap(new,exponent) == 1,
                'new AP is not wholly sound for A1')
        swaps.append((exponent,former,new))
    for (e,_,a),(f,_,b) in combinations(swaps,2):
        require((a-b) % 3**min(e,f) != 0, 'new swap APs overlap')
    initial = F(43309,9)*masses[1]
    gain = 25465*masses[1]*sum((F(1,3**e) for e,_,_ in swaps),F(0))
    loss = 25465*sum((masses[e-1]/3**e for e,_,_ in swaps),F(0))
    remaining = initial-gain
    require(remaining < vacant, 'five swaps do not break the singleton capacity cut')
    require(initial-25465*masses[1]*sum((F(1,3**e) for e in range(3,7)),F(0))
            > vacant, 'four-swap predecessor already passes the singleton cut')
    require(remaining+loss-vacant > F(3,200), 'old-label losses were not charged')
    return dict(swaps=[dict(modulus=3**e,former_residue=a,new_residue=b,
                           former_source_height=e-1) for e,a,b in swaps],
                remaining_A1=str(remaining),lost_former_sources=str(loss),
                joint_unfulfilled_minus_vacant=str(remaining+loss-vacant))


def bracket(value,digits=18):
    scale = 10**digits
    lower = value.numerator*scale//value.denominator
    return dict(lower_numerator=lower,upper_numerator=lower+1,denominator=scale)


def result():
    constructor = load_constructor()
    family = constructor.build_family()
    source_id = validate_family(family)
    masks = masks_by_predicates(family)
    require(masks == masks_by_rectangles(family), 'two joint mask algorithms disagree')
    histogram = Counter(masks)
    require(dict(sorted(histogram.items())) == EXPECTED_MASKS,
            'literal private-mask fixture changed')
    require(len(masks) == 82944, 'incomplete digit space')
    demand_count = 0
    eligible_count = 0
    for mask,count in histogram.items():
        lower,upper = local_bounds(mask)
        demand_count += count*lower
        eligible_count += count*upper
    require((demand_count,eligible_count) == (71309,34758), 'local budget totals changed')
    masses = height_masses()
    demand = demand_count*sum((masses[t]/3**(t+1) for t in range(1,HEIGHT+1)),F(0))
    # Swap finite sums independently: every closing j permits source t<=j.
    demand_alt = demand_count*sum((prod((g(p,j) for p in COFACTORS),start=F(1))/23*
                                  sum((F(1,3**(t+1)) for t in range(1,j+1)),F(0))
                                  for j in range(1,HEIGHT+1)),F(0))
    require(demand == demand_alt, 'joint source/closing sum orders disagree')
    pure_capacity = eligible_count*masses[1]/6  # sum_(e>=2)3^-e = 1/6
    for cutoff in (2,3,22,23,40):
        require(sum((F(1,3**e) for e in range(2,cutoff+1)),F(0))+
                F(1,2*3**cutoff) == F(1,6), 'unbounded pure-power tail failed')
    reserved,euler,vacant,pool_count = reserved_capacity(family)
    gap = demand-pure_capacity-vacant
    require(demand > F(131654,10**6) and pure_capacity < F(65225,10**6)
            and vacant < F(38387,10**6), 'displayed outward budget inequalities failed')
    require(F(131654-65225-38387,10**6) > F(1,40), 'coarse gap threshold failed')
    require(gap > F(1,40), 'pure-3 reallocation exclusion failed')
    threshold = (demand-pure_capacity+reserved)/euler
    require(F(899,840) < threshold < F(33263,30240),
            'two-versus-three fresh-prime threshold failed')
    two_fresh_vacant = euler*F(899,840)-reserved
    two_fresh_gap = demand-pure_capacity-two_fresh_vacant
    require(two_fresh_gap > F(1,240), 'two-fresh-prime uniform hole bound failed')
    containment_count = finite_containment_checks()
    literal_count = literal_boundary_checks(constructor,family,source_id)
    swaps = five_swap_example(masses,vacant)
    # Check the API at every original height and representative higher precision.
    for t in range(1,HEIGHT+1):
        for e in (t+1,t+2,t+25):
            bound = pure_ap_private_bound(3**t+1,e,masses,eligible_count)
            require(bound == eligible_count*masses[t]/3**e <=
                    eligible_count*masses[1]/3**e, 'pure-AP capacity API failed')
    numbers = dict(joint_private_demand=demand,all_pure3_private_capacity=pure_capacity,
                   reserved_pool_reciprocal_mass=reserved,
                   all_supported_reciprocal_mass=euler,vacant_capacity=vacant,
                   strict_hole_lower=gap,necessary_fresh_euler_threshold=threshold,
                   maximum_two_fresh_vacant=two_fresh_vacant,
                   strict_two_fresh_hole_lower=two_fresh_gap)
    # Restrict the SAME cofactor probability space to |M|>=3. Every
    # retained private source obligation and AP intersection carries
    # this same indicator. Keep the complete all-mask case above.
    cut_demand_count = 0
    cut_eligible_count = 0
    for mask,count in histogram.items():
        if mask.bit_count() >= 3:
            lower,upper = local_bounds(mask)
            cut_demand_count += count*lower
            cut_eligible_count += count*upper
    require((cut_demand_count,cut_eligible_count) == (63518,25808),
            'three-private-root cut counts changed')
    cut_demand = cut_demand_count*sum((masses[t]/3**(t+1)
                                      for t in range(1,HEIGHT+1)),F(0))
    cut_pure_capacity = cut_eligible_count*masses[1]/6
    cut_gap = cut_demand-cut_pure_capacity-vacant
    cut_two_fresh_gap = cut_demand-cut_pure_capacity-two_fresh_vacant
    cut_threshold = (cut_demand-cut_pure_capacity+reserved)/euler
    require(cut_demand*demand_count == demand*cut_demand_count,
            'filtered source/closing sum differs from its parallel all-mask case')
    require(cut_demand > F(117270,10**6) and cut_pure_capacity < F(48430,10**6),
            'filtered outward budget inequalities failed')
    require(F(117270-48430-38387,10**6) > F(3,100),
            'filtered coarse gap threshold failed')
    require(cut_gap > F(3,100) and cut_two_fresh_gap > F(1,160),
            'three-private-root cut gap failed')
    require(cut_gap > gap and cut_two_fresh_gap > two_fresh_gap,
            'filtered cut does not strengthen the unchanged all-mask case')
    require(F(899,840) < cut_threshold < F(33263,30240),
            'filtered two-versus-three fresh-prime threshold failed')
    for t in range(1,HEIGHT+1):
        for e in (t+1,t+2,t+25):
            bound = pure_ap_private_bound(3**t+1,e,masses,cut_eligible_count)
            require(bound == cut_eligible_count*masses[t]/3**e <=
                    cut_eligible_count*masses[1]/3**e,
                    'filtered pure-AP capacity API failed')
    cut_numbers = {**numbers,
                   'joint_private_demand':cut_demand,
                   'all_pure3_private_capacity':cut_pure_capacity,
                   'strict_hole_lower':cut_gap,
                   'strict_two_fresh_hole_lower':cut_two_fresh_gap,
                   'necessary_fresh_euler_threshold':cut_threshold}
    return dict(success=True,source_label_family=source_id,source_heights=[1,HEIGHT],
                joint_private_masks=dict(sorted(histogram.items())),
                digit_tuples=len(masks),mask_algorithms=['row-predicates','rectangle-marking'],
                target_cofactor_cut='at least three private old roots: |M|>=3',
                retained_private_count=cut_demand_count,
                one_pure_AP_eligible_count=cut_eligible_count,
                reserved_numerical_candidate_count=pool_count,
                finite_AP_containment_checks=containment_count,
                literal_closing_endpoint_checks=literal_count,
                all_pure3_exponents_allowed='every e>=2; exact geometric tail',
                exact={k:str(v) for k,v in cut_numbers.items()},
                rational_brackets={k:bracket(v) for k,v in cut_numbers.items()},
                parallel_cases={
                    'all_masks':dict(retained_private_count=demand_count,
                        one_pure_AP_eligible_count=eligible_count,
                        exact={k:str(v) for k,v in numbers.items()},
                        rational_brackets={k:bracket(v) for k,v in numbers.items()},
                        certified_global_hole_lower='1/40',
                        certified_at_most_two_fresh_hole_lower='1/240')},
                all_source_height_masses={str(t):str(masses[t]) for t in masses},
                certified_global_hole_lower='3/100',
                certified_at_most_two_fresh_hole_lower='1/160',
                five_swap_example=swaps,
                scope='All pure-3 numerical moduli may be reassigned at arbitrary heights. Mixed standard candidates remain reserved for descendants of all 22 A_t sources, whose moduli share support P0 union F at arbitrary heights. The final restricted target proves hole mass >3/100 for F empty and >1/160 for at most two fresh odd primes. Adaptive three-of-four root injections use one common CRT source. This does not exclude mixed-pool reallocation, larger fresh-prime extensions passing only the budget test, different memory maps, or general odd covers.')


if __name__ == '__main__':
    print(json.dumps(result(),sort_keys=True,indent=2))
