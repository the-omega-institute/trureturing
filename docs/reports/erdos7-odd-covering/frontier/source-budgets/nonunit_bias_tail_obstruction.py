#!/usr/bin/env python3
"""Exact actual-support obstruction to one complete-tail cylinder-bias gate."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations, product
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import sys
sys.dont_write_bytecode = True
PROOF = 'profile-notes/321-384/346-old-cylinder-tree-gluing-and-source-corrections.md'
CERTIFICATE = 'certificates/source_norms/source-budgets/nonunit_bias_tail_obstruction.json'
SOURCE = 'certificates/source_norms/source-budgets/source_mean_sharpness.json'
FLOORS = 'frontier/source-budgets/nonunit_tail_floors.json'
PERSISTENT_FLOORS = 'frontier/source-budgets/nonunit_persistent_floors.json'
SOURCES = (SOURCE, FLOORS, PERSISTENT_FLOORS, 'certificate_io.py',
           'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md',
           'profile-notes/321-384/339-irredundant-source-seven-labels-bound-the-actual-surplus.md')
EXTRA = (11, 13, 17, 19, 23, 29, 31, 37)
FUTURE = (41, 43, 47, 53, 59, 61, 67, 71, 73)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def pure_count(p, h):
    value = p**h - sum(p**(h-a) for a in range(1, h+1))
    require(value == F((p-2)*p**h+1, p-1) > 0, 'Exact positive pure-prefix count')
    return value


def schedule_coefficients(clips):
    U = V = F(1)
    L0 = L1 = L3 = F(0)
    for p, delta in zip(FUTURE, clips):
        require(0 < delta < 1, 'Declared clipping domain')
        h = 1/(4*(p-2)**2*delta*(1-delta))
        L0 += h
        L1 += h*U
        L3 += h*V
        u = 1+1/((p-2)*(1-delta))
        v = 1+F(3*p-1, (p-2)*(p-1))/(1-delta)
        require(v >= u > 1, 'Pointwise product-coefficient ordering')
        U *= u
        V *= v
    require(L3 >= L1 > 0, 'Nonunit affine coefficients have the correct sign')
    return dict(U=U, V=V, L0=L0, L1=L1, L3=L3)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def floor_input(io, base, path, schema):
    fixed = json.loads(io.read_artifact_bytes(base/path), object_pairs_hook=io._unique)
    require(set(fixed) == {'schema', 'scale', 'output_floor_units'}
            and fixed['schema'] == schema
            and type(fixed['scale']) is int and fixed['scale'] == 10000,
            'Declared fixed floor input format')
    units = fixed['output_floor_units']
    require(isinstance(units, list) and all(type(n) is int and n > 0 for n in units),
            'Positive exact grid integers')
    return fixed['scale'], units


def later_tail(io, base, initial_floor):
    """Verify fixed rational floors, never generate or optimize them."""
    scale, units = floor_input(io, base, FLOORS, 'nonunit-unrefunded-tail-floor-input-v1')
    endpoint = 38851
    primes = [p for p in range(FUTURE[-1]+1, endpoint) if prime(p)]
    require(prime(endpoint) and len(primes) == len(units) == 4071
            and primes[0] == 79 and primes[-1] == 38839
            and initial_floor == F(7129, 50), 'Every consecutive prime and inherited seed')
    f, minimum, minimum_prime, digest = initial_floor, None, None, sha256()
    for p, n in zip(primes, units):
        k = F(n, scale)
        a, b = F(3*p-1, (p-1)**2), F(1, 4*(p-1)**2)
        qa, qb, qc = k-f, f*(1+a)-k, k*b*f
        gap = 4*qa*qc-qb*qb
        require(k > f >= 1 and gap > 0
                and qc == qb*qb/(4*qa)+gap/(4*qa), 'Every later all-real quadratic is positive')
        digest.update((json.dumps(encode((p, f, k, qa, qb, qc, gap)), separators=(',', ':'))+'\n').encode())
        if minimum is None or gap < minimum:
            minimum, minimum_prime = gap, p
        f = k
    capacity = F((endpoint-1)**2)
    require(f > capacity, 'Carried floor exceeds every legal next-denominator capacity')
    return dict(input=FLOORS, seed_prime=73, seed_strict_floor=initial_floor,
        verified_quadratic_rows=len(primes), first_prime=primes[0], last_certified_prime=primes[-1],
        reconstructed_rows_sha256=digest.hexdigest(), minimum_discriminant_margin=minimum,
        minimum_margin_prime=minimum_prime, failure_prime=endpoint,
        carried_strict_floor=f, strict_capacity=capacity, floor_exceeds_capacity_by=f-capacity,
        scope='For each actual source law, positivity of the same nonunit affine coefficients transfers the surrogate seed to its assigned ratio. Condition once at73 with that assigned bound, then use unrefunded full-tail T6 at every prime. Every legal adaptive 0<delta<1 schedule stops by38851. This is not an actual moment or survivor-mass lower bound; further nonunit corrections, sharper actual-law bounds, another law or recurrence, and finite-inventory pricing are not excluded.')


def persistent_tail(io, base, A, B):
    """Keep the nonunit correction, with rigorous directed product bounds."""
    scale, units = floor_input(io, base, PERSISTENT_FLOORS, 'nonunit-persistent-tail-floor-input-v1')
    grid, endpoint = 10**12, 63997
    require(A > F(3, 4) and B > 2*A, 'Same-source hypotheses for historical-control monotonicity')
    def ceiling(value):
        return -(-value.numerator//value.denominator)
    def flooring(value):
        return value.numerator//value.denominator
    X, Y, f = ceiling(grid*A), flooring(grid*B), F(flooring(scale*B), scale)
    require(F(X-1, grid) < A <= F(X, grid) and F(Y, grid) <= B < F(Y+1, grid)
            and 0 < f < B, 'Initial directed product bounds and strict scalar floor')
    initial = dict(X_upper_grid=X, Y_lower_grid=Y, F_lower_grid=int(scale*f))
    primes = [p for p in range(FUTURE[0], endpoint) if prime(p)]
    require(prime(endpoint) and len(primes) == len(units) == 6400
            and primes[0] == 41 and primes[-1] == 63977, 'Complete persistent-correction prime sequence')
    minimum, minimum_prime, digest = None, None, sha256()
    for p, n in zip(primes, units):
        require(Y > 0 and 2*X-grid > 0, 'Directed ratio denominator and numerator signs')
        q, k = 1-F(2*X-grid, Y), F(n, scale)
        require(0 < q < 1, 'Conservative positive nonunit ratio')
        a, b, c = F(3*p-1, (p-2)*(p-1)), F(1, 4*(p-2)**2), F(1, p-2)
        require(A > a/(2*(a-c)), 'Sufficient monotonicity in every historical control')
        qa, qb, qc = k-f, f*(1+a)-k, k*b*q*f
        gap = 4*qa*qc-qb*qb
        require(k > f > 0 and gap > 0 and qc == qb*qb/(4*qa)+gap/(4*qa),
                'Persistent full-tail all-real quadratic positivity')
        xnext, ynext = F(X*(p-1), p-2), F(Y*(p*p+1), (p-2)*(p-1))
        newX, newY = ceiling(xnext), flooring(ynext)
        require(newX-1 < xnext <= newX and newY <= ynext < newY+1,
                'Outward product rounding at each prime')
        digest.update((json.dumps(encode((p, X, Y, q, f, k, qa, qb, qc, gap, newX, newY)),
                                  separators=(',', ':'))+'\n').encode())
        if minimum is None or gap < minimum:
            minimum, minimum_prime = gap, p
        X, Y, f = newX, newY, k
    require(Y > 0 and 2*X-grid > 0, 'Endpoint directed signs')
    q, capacity = 1-F(2*X-grid, Y), (endpoint-2)**2
    require(0 < q < 1 and q*f > capacity, 'No threshold can keep the next surrogate budget positive')
    return dict(input=PERSISTENT_FLOORS, floor_scale=scale, product_grid=grid,
        initial=initial, verified_rows=len(primes), first_prime=primes[0], last_certified_prime=primes[-1],
        reconstructed_rows_sha256=digest.hexdigest(), minimum_discriminant_margin=minimum,
        minimum_margin_prime=minimum_prime,
        endpoint=dict(prime=endpoint, X_upper_grid=X, Y_lower_grid=Y, q_lower=q,
            F_lower=f, qF_lower=q*f, strict_capacity=capacity, gap=q*f-capacity),
        scope='Same initial actual-source law, same thresholds for actual-law and surrogate allocated payments, persistent nonunit correction and full exponent tails at every prime. Positive nonunit coefficients give actual-law allocated budget no larger than the surrogate. Every adaptive clipping schedule has nonpositive allocated budget by63997. This does not bound actual survival from above or exclude another law, joint estimates, finite heights or absent-label-aware prices.')


def calculate(base, proof):
    spec = importlib.util.spec_from_file_location('nonunit_io', base/'certificate_io.py')
    require(spec is not None and spec.loader is not None, 'Readable canonical certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    source = json.loads(io.read_artifact_bytes(base/SOURCE), object_pairs_hook=io._unique)
    old = next(row for row in source['results'] if row['height'] == 12)
    family, witnesses = old['original_classes'], old['private_integer_witnesses']
    N, old_period = 12, 105**12
    require(len(family) == len(witnesses) == 204 and old['private_membership_checks'] == 204**2,
            'Consume the published original-private certificate without rerunning it')
    require([w['original_index'] for w in witnesses] == list(range(204))
            and lcm(*(c['modulus'] for c in family)) == old_period,
            'Complete inherited labels, witnesses and old period')
    require(F(old['source']['delta']) < F(1, 4000) and F(old['source']['rho']) > F(3, 50)
            and F(old['source']['qJ']) + F(old['source']['delta']) == 1
            and F(old['source']['rho']) == F(old['source']['S']) - F(old['source']['S0'])
            and any(c['modulus'] == 7 for c in family), 'Actual unchanged357 source guard')
    hole = old['uncovered_integer']
    require(hole == 4 and old['uncovered_coordinates'] == [4, 4, 4], 'Published actual old hole')
    period = old_period*prod(EXTRA)
    def lift(value, residues):
        old_value = value % old_period
        value, modulus = old_value, old_period
        for p, r in zip(EXTRA, residues):
            require(gcd(modulus, p) == 1, 'Coprime actual CRT augmentation')
            value += modulus*(((r-value)*pow(modulus, -1, p)) % p)
            modulus *= p
        require(modulus == period and value % old_period == old_value
                and all(value % p == r for p, r in zip(EXTRA, residues)), 'Actual CRT coordinate lift')
        return value
    lifts = [dict(original_index=w['original_index'], old_integer=w['integer'],
                  lifted_integer=lift(w['integer'], (1,)*8)) for w in witnesses]
    new_private = [dict(modulus=p, residue=0, private_integer=lift(hole, tuple(int(q != p) for q in EXTRA)))
                   for p in EXTRA]
    new_hole = lift(hole, (1,)*8)
    moduli = [c['modulus'] for c in family]+list(EXTRA)
    require(len(moduli) == len(set(moduli)) == 212 and all(d > 1 and d % 2 for d in moduli),
            'Actual distinct odd augmented inventory')
    require(all(gcd(c['modulus'], p) == 1 for c in family for p in EXTRA), 'Old and added prime coordinates separate')
    pure, pair_checks, rectangle_checks = {}, 0, 0
    for index, p in enumerate((3, 5, 7)):
        rows = [c for c in family if c['exponents'][index] and sum(e > 0 for e in c['exponents']) == 1]
        require(sorted(c['exponents'][index] for c in rows) == list(range(1, N+1)), 'Every inherited pure depth')
        for c, d in combinations(rows, 2):
            require((c['residue']-d['residue']) % gcd(c['modulus'], d['modulus']) != 0,
                    'Disjoint original pure cylinders')
            pair_checks += 1
        pure[p] = rows
    original15 = next(c for c in family if c['modulus'] == 15)
    require(original15['coordinate_residues'] == [1, 2, 0], 'Literal original15 rectangle')
    for p, residue in ((3, 1), (5, 2)):
        for c in pure[p]:
            require((c['residue']-residue) % p != 0, 'Whole original15 rectangle misses every pure cylinder')
            rectangle_checks += 1
    counts = {p: [pure_count(p, h) for h in range(N+1)] for p in (3, 5, 7)}
    for p, values in counts.items():
        require(all(values[h+1] == p*values[h]-1 for h in range(N)), 'Independent pure-count recurrence')
    def count35(i, j):
        return counts[3][i]*counts[5][j]-(3**(i-1)*5**(j-1) if i and j else 0)
    small = []
    for i, j in product(range(4), repeat=2):
        total = 0
        for x, y in product(range(3**i), range(5**j)):
            if any(x % c['modulus'] == c['residue'] for c in pure[3] if c['modulus'] <= 3**i):
                continue
            if any(y % c['modulus'] == c['residue'] for c in pure[5] if c['modulus'] <= 5**j):
                continue
            if i and j and x % 3 == 1 and y % 5 == 2:
                continue
            total += 1
        require(total == count35(i, j), 'Independent complete small-prefix containing-set count')
        small.append(dict(exponents=(i, j), direct_count=total))
    grid = [dict(exponents=(i, j), support_upper=count35(i, j), omega=(2*i+1)*(2*j+1))
            for i, j in product(range(N+1), repeat=2)]
    require(all(row['support_upper'] > 0 for row in grid), 'Positive containing mixed-prefix counts')
    A35 = sum(F(1, row['support_upper']) for row in grid)
    B35 = sum(F(row['omega'], row['support_upper']) for row in grid)
    Arest = sum(F(1, x) for x in counts[7])*prod(1+F(1, p-1) for p in EXTRA)
    Brest = sum(F(2*k+1, x) for k, x in enumerate(counts[7]))*prod(1+F(3, p-1) for p in EXTRA)
    A, B = A35*Arest, B35*Brest
    require(B > 12*A and B > 54 and grid[0]['support_upper'] == 1, 'Same-table ratio and exact unit cap')
    target = F(138877, 1000)
    fixed = schedule_coefficients((F(1, 4),)*9)
    V, L0, L1, L3 = (fixed[k] for k in ('V', 'L0', 'L1', 'L3'))
    theta = 2*target*L1/(V+target*L3)
    limit = target*(1-L0)/(V+target*L3)
    require(0 < theta < 1 and limit > 0, 'Fixed-target positive coefficients')
    contributions = [(row['omega']*Brest-theta*Arest)/row['support_upper'] for row in grid]
    lower = B-theta*A
    require(min(contributions) > 0 and sum(contributions) == lower > limit,
            'One positive-coefficient objective, factored without incompatible extrema')
    example = schedule_coefficients((F(1, 10000),)+(F(1, 4),)*8)
    unit_coefficient = example['V']+target*example['L3']-2*target*example['L1']
    require(unit_coefficient < 0, 'Unit coefficient can be negative; retain c(1)=1 exactly')
    floors = ((41, F(54), F(6207, 100)), (43, F(6207, 100), F(7113, 100)),
              (47, F(7113, 100), F(8069, 100)), (53, F(8069, 100), F(451, 5)),
              (59, F(451, 5), F(9967, 100)), (61, F(9967, 100), F(110)),
              (67, F(110), F(12031, 100)), (71, F(12031, 100), F(6551, 50)),
              (73, F(6551, 50), F(7129, 50)))
    require(tuple(p for p, _, _ in floors) == FUTURE
            and list(FUTURE) == [p for p in range(41, 74) if all(p % d for d in range(2, p))],
            'All nine intervening prime stages included')
    q, carried, rows = F(5, 6), F(54), []
    for p, f, k in floors:
        a, b = F(3*p-1, (p-2)*(p-1)), F(1, 4*(p-2)**2)
        qa, qb, qc = k-f, f*(1+a)-k, k*b*q*f
        gap = 4*qa*qc-qb*qb
        require(f == carried and qa > 0 and gap > 0
                and qa*(qb/(2*qa))**2+gap/(4*qa) == qc, 'Linked all-real exact quadratic barrier')
        rows.append(dict(prime=p, input_floor=f, output_strict_floor=k, a=a, b=b,
                         quadratic=(qa, qb, qc), four_AC_minus_B_squared=gap))
        carried = k
    require(carried == F(7129, 50) and carried-target == F(3703, 1000) > 0, 'Final entry obstruction')
    raw_proof = io.read_artifact_bytes(proof)
    result = dict(schema='nonunit-bias-tail-obstruction-v2',
        scope='One actual irredundant 212-label noncover in the339 source guard. Every probability on its actual through37 survivors fails the declared complete-tail entry formula for every clipping schedule at all nine primes41..73. Two subsequent routes are separately bounded: one conditioning at73 then unrefunded full-tail T6 stops by38851; persistent nonunit full-tail allocation from41 has nonpositive budget by63997. Allocated expressions only; no actual survival or moment lower bounds and no exclusion of another law, new joint estimates or finite-height/missing-label-aware methods.',
        source_sha256={p: sha256(io.read_artifact_bytes(base/p)).hexdigest() for p in SOURCES},
        ordinary_proof=dict(sha256=sha256(raw_proof).hexdigest(), byte_count=len(raw_proof)),
        producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        actual_family=dict(old_source_certificate=SOURCE, old_height=N, old_labels=204,
            old_private_membership_checks_consumed=204**2, old_private_checks_rerun=False,
            added_labels=new_private, original_label_count=212, period=period,
            old_private_CRT_lifts=lifts, uncovered_integer=new_hole,
            unchanged357_source={k: old['source'][k] for k in ('S', 'S0', 'qJ', 'delta', 'rho')}),
        support_geometry=dict(pure_pair_checks=pair_checks, original15_checks=rectangle_checks,
            small_prefix_counts=small, pure_prefix_counts=counts, mixed35_prefix_counts=grid,
            general_bound='Nd=A35(i,j)*A7(k)*prod_(p in E)(p-1); c_nu(d)>=1/Nd; c_nu(1)=1 exactly.'),
        same_table_sums=dict(A35=A35, B35=B35, Arest=Arest, Brest=Brest, A=A, B=B, B_minus_12A=B-12*A),
        fixed_quarter_target=dict(coefficients=fixed, theta=theta, limit=limit,
            same_objective_lower=lower, strict_gap=lower-limit),
        all_thresholds=dict(target=target, fraction=q, initial_floor=54, rows=rows,
            final_strict_floor=carried, final_gap=carried-target,
            negative_unit_example=dict(clips=(F(1,10000),)+(F(1,4),)*8, coefficient=unit_coefficient),
            scope='Use nonunit coefficient positivity and the exact unit. If allocated final mass is nonpositive the gate fails immediately; otherwise each earlier allocated mass and every relaxed denominator is positive, so the nine barriers apply.'),
        later_unrefunded_tail=later_tail(io, base, carried),
        persistent_nonunit_tail=persistent_tail(io, base, A, B))
    return io, encode(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--proof', type=Path)
    parser.add_argument('--certificate', type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io, result = calculate(args.base, args.proof or args.base/PROOF)
    path = args.certificate or args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path), object_pairs_hook=io._unique), 'Complete exact certificate replay')
    print('PASS actual212-label CRT augmentation; 198 pure-pair and24 rectangle checks; 16 complete small-prefix counts; all9 scalar barriers')
    print('Fixed target gap positive; all-threshold assigned ratio >7129/50 >138877/1000')
    print('PASS 4071 exact later T6 barriers; every legal schedule stops by38851')
    print('PASS 6400 persistent nonunit barriers with directed products; allocated budget fails by63997')


if __name__ == '__main__':
    main()
