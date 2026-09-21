"""Exact independent controls for the phase-shell accounting and every row cut."""
import argparse
import sys
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import lcm
from pathlib import Path
import json

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--base', type=Path, required=True, help='erdos7-odd-covering report root')
mode = parser.add_mutually_exclusive_group(required=True)
mode.add_argument('--write', action='store_true')
mode.add_argument('--check', action='store_true')
args = parser.parse_args()
base = args.base.resolve()
sys.path.insert(0, str(base))
from certificate_io import read_artifact_bytes, write_certificate_text
folder = base/'frontier/cover-geometry'
input_path = folder/'phase_shell_transport.input.json'
result_path = folder/'phase_shell_transport.json'
input_raw = read_artifact_bytes(input_path)
inputs = json.loads(input_raw)
checks = 0


def require(condition, message):
    global checks
    if not condition:
        raise ValueError(message)
    checks += 1


def valuation(n, p):
    if n == 0:
        raise ValueError('zero valuation is not needed on a mismatch')
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e


def factor(n):
    return {p: valuation(n, p) for p in range(2, n + 1)
            if n % p == 0 and all(p % d for d in range(2, p))}


def audit(name, classes):
    period = lcm(*(m for a, m in classes))
    count = len(classes)
    factors = [factor(m) for a, m in classes]
    primes = sorted({p for fs in factors for p in fs})
    hits = [tuple(t for t, (a, m) in enumerate(classes) if (x-a) % m == 0)
            for x in range(period)]
    require(all(hits), 'the fixture is a whole cover')
    owners = [hs[0] if len(hs) == 1 else None for hs in hits]
    unique = [[x for x, t0 in enumerate(owners) if t0 == t] for t in range(count)]
    require(all(unique), 'every original class has a private residue')
    require(min(map(len, hits)) == 1, 'all private points attain the global minimum1')
    overlap = [x for x, hs in enumerate(hits) if len(hs) >= 2]
    require(sum(map(len, unique)) + len(overlap) == period, 'the unique and overlap regions partition the period')
    u = [F(len(xs), period) for xs in unique]
    shells = []
    for s, (a, m) in enumerate(classes):
        for p, e in factors[s].items():
            cofactor = m // p**e
            for r in range(e):
                members = [x for x in range(period)
                           if (x-a) % (cofactor*p**r) == 0
                           and (x-a) % (cofactor*p**(r+1)) != 0]
                alpha = F(1, p**(e-r-1))
                cap = F(p-1, m)
                require(0 < alpha <= 1, 'every shell weight lies in (0,1]')
                require(alpha * F(len(members), period) == cap, 'exact weighted shell capacity')
                require(not any(x in unique[s] for x in members), 'a supplier shell misses its own private region')
                by_target = [alpha * F(sum(owners[x] == t for x in members), period)
                             for t in range(count)]
                active = sum((v for t, v in enumerate(by_target) if p in factors[t]), F(0))
                omitted = sum((v for t, v in enumerate(by_target) if p not in factors[t]), F(0))
                multi = alpha * F(sum(owners[x] is None for x in members), period)
                require(sum(by_target, F(0)) + multi == cap, 'all-target column identity')
                require(active + omitted + multi == cap, 'positive-demand column includes the omitted unique mass')
                shells.append({'s': s, 'p': p, 'r': r, 'members': members,
                               'alpha': alpha, 'cap': cap, 'B': by_target,
                               'active': active, 'V': omitted, 'W': multi})
    for s in range(count):
        supplied = [sh for sh in shells if sh['s'] == s]
        for x in range(period):
            require(sum(x in sh['members'] for sh in supplied) <= 1,
                    'all depths and all primes of one supplier are pointwise disjoint')
        for left, right in combinations(supplied, 2):
            require(not set(left['members']) & set(right['members']), 'pairwise shell disjointness')

    # Derive the directional sum directly from the published I_x(p) predicate,
    # independently of shell membership, at every actual private point.
    private_directions = 0
    for t, xs in enumerate(unique):
        for x in xs:
            for p in primes:
                direct = F(0)
                for s, (a, m) in enumerate(classes):
                    e = factors[s].get(p, 0)
                    if e and (a-x) % (m//p**e) == 0 and (a-x) % m != 0:
                        r = valuation(a-x, p)
                        require(0 <= r < e, 'a directional mismatch has an unambiguous finite depth')
                        direct += F(1, p**(e-r-1))
                via_shells = sum((sh['alpha'] for sh in shells if sh['p'] == p and x in sh['members']), F(0))
                require(direct == via_shells, 'the original weighted theorem sum equals the shell sum')
                require(direct >= factors[t].get(p, 0)*(p-1), 'Lettl-Sun inequality at a genuine global-minimum point')
                private_directions += 1

    rows = [(t, p) for t in range(count) for p in factors[t]]
    row_demand = {(t, p): u[t]*factors[t][p]*(p-1) for t, p in rows}
    for t, p in [(t, p) for t in range(count) for p in primes]:
        service = sum((sh['B'][t] for sh in shells if sh['p'] == p), F(0))
        require(service >= u[t]*factors[t].get(p, 0)*(p-1), 'integrated row demand, including zero-demand rows')

    cuts = []
    inactive_but_no_gain = None
    for mask in range(1, 1 << len(rows)):
        selected = [row for i, row in enumerate(rows) if mask & (1 << i)]
        targets = {t for t, p in selected}
        uq = sum((u[t] for t in targets), F(0))
        demand = sum((row_demand[row] for row in selected), F(0))
        actual = fine = coarse = F(0)
        for s, (a, m) in enumerate(classes):
            supplied = [sh for sh in shells if sh['s'] == s]
            service = sum((sh['B'][t] for sh in supplied for t, p in selected if sh['p'] == p), F(0))
            mass_bound = uq - (u[s] if s in targets else 0)
            active_shells = [sh for sh in supplied if any(sh['p'] == p and sh['B'][t] > 0 for t, p in selected)]
            depth_bound = sum((sh['cap'] for sh in active_shells), F(0))
            full_bound = sum((sh['cap'] for sh in supplied), F(0))
            require(service <= mass_bound, 'supplier service respects the common target-region budget')
            require(service <= depth_bound <= full_bound, 'supplier service respects the active-depth capacity')
            actual += service
            fine += min(mass_bound, depth_bound)
            coarse += min(mass_bound, full_bound)
            if depth_bound < full_bound and min(mass_bound, depth_bound) == min(mass_bound, full_bound):
                if inactive_but_no_gain is None:
                    inactive_but_no_gain = {'mask': mask, 'supplier': s, 'mass_bound': str(mass_bound),
                                            'active_bound': str(depth_bound), 'full_bound': str(full_bound)}
        require(demand <= actual <= fine <= coarse, 'the complete row-subset demand and cut chain')
        cuts.append([mask, str(demand), str(actual), str(fine), str(coarse)])

    demand = sum(row_demand.values(), F(0))
    W = sum((sh['W'] for sh in shells), F(0))
    V = sum((sh['V'] for sh in shells), F(0))
    cap = sum((sh['cap'] for sh in shells), F(0))
    positive_service = sum((sh['active'] for sh in shells), F(0))
    require(positive_service + W + V == cap, 'complete aggregate capacity identity')
    require(demand + W + V <= cap, 'aggregate weighted demand bound')
    omissions = [{'supplier_index': sh['s'], 'prime': sh['p'], 'depth': sh['r'],
                 'active': str(sh['active']), 'overlap': str(sh['W']),
                 'unused_unique': str(sh['V']), 'capacity': str(sh['cap'])}
                for sh in shells if sh['V']]
    if name == 'distinct_even':
        example = next(sh for sh in shells if (sh['s'], sh['p'], sh['r']) == (2, 2, 1))
        require((example['active'], example['W'], example['V'], example['cap']) ==
                (F(1, 6), F(0), F(1, 12), F(1, 4)), 'explicit omitted-column counterexample')
        require(V == F(2, 3), 'total omitted unique mass in the period12 control')
    return {'name': name, 'classes': classes, 'period': period, 'unique_regions': unique,
            'overlap_region': overlap, 'shell_count': len(shells), 'demand_rows': len(rows),
            'private_point_prime_checks': private_directions, 'cuts': len(cuts),
            'strictly_sharper_cuts': sum(F(row[3]) < F(row[4]) for row in cuts),
            'tight_cuts': sum(F(row[1]) == F(row[3]) for row in cuts),
            'column_omissions': omissions, 'demand': str(demand), 'overlap_tax': str(W),
            'unused_unique_service': str(V), 'total_shell_capacity': str(cap),
            'positive_demand_service': str(positive_service),
            'inactive_depth_without_strict_supplier_gain': inactive_but_no_gain,
            'cut_columns': ['mask', 'demand', 'actual_service', 'active_depth_bound', 'all_depth_bound'],
            'all_nonempty_cuts': cuts}


require(inputs['schema'] == 'phase-shell-transport-input-v1', 'recognized finite input schema')
require([case['name'] for case in inputs['cases']] == ['distinct_even', 'odd_repeated'],
        'the two explicitly scoped finite controls are present')
require(len({m for a, m in inputs['cases'][0]['classes']}) == len(inputs['cases'][0]['classes']),
        'the even control has distinct original moduli')
require(all(m % 2 for a, m in inputs['cases'][1]['classes']), 'the repeated control has only odd moduli')
records = [audit(case['name'], case['classes']) for case in inputs['cases']]
require((records[0]['cuts'], records[0]['strictly_sharper_cuts'], records[0]['tight_cuts']) == (127, 88, 11),
        'complete period12 cut enumeration')
require((records[1]['cuts'], records[1]['strictly_sharper_cuts'], records[1]['tight_cuts']) == (7, 0, 7),
        'complete repeated-odd cut enumeration')
# Derive the noncover failure directly from the complete retained input.
negative = inputs['noncover_control']
negative_classes = negative['classes']
negative_period = lcm(*(m for a, m in negative_classes))
x, p = negative['private_point'], negative['prime']
noncover_hits = [sum((y-a) % m == 0 for a, m in negative_classes) for y in range(negative_period)]
targets = [t for t, (a, m) in enumerate(negative_classes) if (x-a) % m == 0]
require(len(targets) == 1, 'the noncover control has the specified private point')
weighted = F(0)
for a, m in negative_classes:
    e = factor(m).get(p, 0)
    if e and (a-x) % (m//p**e) == 0 and (a-x) % m != 0:
        weighted += F(1, p**(e-valuation(a-x, p)-1))
demand = factor(negative_classes[targets[0]][1]).get(p, 0)*(p-1)
noncover = {'classes': negative_classes, 'period': negative_period,
            'uncovered': [y for y, h in enumerate(noncover_hits) if h == 0],
            'private_point': x, 'global_minimum': min(noncover_hits),
            'local_multiplicity': noncover_hits[x], 'prime': p,
            'weighted_sum': str(weighted), 'putative_demand': str(demand)}
require(noncover_hits == [1, 1, 0], 'irredundant noncover has global minimum0')
require(weighted == 1 and demand == 2 and weighted < demand,
        'the computed private-point lower bound fails without whole coverage')
out = {'status': 'PASS', 'records': records, 'noncover_negative_control': noncover,
       'active_checks': checks, 'producer_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
       'input_sha256': sha256(input_raw).hexdigest(),
       'serializer_sha256': sha256((base/'certificate_io.py').read_bytes()).hexdigest(),
       'scope': 'Finite ordinary controls and explicit accounting counterexample only; no distinct odd cover, no universal contradiction, no Lean theorem.'}
encoded = json.dumps(out, indent=2)+'\n'
if args.write:
    write_certificate_text(result_path, encoded)
else:
    if read_artifact_bytes(result_path) != encoded.encode():
        raise ValueError('canonical result differs from recomputation or code/input/serializer bindings')
print(json.dumps({'mode': 'write' if args.write else 'check', 'status': 'PASS', 'active_checks': checks,
                  'cuts': [r['cuts'] for r in records], 'omitted_V': records[0]['unused_unique_service']}, indent=2))
