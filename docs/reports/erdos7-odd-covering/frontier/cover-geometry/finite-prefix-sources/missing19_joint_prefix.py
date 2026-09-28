"""A fixed-query common-law bound for the missing-19 eight-prime core.

Consumes the retained basic geometry and a small attributed geometry extension.
No geometry producer is executed. Source comparison formulas adapted from
Michael Schroeder, Nine Prime Divisors in Odd Distinct Covering Systems 1.0.1,
MIT license (full license and immutable source pins in the geometry artifact).
Exact rational calculation under the attributed comparison theorem; not Lean.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from math import prod
from pathlib import Path
import json

PRIMES = (7, 11, 13, 17, 23, 29)
THRESHOLDS = (2, 4, 4, 8, 12, 16)
CAPS = tuple(F(p-1, p-1-t) for p, t in zip(PRIMES, THRESHOLDS))
QUERY = 18
TARGET = F(29)
RATIOS = tuple(sorted({F(t, m) for t in (2, 4, 8, 12) for m in range(1, t)}))
REGIONS = tuple(product((False, True), repeat=2))
MODS = (3, 9, 27, 5, 15, 45)
PROJECTIONS = tuple(product((1, 2), range(1, 5), (2, 4, 5, 7, 8), (1, 4, 7, 8, 11, 13, 14)))
PINS = {
    'six_prime_prefix_certificate.json': 'ecdeb6246626c101b7bb16130366a7d22bf8d71775d5f28997b85e74c796ee61',
    'six_prime_prefix_geometry.json': '0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1',
    'six_prime_prefix_certificate.py': '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4',
    'query_stoploss_completion.py': '289acdd682bd06def66d93fe11950e7f6eec680712bd639093d1adb205538dfb',
}
EXTENSION_PIN = '718f9f331e694cd7e58032dd288b956f2edd4d6eea7320619f73d285443e3c24'


def require(test, message):
    if not test:
        raise ValueError(message)


def load_module(path, name):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def up(x):
    require(x >= 0, 'nonnegative source loss')
    return F(-(-x.numerator*10**10//x.denominator), 10**10)


@lru_cache(None)
def cells(a, b, r):
    return tuple(x for x in range(135) if x % 3 and x % 9 != 1 and x % 27 != b
                 and x % 5 and x % 15 != a and (r < 0 or x % 45 != r))


def weights(node, region):
    a, b, c, r, j, d, k, i, z = node
    require(z == -1, 'no pure3 refinement in this certificate')
    return tuple((1 if region[0] else 4) *
                 (1 if region[1] else 16-4*(x % 5 == c)-(x % 5 == j)
                  -(4-i)*(d != 0 and x % 3 == d and x % 5 == k))
                 for x in cells(a, b, r))


def counts(cs, projection):
    return tuple(sum(x % m == a for m, a in zip((3, 5, 9, 15), projection)) for x in cs)


def coefficients(mode, u, v):
    if mode in ('current', 'common'):
        return (F(1, 7), F(1, 7), 1+u, v+F(1, 7), v+F(1, 7), 1+v, (1+u)*(1+v))
    return (1, 1, 1+u, 1+v, 1+v, 1+v, (1+u)*(1+v))


def depth(p, positive, stop):
    if not positive:
        return ((0, F(1)),), (F(1), F(0)), (F(0), F(0)), (F(1), F(0))
    atoms = tuple((j, F(p-1, p**(j+1))) for j in range(1, stop))
    retained = sum(w for j, w in atoms), sum(j*w for j, w in atoms)
    tail = F(1, p**stop), F(1, p**stop)*(stop+F(1, p-1))
    whole = F(1, p), F(1, p-1)
    require(tuple(retained[i]+tail[i] for i in range(2)) == whole, 'exact anchor-tail mass and mean')
    return atoms, retained, tail, whole


def reserve(node):
    a, b, c, r, j, d, k, i, _ = node
    gamma15 = 3*(a == 1)+(b % 3 == a % 3)
    D = lambda h: F(c == h, 5)+F(j == h, 20)
    value = F(135, 4)+gamma15+(9-gamma15)*D(a)
    if r >= 0:
        gamma45 = F(b % 9 == r % 9)
        value += gamma45+(3-gamma45)*D(r % 5)
    if d:
        size = sum(x % 3 == d and x % 5 == k for x in cells(a, b, r))
        value += F(9, 5)-size*F(4-i, 20)
    return value


class Geometry:
    def __init__(self, base, extension):
        self.base, self.extension = base, extension
        self.used_base, self.used_extension, self.fallback = set(), set(), set()
        self.sizes = {}

    def table(self, cs, ws, mode, region, projection):
        uv = tuple(product(range(1, 12) if region[0] else (0,), range(1, 9) if region[1] else (0,)))
        ts = RATIOS if mode == 'ordinary' else (F(1 if mode == 'current' else 2),)
        off = tuple(6*n for n in counts(cs, projection)) if mode == 'current' else (0,)*len(cs)
        lines = [str(len(cs))]+[f'{x} {w} {o}' for x, w, o in zip(cs, ws, off)]
        labels = []
        for u, v in uv:
            co = coefficients(mode, u, v)
            for t in ts:
                den = t.denominator if mode == 'ordinary' else 7
                baseline = den if mode == 'ordinary' else 13 if mode == 'common' else 0
                ico = [int(den*x) for x in co]
                require(all(F(x, den) == y for x, y in zip(ico, co)), 'integer geometry coefficients')
                lines.append(' '.join(map(str, [len(labels), den, baseline, *ico, int(den*t)])))
                labels.append((u, v, t, den))
        key = sha256(('\n'.join(lines)+'\n').encode()).hexdigest()
        if key in self.base:
            raw = self.base[key]['integer_maxima']
            self.used_base.add(key)
        elif key in self.extension:
            raw = self.extension[key]['integer_maxima']
            self.used_extension.add(key)
        else:
            return None
        require(len(raw) == len(labels), 'geometry row count')
        require(all(len(row) == 3 and row[0] == i and row[1] == lab[3] and 0 <= row[2] < 2**30
                    for i, (row, lab) in enumerate(zip(raw, labels))), 'geometry labels and bounds')
        self.sizes[key] = len(raw)
        return {(u, v, t): F(row[2], den) for (u, v, t, den), row in zip(labels, raw)}

    def region(self, node, mode, region, projection, killed):
        cs = cells(node[0], node[1], node[3])
        ws = weights(node, region)
        if killed:
            ws = tuple(w*(11, 11, 9, 6, 3)[n] for w, n in zip(ws, counts(cs, projection)))
        require(cs and len(cs) == len(ws) and all(0 <= w <= 704 for w in ws), 'geometric cell domain')
        ts = RATIOS if mode == 'ordinary' else (F(1 if mode == 'current' else 2),)
        inc = tuple(max(sum(w for x, w in zip(cs, ws) if x % m == a) for a in range(m)) for m in MODS)
        mass, largest = sum(ws), max(ws)
        offset = F(6, 7)*sum(w*n for w, n in zip(ws, counts(cs, projection))) if mode == 'current' else F(0)
        baseline = F(13, 7) if mode == 'common' else 0 if mode == 'current' else 1

        def linear(u, v):
            co = coefficients(mode, u, v)
            return baseline*mass+sum(c*h for c, h in zip(co, inc))+co[6]*largest+offset

        table = self.table(cs, ws, mode, region, projection)
        if table is None:
            require(mode == 'ordinary' and not killed and node[3] >= 0, 'missing required fine geometry')
            a, b, c, _, j, *_ = node
            basic = (a, b, c, -1, j, 0, 0, 0, -1)
            oldcs = cells(a, b, -1)
            oldws = weights(basic, region)
            oldmap = dict(zip(oldcs, oldws))
            require(all(x in oldmap and w <= oldmap[x] for x, w in zip(cs, ws)), 'pointwise basic domination')
            table = self.table(oldcs, oldws, mode, region, ())
            require(table is not None, 'basic geometry required for domination screen')
            self.fallback.add((node, region))
        # These are vertex upper bounds. No convexity of their minimum is asserted.
        if mode == 'ordinary':
            table = {key: min(value, linear(key[0], key[1])-mass) for key, value in table.items()}
        require(all(value >= 0 for value in table.values()), 'nonnegative hinge upper')
        return table, linear, mass, ts

    @lru_cache(None)
    def envelope(self, node, mode='ordinary', projection=(), killed=False):
        values = None
        mass = whole = F(0)
        for region in REGIONS:
            table, linear, total, ts = self.region(node, mode, region, projection, killed)
            if values is None:
                values = {t: F(0) for t in ts}
            ud, ur, ut, ua = depth(3, region[0], 12)
            vd, vr, vt, va = depth(5, region[1], 9)
            scale = F(1, (1 if region[0] else 6)*(1 if region[1] else 20))

            def integral(aa, bb):
                return aa[0]*bb[0]*linear(aa[1]/aa[0], bb[1]/bb[0]) if aa[0] and bb[0] else F(0)

            tail = integral(ut, va)+integral(ur, vt)
            require(tail >= 0, 'positive disjoint anchor-tail majorant')
            mass += scale*ua[0]*va[0]*total
            whole += scale*integral(ua, va)
            for t in ts:
                values[t] += scale*(sum(p*q*table[u, v, t] for u, p in ud for v, q in vd)+tail)
        return mass, whole, values


def compute(source_directory, geometry_path):
    for name, pin in PINS.items():
        require(sha256((source_directory/name).read_bytes()).hexdigest() == pin, 'pinned source '+name)
    raw = geometry_path.read_bytes()
    require(sha256(raw).hexdigest() == EXTENSION_PIN, 'extension pin')
    data = json.loads(raw)
    base = json.loads((source_directory/'six_prime_prefix_geometry.json').read_text())
    require(data['source_archive_sha256'] == base['source_archive_sha256'] and
            data['source_verifier_sha256'] == base['source_verifier_sha256'] and
            data['source_geometry_cpp_sha256'] == base['source_geometry_cpp_sha256'], 'same attributed geometry source')
    q = load_module(source_directory/'query_stoploss_completion.py', 'missing19_query_tools')
    geometry = Geometry(base['batches'], data['batches'])
    full, checks = q.comparison_distributions(PRIMES, CAPS, QUERY)
    skip, checks2 = q.comparison_distributions(PRIMES[1:], CAPS[1:], QUERY)

    def ordinary_hinge(t, stage, env):
        return q.query_hinge(t, full[stage], *env)

    def weighted_hinge(t, dist, mean, probability, env):
        mass, whole, values = env
        low = {m: w for m, w in dist.items() if m < t}
        prob, first = sum(low.values(), F(0)), sum((m*w for m, w in low.items()), F(0))
        require(0 <= prob <= probability and 0 <= first <= mean, 'positive multiplier component remainder')
        value = (sum((m*w*q.anchor_hinge_upper(F(t, m), *env) for m, w in low.items()), F(0))
                 +(mean-first)*whole-t*(probability-prob)*mass)
        require(value >= 0, 'nonnegative charged hinge component')
        return value

    def charged_hinge(t, stage, ordinary, zero):
        require(1 <= stage <= 6, 'post-seven charged stage')
        table, mean = full[stage]
        omitted, omitted_mean = skip[stage-1]
        positive = {m: table.get(m, F(0))-F(11, 14)*omitted.get(m, F(0)) for m in table.keys() | omitted.keys()}
        require(all(w >= 0 for w in positive.values()), 'matched positive-depth multiplier atoms')
        return (weighted_hinge(t, positive, mean-F(11, 14)*omitted_mean, F(3, 14), ordinary)
                +weighted_hinge(t, omitted, omitted_mean, F(1), zero)/14)

    def ordinary_row(node):
        env = geometry.envelope(node)
        losses = [up(ordinary_hinge(t, i, env)/(p-1-t)) for i, (p, t) in enumerate(zip(PRIMES, THRESHOLDS))]
        return reserve(node), losses, ordinary_hinge(QUERY, 6, env)

    terminal = []

    def accept(phase, node, projection, R, costs, numerator):
        live = R-sum(costs, F(0))
        slack = (TARGET-QUERY+1)*live-numerator
        if slack <= 0:
            return False
        require(live > 0 and numerator >= 0, 'strict same-law live-mass and query bound')
        terminal.append(dict(phase=phase, node=node, projection=projection, live=live,
                             slack=slack, bound=QUERY-1+numerator/live))
        return True

    failed_basic = []
    for a, b in product((1, 2), (2, 4)):
        for c in (a, 3-a):
            rows = [(a, b, c, -1, j, 0, 0, 0, -1) for j in range(1, 5)]
            if (a, b, c) == (2, 4, 1):
                for node in rows:
                    R, losses, numerator = ordinary_row(node)
                    require((TARGET-QUERY+1)*(R-sum(losses,F(0)))-numerator <= 0, 'basic chart requires refinement')
                failed_basic.extend(rows)
                continue
            for node in rows:
                require(accept('basic', node, (), *ordinary_row(node)), 'remaining basic chart below29')
    require(len(failed_basic) == 4, 'all32 basic vertices evaluated')
    pending = []
    mixed = []
    for r in (4, 7, 8, 11, 16, 22, 31, 34):
        for d, k in product((1, 2), range(1, 5)):
            if (d, k) == (2, 2):
                continue
            for j, i in [(j, 0) for j in range(1, 5)]+[(k, 1)]:
                node = (2, 4, 1, r, j, d, k, i, -1)
                R, losses, numerator = ordinary_row(node)
                mixed.append(node)
                if not accept('mixed', node, (), R, losses, numerator):
                    pending.append((node, R, losses, numerator))
    require(len(mixed) == 280 and len(set(mixed)) == 280 and len(pending) == 2, 'mixed complete domain and routing')
    spatial = []
    for node, R, losses, numerator in pending:
        common = up(geometry.envelope(node, 'common')[2][F(2)]/4)
        cs = cells(node[0], node[1], node[3])
        _, _, c, r, j, d, k, i, _ = node
        wtotal = [20-4*(x % 5 == c)-(x % 5 == j)-(4-i)*(x % 3 == d and x % 5 == k) for x in cs]
        for projection in PROJECTIONS:
            score = sum(w*max(s-1, 0) for w, s in zip(wtotal, counts(cs, projection)))
            costs = [min(losses[0], common+F(3*score, 280))]+losses[1:]
            if not accept('coarse7', node, projection, R, costs, numerator):
                spatial.append((node, projection, R, costs, numerator))
    charged = []
    for node, projection, R, losses, numerator in spatial:
        current = up(geometry.envelope(node, 'current', projection)[2][F(1)]/4)
        costs = [min(losses[0], current)]+losses[1:]
        if not accept('current7', node, projection, R, costs, numerator):
            charged.append((node, projection, R, costs))
    for node, projection, R, costs in charged:
        ordinary = geometry.envelope(node)
        zero = geometry.envelope(node, 'ordinary', projection, True)
        costs = costs[:1]+[up(charged_hinge(t, i, ordinary, zero)/(p-1-t))
                           for i, (p, t) in enumerate(zip(PRIMES, THRESHOLDS)) if i > 0]
        numerator = charged_hinge(QUERY, 6, ordinary, zero)
        require(accept('charged7', node, projection, R, costs, numerator), 'last same-law charged continuation')
    require(geometry.used_extension == set(data['batches']), 'minimal extension: every retained entry used')
    require(len(geometry.used_base) == 72 and len(geometry.used_extension) == 102, 'exact cache coverage')
    phase_counts = dict(Counter(row['phase'] for row in terminal))
    require(phase_counts == dict(basic=28, mixed=278, coarse7=554, current7=4, charged7=2), 'complete disjoint terminal coverage')
    minimum_mass = min(row['live'] for row in terminal)
    minimum_slack = min(row['slack'] for row in terminal)
    maximum_bound = max(row['bound'] for row in terminal)
    require(minimum_mass > 0 and minimum_slack > 0 and maximum_bound < TARGET, 'full-domain strict certificate')
    result = dict(scope='One query-independent law on each fixed finite query carrier K supported on the eight core primes and resolving the original and parent31 cofactor-query heights, for every actual core family on (3,5,7,11,13,17,23,29). Conditional on the attributed source completion, same charged capped kernels, arbitrary-label comparison and finite prime transport. No projective compatibility, unrestricted odd-covering conclusion, or Lean verification.',
                  source_primes=(3, 5)+PRIMES, source_thresholds=THRESHOLDS, caps=CAPS, fixed_query=QUERY,
                  strict_query_bound=TARGET, phase_counts=phase_counts, terminal_rows=len(terminal),
                  all_domain_live_cell_lower=minimum_mass, all_domain_haar_mass_lower=minimum_mass/135,
                  all_domain_slack_lower=minimum_slack, worst_vertex_query_upper=maximum_bound,
                  worst_vertex_query_upper_decimal=float(maximum_bound),
                  unnormalized_density_cap=prod(CAPS), normalized_density_cap=135*prod(CAPS)/minimum_mass,
                  independent_multiplier_checks=checks+checks2,
                  cached_basic_batches=len(geometry.used_base), cached_extension_batches=len(geometry.used_extension),
                  extension_integer_maxima=sum(geometry.sizes[k] for k in geometry.used_extension),
                  basic_domination_vertex_regions=len(geometry.fallback), input_pins=PINS,
                  extension_sha256=sha256(raw).hexdigest(),
                  tight_vertices=[row for row in terminal if row['bound'] == maximum_bound],
                  final_charged_vertices=[row for row in terminal if row['phase'] == 'charged7'])
    return result, geometry.used_extension


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--geometry', type=Path, default=Path(__file__).with_name('missing19_joint_prefix_geometry.json'))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--used-keys', type=Path)
    args = parser.parse_args()
    result, keys = compute(args.source_directory, args.geometry)
    rendered = json.dumps(result, default=str, indent=2)+'\n'
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end='')
    if args.used_keys:
        args.used_keys.write_text(json.dumps(sorted(keys), indent=2)+'\n')


if __name__ == '__main__':
    main()
