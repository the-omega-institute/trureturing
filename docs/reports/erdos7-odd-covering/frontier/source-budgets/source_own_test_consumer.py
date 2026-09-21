#!/usr/bin/env python3
"""Replay source cell costs, four through37 consumers, and a reweighted through41 law.

Exact rational comparison arithmetic only. The ordinary proof supplies the
actual-source domination, convexity, and unrestricted exponent tails.
"""
import argparse
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
from functools import lru_cache
from hashlib import sha256
from itertools import product
import importlib.util
import json
import sys
sys.dont_write_bytecode = True
DEFAULT_PROOF = 'profile-notes/321-384/339-irredundant-source-seven-labels-bound-the-actual-surplus.md'
DEFAULT_CERTIFICATE = 'certificates/source_norms/source-budgets/source_own_test_consumer.json'
PREFIX = ((11, F(5, 3)), (13, F(12, 7)))
FIXED_SCHEDULE = ((17, 6), (19, 8), (23, 9), (29, 12), (31, 16), (37, 18))
FULL_HAAR_HEAD = ((11, 3), (13, 4))
MAIN_SCHEDULE = ((17, 6), (19, 8), (23, 9), (29, 12), (31, 16), (37, 20))
SOURCE_WITNESS = 'certificates/source_norms/source-budgets/irredundant_whole_j_finite_source.json'
SOURCES = (SOURCE_WITNESS, 'profile-notes/001-064/16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md', 'certificate_io.py', 'verify_joint_frontier.py', 'profile-notes/001-064/31-one-original-zero-five-layout-across-both-actual-measures.md', 'profile-notes/001-064/42-whole-hinge-absorption-sharpens-actual-survival.md', 'profile-notes/321-384/329-a-finite-whole-j-neighborhood-covers-high-surplus.md', 'profile-notes/321-384/331-complete-physical-hinges-continue-finite-sources-through43.md', 'profile-notes/321-384/333-variable-full-haar-thresholds-retain-more-survivor-mass.md', 'certificates/source_norms/j-geometry/j_aligned_complete_moment_comparison.json', 'certificates/source_norms/moments-survival/high_rho_physical_hinge_prime_scan.json', 'certificates/source_norms/comparison-bounds/high_rho_full_haar_thresholds.json')

SOURCES += ('frontier/source-budgets/source_mean_sharpness.py',)

def require(ok, message):
    if not ok:
        raise ValueError(message)

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable source module')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value

def complete_law(factors, cutoff):
    """Finite product atoms and both complete tails, without truncating a law."""
    require(isinstance(cutoff, int) and cutoff >= 1, 'Positive integer tail entrance')
    atoms = {1: F(1)} if cutoff > 1 else {}
    mean = F(1)
    for prime, cap in factors:
        require(prime > 1 and 0 <= cap <= prime, 'Nonnegative comparison count law')
        following = {}
        for count, probability in atoms.items():
            for value in range(1, (cutoff - 1) // count + 1):
                mass = 1 - cap / prime if value == 1 else cap * F(prime - 1, prime ** value)
                following[count * value] = following.get(count * value, F(0)) + probability * mass
        atoms = following
        mean *= 1 + cap / (prime - 1)
    tail_mass = 1 - sum(atoms.values())
    tail_first = mean - sum(count * probability for count, probability in atoms.items())
    require(all(probability >= 0 for probability in atoms.values())
            and tail_mass >= 0 and tail_first >= cutoff * tail_mass,
            'Complete count probability and first-moment tail')
    return atoms, tail_mass, tail_first

def calculate(base, proof):
    io = load('own_test_io', base / 'certificate_io.py')
    src = load('own_test_source', base / 'verify_joint_frontier.py')
    for number, name, producer in ((331, 'moments-survival/high_rho_physical_hinge_prime_scan', 'frontier/moments-survival/high_rho_physical_hinge_prime_scan.py'), (333, 'comparison-bounds/high_rho_full_haar_thresholds', 'frontier/comparison-bounds/high_rho_full_haar_thresholds.py')):
        obj = json.loads(io.read_artifact_bytes(base / f'certificates/source_norms/{name}.json'), object_pairs_hook=io._unique)
        for path, pin in obj['source_sha256'].items():
            require(sha256(io.read_artifact_bytes(base / path)).hexdigest() == pin, 'Current inherited source ' + path)
        pdoc = base / next((p for p in SOURCES if f'/{number}-' in p))
        raw = io.read_artifact_bytes(pdoc)
        require(sha256(raw).hexdigest() == obj['ordinary_proof']['sha256'] and len(raw) == obj['ordinary_proof']['byte_count'], 'Current inherited ordinary proof')
        require(sha256(io.read_artifact_bytes(base / producer)).hexdigest() == obj['producer_sha256'], 'Current inherited producer')
    delta = F(1, 4000)
    scale = 1 + 7 * delta
    ac = F(1, 7986)
    da = (6 - F(1, 7 ** 4)) / 35
    db = F(6, 35)
    weights = (da, da + db, F(0), F(0), F(0))
    oldM = F(13, 20) + F(91, 60) * delta
    pure5M = (536 + F(1, 7 ** 4)) / 840 + F(61, 42) * delta
    rhomax = F(14832829, 230496000)
    vertices = []
    for ib, il in product(range(2, 5), repeat=2):
        par = ((F(1, 2), F(0), F(0), F(0), F(0)), (F(0), F(1, 4)), tuple((F(1, 4) if i == ib else F(0) for i in range(5))), tuple((F(1, 72) if i == il else F(0) for i in range(5))), F(3, 4))
        vertices.append(src.data(par))
    surviving_weights = tuple(1 - u for u in weights)
    weighted35_vertices = []
    for d, m, eta, _, _ in vertices:
        wd, wm, we = (tuple(surviving_weights[l] * values[l] for l in range(5))
                      for values in (d, m, eta))
        rootmax = lambda values: max(sum(values[l] for l in range(5) if src.ROOT[l] == r)
                                    for r in range(2))
        weighted35_vertices.append(rootmax(wm) + max(wm) + max(wd) / 18
                                   + (sum(we) + rootmax(we) + max(we)) / 4
                                   + max(surviving_weights) / 72)
    weighted35_star = max(weighted35_vertices)
    require(weighted35_star == F(685487, 1512630), 'Complete weighted raw35 face mean')
    newM = scale * weighted35_star + F(3, 20) + F(13, 40) * delta
    require(newM == F(2923852811, 4840416000) and newM < pure5M,
            'Weighted full zero7 block sharpens the pure5-only source mean')

    class WeightedCost:

        def __init__(self, t, w, r=(F(1),) * 5, tag=None):
            self.t, self.w, self.r = F(t), w, r
            self.tag = tag or ('seven_block', (('h', self.t), 0))
            degree, slope, intercept, cutoff = src.zero5_cost_metadata(self.tag)
            require(degree == 1 and len(r) == len(w) == 5 and min(r) > 0,
                    'Positive cell weights and complete eventual affine cost')
            self.cut = max(2, cutoff)
            self.slopes = tuple(r[l] * (slope - w[l]) for l in range(5))
            self.intercepts = tuple(r[l] * (intercept + w[l] * self.t) for l in range(5))
            self.tail0, self.tail1 = (4 * x for x in src.geom(5, self.cut)[:2])
            for l in range(5):
                require(w[l] <= F(29, 35), 'Exact comparison: w[l] <= F(29, 35)')
                require(self.g(l, 1) == 0, 'Exact comparison: self.g(l, 1) == 0')
                for v in range(1, self.cut + 3):
                    require(self.g(l, v) >= 0 and self.g(l, v + 1) >= self.g(l, v), 'Exact comparison: self.g(l, v) >= 0 and self.g(l, v + 1) >= self.g(l, v)')
                    require(self.g(l, v + 2) - 2 * self.g(l, v + 1) + self.g(l, v) >= 0, 'Exact comparison: self.g(l, v + 2) - 2 * self.g(l, v + 1) + self.g(l, v) >= 0')
                require(self.g(l, self.cut) == self.slopes[l] * self.cut + self.intercepts[l], 'Exact comparison: self.g(l, self.cut) == self.slopes[l] * self.cut + self.intercepts[l]')

        @lru_cache(None)
        def g(self, l, v):
            return self.r[l] * (src.zero5_cost(self.tag, v) - self.w[l] * max(F(v) - self.t, F(0)))

        @lru_cache(None)
        def q(self, n, l, v):
            return (self.g(l, n * v) - self.g(l, n)) / n

        @lru_cache(None)
        def bar(self, l, v):
            return sum((F(4, 5 ** n) * self.q(n, l, v) for n in range(2, self.cut))) + self.tail0 * self.slopes[l] * (v - 1) - self.g(l, v) / 5

        def deep(self, fun, b, cut, slope):
            e = max(0, cut - b)
            require(fun(b + e + 1) - fun(b + e) == fun(b + e + 2) - fun(b + e + 1) == slope, 'Exact comparison: fun(b + e + 1) - fun(b + e) == fun(b + e + 2) - fun(b + e + 1) == slope')
            return sum((F(1, 3 ** (k + 3)) * (fun(b + k + 1) - fun(b + k)) for k in range(e))) + slope * src.geom(3, e + 3)[0]

        @lru_cache(None)
        def dg(self, l, b):
            return self.deep(lambda v: self.g(l, v), b, self.cut, self.slopes[l])

        @lru_cache(None)
        def dbar(self, l, b):
            return self.deep(lambda v: self.bar(l, v), b, self.cut, F(0))

        @lru_cache(None)
        def dq(self, n, l, b):
            return self.deep(lambda v: self.q(n, l, v), b, src.ceilq(F(self.cut, n)), self.slopes[l])

        def operator(self, dat):
            d, m, eta, _, _ = dat
            zero = max((sum((m[l] * self.g(l, b[l]) + eta[l] * self.bar(l, b[l]) for l in range(5))) + max((d[l] * self.dg(l, b[l]) + self.dbar(l, b[l]) for l in range(5))) for b in src.BASES))
            pos = F(0)
            for n in range(2, self.cut):
                pu = max((sum((eta[l] * self.q(n, l, b[l]) for l in range(5))) + max((self.dq(n, l, b[l]) for l in range(5))) for b in src.BASES))
                pos += F(4, 5 ** n) * (sum((eta[l] * self.g(l, n) for l in range(5))) + (n - 1) * pu)
            pa = max((sum((eta[l] * self.slopes[l] * (b[l] - 1) for l in range(5))) + max(self.slopes) / 18 for b in src.BASES))
            pos += self.tail1 * sum((eta[l] * self.slopes[l] for l in range(5))) + self.tail0 * sum((eta[l] * self.intercepts[l] for l in range(5))) + (self.tail1 - self.tail0) * pa
            return zero + pos

    @lru_cache(None)
    def rawgain(t):
        op = WeightedCost(t, weights)
        ref = WeightedCost(t, (F(0),) * 5)
        old = []
        new = []
        for dat in vertices:
            before = ref.operator(dat)
            require(before == src.zero5_raw(ref.tag, dat), 'Exact comparison: before == src.zero5_raw(ref.tag, dat)')
            after = op.operator(dat)
            require(after <= before, 'Exact comparison: after <= before')
            raw = src.raw357(t, dat)
            old.append(raw)
            new.append(raw - before + after)
        return (max(old) - max(new), tuple(old), tuple(new))
    out = {'delta': str(delta), 'mean_new': str(newM),
           'weighted_source_mean': {'weighted35_vertices': [str(v) for v in weighted35_vertices],
                                    'weighted35_star': str(weighted35_star),
                                    'positive7_face_cap': str(F(3, 20)),
                                    'positive7_delta_coefficient': str(F(13, 40)),
                                    'pure5_only_mean': str(pure5M)},
           'schedules': {}}
    inv = json.loads(io.read_artifact_bytes(base / 'certificates/source_norms/j-geometry/j_aligned_complete_moment_comparison.json'))
    count = inv['count_law']
    probs = {int(n): F(v) for n, v in count['probabilities'].items()}
    ids = {int(n): {int(t): F(v) for t, v in r.items()} for n, r in count['all_load_identities'].items()}
    tp = F(count['tail_probability'])
    apco = [{t: sum((probs[n] * ids[n].get(t, 0) / n for n in range(j + 1, 5))) + (tp if t == 1 else 0) for t in (1, 2, 3, 5)} for j in range(4)]
    coeff = {F(t): sum((r[t] for r in apco)) / 7 for t in (1, 2, 3, 5)}
    coeff[F(4)] = F(1, 6)
    for t in coeff:
        rawgain(t)
    require(all(v == c + F(3, 20) for v, c in zip(rawgain(F(1))[2], weighted35_vertices)),
            'Independent weighted35 formula agrees with every existing new h1 source cost')
    Doldv = [sum((c * rawgain(t)[1][i] for t, c in coeff.items())) + ac * F(13, 20) / 7 for i in range(9)]
    Dnewv = [sum((c * rawgain(t)[2][i] for t, c in coeff.items())) for i in range(9)]
    Djoint = scale * max(Dnewv) + ac * newM / 7
    originalD = F(0)
    for number, name in [(331, 'moments-survival/high_rho_physical_hinge_prime_scan'), (333, 'comparison-bounds/high_rho_full_haar_thresholds')]:
        obj = json.loads(io.read_artifact_bytes(base / f'certificates/source_norms/{name}.json'))
        ec = F(obj['denominator_mass_coefficient'])
        D = F(obj['denominator_constant'])
        require(D == scale * max(Doldv) + ac * F(91, 420) * delta, 'Exact comparison: D == scale * max(Doldv) + ac * F(91, 420) * delta')
        originalD = D
        fs = ks = cs = F(0)
        rows = []
        for row in obj['rows']:
            if row['prime'] > 37:
                break
            h = row['hinge'] if number == 331 else row
            k = F(row['charge_factor'])
            f = F(h['post_floor'])
            c = F(h['mass_coefficient'])
            tf = F(h['tail_first'])
            t = F(h['threshold'])
            atoms = {int(n): F(v) for n, v in h['count_atoms'].items()}
            factors = tuple(((int(p), F(v)) for p, v in h['full_factors']))
            post = tuple(((int(p), F(v)) for p, v in h['post' if number == 331 else 'incoming_post_factors']))
            require(factors == PREFIX + post, 'Same supported13 prefix and preceding physical caps')
            checked_atoms, tails = src.ap_product_distribution(factors, int(t))
            _, post_tails = src.ap_product_distribution(post, int(t))
            require(atoms == checked_atoms and F(h['tail_mass']) == tails[0] and (tf == tails[1]), 'Complete original full-factor count atoms and analytic tails')
            rebuilt_atoms, rebuilt_mass, rebuilt_first = complete_law(factors, int(t))
            _, rebuilt_post_mass, rebuilt_post_first = complete_law(post, int(t))
            require(rebuilt_atoms == checked_atoms and (rebuilt_mass, rebuilt_first) == tails[:2]
                    and (rebuilt_post_mass, rebuilt_post_first) == post_tails[:2],
                    'Independent full and post-only product-law reconstruction')
            require(f == post_tails[1] - t * post_tails[0] and c == tf - t * tails[0], 'Post13-only floor and entire affine product tail')
            weights_n = {n: p * n for n, p in atoms.items() if n < t}
            oldv = [sum((w * rawgain(t / n)[1][i] for n, w in weights_n.items())) for i in range(9)]
            newv = [sum((w * rawgain(t / n)[2][i] for n, w in weights_n.items())) for i in range(9)]
            require(scale * max(oldv) + tf * oldM == F(h['finite_constant']), "Exact comparison: scale * max(oldv) + tf * oldM == F(h['finite_constant'])")
            Cnew = scale * max(newv) + tf * newM
            fs += k * f
            ks += k * (c - f)
            cs += k * Cnew
            A = (1 - fs) * ec - ks
            B = (1 - fs) * Djoint + cs
            crit = B / A - F(3, 20) + F(263, 360) * delta
            require(A > 0 and ec * B - A * Djoint > 0, 'Exact comparison: A > 0 and ec * B - A * Djoint > 0')
            masses = {}
            for label, rho in [('benchmark', F(7, 120)), ('pure7_rho_upper', rhomax), ('source329_lower', F(1, 40))]:
                S = F(3, 20) + rho - F(263, 360) * delta
                require(ec * S - Djoint > 0, 'Exact comparison: ec * S - Djoint > 0')
                masses[label] = str((A * S - B) / (ec * S - Djoint))
            rows.append({'prime': row['prime'], 'threshold': str(t), 'old_finite_nonlinear': str(max(oldv)), 'new_finite_nonlinear': str(max(newv)), 'finite_nonlinear_saving': str(scale * (max(oldv) - max(newv))), 'new_C': str(Cnew), 'numerator_A': str(A), 'numerator_B': str(B), 'new_rho_critical': str(crit), 'remaining_to_rhomax': str(crit - rhomax), 'mass_lowers': masses, 'old_vertex_payments': [str(v) for v in oldv], 'new_vertex_payments': [str(v) for v in newv]})
        out['schedules'][str(number)] = rows
    require(ec == F(614921, 614922), 'Same supported13 denominator mass coefficient')
    def physical_chain(prefix, schedule, ec, Djoint, cost=None, mean=None, lower=None,
                       benchmark_rho=F(7, 120), mass_cases=None):
        cost = cost or (lambda t: rawgain(t)[2])
        mean = newM if mean is None else mean
        lower = lower or (lambda rho: F(3, 20) + rho - F(263, 360) * delta)
        mass_cases = mass_cases or [('benchmark', benchmark_rho), ('simple_guard', F(7, 125)),
                                    ('pure7_rho_upper', rhomax), ('source329_lower', F(1, 40))]
        fixed_rows = []
        post = ()
        fs = ks = cs = benchmark_charge = F(0)
        benchmark_S = lower(benchmark_rho)
        benchmark_E = ec * benchmark_S - Djoint
        require(benchmark_E > 0, 'Positive benchmark supported13 denominator')
        for prime, threshold in schedule:
            t = F(threshold)
            clip = t / (prime - 1)
            cap = F(prime - 1, prime - 1 - threshold)
            k = F(1, prime - 1 - threshold)
            require(0 < clip < 1 and cap == 1 / (1 - clip) and 0 < cap <= prime,
                    'One actual full-Haar clipped kernel at the prescribed threshold')
            factors = prefix + post
            atoms, tm, tf = complete_law(factors, threshold)
            _, pm, pf = complete_law(post, threshold)
            checked_atoms, checked_tails = src.ap_product_distribution(factors, threshold)
            _, checked_post_tails = src.ap_product_distribution(post, threshold)
            require(atoms == checked_atoms and (tm, tf) == checked_tails[:2]
                    and (pm, pf) == checked_post_tails[:2],
                    'Prescribed chain independent complete full and post-only laws')
            f = pf - t * pm
            c = tf - t * tm
            require(c >= f >= 0, 'Post13-only floor before the sole supported13 conditioning')
            vertex_payments = [sum(probability * count * cost(t / count)[i]
                                   for count, probability in atoms.items()) for i in range(9)]
            Cnew = scale * max(vertex_payments) + tf * mean
            require(Cnew >= 0 and ec * Cnew + (c - f) * Djoint > 0,
                    'Nonnegative centered numerator and decreasing hinge upper in actual S')
            hinge = f + (Cnew + (c - f) * benchmark_S) / benchmark_E
            charge = k * hinge
            benchmark_charge += charge
            fs += k * f
            ks += k * (c - f)
            cs += k * Cnew
            A = (1 - fs) * ec - ks
            B = (1 - fs) * Djoint + cs
            require(A > 0 and ec * B - A * Djoint > 0,
                    'Prescribed chain cumulative mass lower increases with actual S')
            crit = (B / A - lower(F(0))) / (lower(F(1)) - lower(F(0)))
            require(ec * (B / A) - Djoint > 0, 'Positive denominator at the strict source threshold')
            masses = {}
            for label, rho in mass_cases:
                S = lower(rho)
                require(ec * S - Djoint > 0, 'Positive prescribed-chain source denominator')
                masses[label] = str((A * S - B) / (ec * S - Djoint))
            require(F(masses['benchmark']) == 1 - benchmark_charge,
                    'Exact same-chain sum of charges and cumulative rational lower')
            fixed_rows.append({'prime': prime, 'threshold': str(t), 'clip_delta': str(clip),
                               'cap': str(cap), 'charge_factor': str(k),
                               'incoming_post_factors': [[p, str(v)] for p, v in post],
                               'full_factors': [[p, str(v)] for p, v in factors],
                               'count_atoms': {str(n): str(v) for n, v in atoms.items()},
                               'tail_mass': str(tm), 'tail_first': str(tf), 'post_floor': str(f),
                               'mass_coefficient': str(c), 'new_vertex_payments': [str(v) for v in vertex_payments],
                               'new_C': str(Cnew), 'benchmark_hinge_upper': str(hinge),
                               'benchmark_charge_upper': str(charge), 'numerator_A': str(A),
                               'numerator_B': str(B), 'new_rho_critical': str(crit),
                               'remaining_to_rhomax': str(crit - rhomax), 'mass_lowers': masses})
            post += ((prime, cap),)
        return {'schedule': [[p, t] for p, t in schedule],
                                 'endpoint': schedule[-1][0], 'benchmark_rho': str(benchmark_rho),
                                 'benchmark_S_lower': str(benchmark_S), 'benchmark_E_lower': str(benchmark_E),
                                 'rows': fixed_rows,
                                 'strict_source_threshold': fixed_rows[-1]['new_rho_critical'],
                                 'benchmark_mass_lower': fixed_rows[-1]['mass_lowers']['benchmark'],
                                 'scope': 'One fixed complete physical chain; no search or optimality assertion.'}
    out['fixed_schedule'] = physical_chain(PREFIX, FIXED_SCHEDULE, ec, Djoint)
    head_caps = tuple((p, F(p - 1, p - 1 - t)) for p, t in FULL_HAAR_HEAD)
    t11, t13 = (F(t) for _, t in FULL_HAAR_HEAD)
    k11, k13 = (F(1, p - 1 - t) for p, t in FULL_HAAR_HEAD)
    head_atoms, head_tm, head_tf = complete_law(head_caps[:1], int(t13))
    checked_head_atoms, checked_head_tails = src.ap_product_distribution(head_caps[:1], int(t13))
    require(head_atoms == checked_head_atoms and (head_tm, head_tf) == checked_head_tails[:2],
            'Independent complete original11 comparison law before the13 head')
    head_c = head_tf - t13 * head_tm
    head13_vertices = [sum(probability * count * rawgain(t13 / count)[2][i]
                           for count, probability in head_atoms.items()) for i in range(9)]
    head_vertices = [k11 * rawgain(t11)[2][i] + k13 * head13_vertices[i] for i in range(9)]
    head_e = 1 - k13 * head_c
    head_D = scale * max(head_vertices) + k13 * head_tf * newM
    require(head_caps == ((11, F(10, 7)), (13, F(3, 2)))
            and head_e == F(74535, 74536)
            and head_D == F(315424555117789, 3758179656000000),
            'Unconditioned full-Haar11/13 head from its own complete source costs')
    require(len(set(head_vertices)) == 1, 'All nine common head vertices attain the same comparison value')
    main_chain = physical_chain(head_caps, MAIN_SCHEDULE, head_e, head_D)
    main_chain['head'] = {'schedule': [list(row) for row in FULL_HAAR_HEAD],
                          'full_factors': [[p, str(cap)] for p, cap in head_caps],
                          'charge_factors': [str(k11), str(k13)],
                          'head13_count_atoms': {str(n): str(v) for n, v in head_atoms.items()},
                          'head13_tail_mass': str(head_tm), 'head13_tail_first': str(head_tf),
                          'head13_mass_coefficient': str(head_c),
                          'head13_nonlinear_vertices': [str(v) for v in head13_vertices],
                          'joint_nonlinear_vertices': [str(v) for v in head_vertices],
                          'denominator_mass_coefficient': str(head_e), 'denominator_constant': str(head_D),
                          'conditioning_count': 1}
    final_main_row = main_chain['rows'][-1]
    guard_rho = F(7, 125)
    guard_S = F(3, 20) + guard_rho - F(263, 360) * delta
    guard_E = head_e * guard_S - head_D
    guard_mass = F(final_main_row['mass_lowers']['simple_guard'])
    require(guard_E > 0 and guard_mass > F(1, 1000),
            'The simple rho>=7/125 and delta<=1/4000 guard has through37 mass greater than1/1000')
    main_chain['simple_guard'] = {'rho_lower': str(guard_rho), 'delta_upper': str(delta),
                                   'S_lower': str(guard_S), 'E_lower': str(guard_E),
                                   'mass37_lower': str(guard_mass), 'certified_mass_floor': str(F(1, 1000))}
    witness = json.loads(io.read_artifact_bytes(base / SOURCE_WITNESS), object_pairs_hook=io._unique)
    for path, pin in witness['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base / path)).hexdigest() == pin,
                'Current finite original source input ' + path)
    witness_producer = base / 'frontier/source-budgets/irredundant_whole_j_finite_source.py'
    require(sha256(io.read_artifact_bytes(witness_producer)).hexdigest() == witness['producer_sha256'],
            'Current finite original source producer')
    witness_proof = io.read_artifact_bytes(base / DEFAULT_PROOF)
    require(sha256(witness_proof).hexdigest() == witness['ordinary_proof']['sha256']
            and len(witness_proof) == witness['ordinary_proof']['byte_count'],
            'Current finite original source ordinary proof')
    family = witness['original_forbidden_classes']
    require(witness['height'] == 12 and len(family) == witness['original_label_count'] == 204
            and len(witness['private_integer_witnesses']) == len(family)
            and any(c['modulus'] == 7 for c in family), 'Actual N12 original source and modulus7 premise')
    for i, private in enumerate(witness['private_integer_witnesses']):
        x = private['private_integer']
        require(private['original_index'] == i
                and [j for j, c in enumerate(family) if x % c['modulus'] == c['residue']] == [i],
                'Each original class has its own independently checked private integer')
    require(all(witness['uncovered_integer'] % c['modulus'] != c['residue'] for c in family),
            'The actual finite witness remains a noncover')
    witness_mass = {name: F(witness['mass'][name]) for name in ('S', 'S0', 'rho', 'qJ', 'delta')}
    require(witness_mass['rho'] == witness_mass['S'] - witness_mass['S0']
            and witness_mass['qJ'] == 1 - witness_mass['delta']
            and 0 <= witness_mass['delta'] <= delta and witness_mass['rho'] >= guard_rho
            and witness_mass['S'] >= F(3, 20) + witness_mass['rho'] - F(263, 360) * delta,
            'Actual finite source parameters satisfy the new simple guard and source lower bound')
    actual_E = head_e * witness_mass['S'] - head_D
    actual_lower = (F(final_main_row['numerator_A']) * witness_mass['S']
                    - F(final_main_row['numerator_B'])) / actual_E
    require(actual_E > 0 and actual_lower >= guard_mass,
            'The actual N12 source has positive mass under the prescribed physical continuation')
    main_chain['actual_finite_source'] = {'certificate': SOURCE_WITNESS, 'height': 12,
                                          'original_label_count': len(family),
                                          'private_membership_checks': len(family) ** 2,
                                          'mass': {k: str(v) for k, v in witness_mass.items()},
                                          'E_lower': str(actual_E), 'mass37_lower': str(actual_lower),
                                          'scope': 'Actual finite noncover satisfying the source guard; no extremal-cover witness.'}
    out['full_haar_head_chain'] = main_chain
    out['joint_denominator'] = {'old': str(originalD), 'new': str(Djoint), 'saving': str(originalD - Djoint), 'coefficients': {str(k): str(v) for k, v in coeff.items()}, 'new_face_nonlinear_vertices': [str(v) for v in Dnewv]}
    reference_costs = set(coeff) | {F(h['threshold']) / int(n) for number, name in [(331, 'moments-survival/high_rho_physical_hinge_prime_scan'), (333, 'comparison-bounds/high_rho_full_haar_thresholds')] for row in json.loads(io.read_artifact_bytes(base / f'certificates/source_norms/{name}.json'))['rows'] if row['prime'] <= 37 for h in [row['hinge'] if number == 331 else row] for n in h['count_atoms'] if int(n) < F(h['threshold'])}
    fixed_costs = {F(threshold, count) for _, threshold in FIXED_SCHEDULE for count in range(1, threshold)}
    main_costs = {t11} | {t13 / count for count in head_atoms} | {
        F(threshold, count) for _, threshold in MAIN_SCHEDULE for count in range(1, threshold)}
    require(all(len(set(rawgain(t)[2])) == 1 for t in main_costs),
            'Each main-chain source cost has one common value at all nine vertices')
    required_costs = reference_costs | fixed_costs | main_costs
    out['source_hinge_costs'] = {str(t): {'old_vertices': [str(v) for v in vals[1]], 'new_vertices': [str(v) for v in vals[2]], 'uniform_face_saving': str(vals[0])} for t in sorted(required_costs) for vals in [rawgain(t)]}
    require(len(reference_costs) == 70 and reference_costs <= required_costs and fixed_costs <= required_costs,
            'Complete new chain hinge inventory retains all70 reference costs')
    require(Djoint == F(18905277286609631, 253677126780000000), 'Exact common supported13 denominator')
    # One fixed reweighting of the same actual source; all positive7 blocks
    # and their constants/tails are weighted, not just the zero7 saving.
    r = (F(11, 8), F(5, 4), F(1), F(1), F(1))
    zero = (F(0),) * 5
    @lru_cache(None)
    def weighted_hinges(t, cell_weights=r):
        t = F(t)
        require(t >= 1, 'Centered reweighted source threshold')
        _, a, b, cutoff = src.zero5_cost_metadata(('h', t))
        tails = tuple(F(36, 5) * v for v in src.geom(7, cutoff))
        expectation = sum(src.zero7_probability(n) * max(F(n) - t, F(0))
                          for n in range(1, cutoff)) + a * tails[1] + b * tails[0]
        first = WeightedCost(t, weights, cell_weights)
        remaining = [WeightedCost(t, zero, cell_weights, ('seven_block', (('h', t), e)))
                     for e in range(1, cutoff - 1)]
        tail = WeightedCost(F(1), zero, cell_weights, ('h', F(1)))
        coefficient = a * (tails[1] - (cutoff - 1) * tails[0])
        require(coefficient >= 0, 'Complete nonnegative original7 block tail')
        return tuple(expectation * sum(v * n for v, n in zip(cell_weights, dat[1]))
                     + first.operator(dat) + sum(op.operator(dat) for op in remaining)
                     + coefficient * tail.operator(dat) for dat in vertices)
    for t in required_costs:
        require(weighted_hinges(t, (F(1),) * 5) == rawgain(t)[2],
                'General cell-weight implementation preserves every inherited hinge')
    mean_r = scale * max(weighted_hinges(F(1)))
    cap_B = (1 - weights[1]) * (F(1, 12) + delta / 36)
    cap_R = F(1, 8) + 5 * delta / 24
    def mass_r(rho):
        return r[0] * (F(3, 20) + rho - F(263, 360) * delta) \
            - (r[0] - r[1]) * cap_B - (r[0] - 1) * cap_R
    mass_slope = -r[0] * F(263, 360) - (r[0] - r[1]) * (1 - weights[1]) / 36 \
        - (r[0] - 1) * F(5, 24)
    require(mass_slope < 0, 'Weighted mass lower decreases with the source error budget')
    weighted_head13 = [sum(probability * count * weighted_hinges(t13 / count)[i]
                          for count, probability in head_atoms.items()) for i in range(9)]
    weighted_head = [k11 * weighted_hinges(t11)[i] + k13 * weighted_head13[i] for i in range(9)]
    D_r = scale * max(weighted_head) + k13 * head_tf * mean_r
    schedule_r = MAIN_SCHEDULE + ((41, 23),)
    chain_r = physical_chain(head_caps, schedule_r, head_e, D_r, weighted_hinges, mean_r,
                             mass_r, F(9, 140), [('benchmark', F(9, 140)), ('simple_guard', F(3, 50))])
    chain_r['benchmark_T_lower'] = chain_r.pop('benchmark_S_lower')
    chain_r['weights'] = [str(v) for v in r]
    chain_r['source_hinge_costs'] = {str(t): [str(v) for v in weighted_hinges(t)] for t in sorted(
        {F(1), t11} | {t13 / n for n in head_atoms} |
        {F(threshold, n) for _, threshold in schedule_r for n in range(1, threshold)})}
    chain_r['mean_upper'] = str(mean_r)
    chain_r['source_mass_lower'] = {'capacity_B': str(cap_B), 'capacity_root1': str(cap_R),
                                   'error_derivative': str(mass_slope),
                                   'formula': 'T >= (11/8)*(3/20+rho-(263/360)*delta0) - capacity_B/8 - 3*capacity_root1/8'}
    chain_r['head'] = dict(main_chain['head'], head13_nonlinear_vertices=[str(v) for v in weighted_head13],
                           joint_nonlinear_vertices=[str(v) for v in weighted_head], denominator_constant=str(D_r))
    guard_T, guard_E = mass_r(F(3, 50)), head_e * mass_r(F(3, 50)) - D_r
    final_r = chain_r['rows'][-1]
    require(mean_r == F(129284945411, 193616640000)
            and D_r == F(8070958205846453, 90196311744000000)
            and guard_T == F(22726567063, 96808320000)
            and guard_E == F(26206200489324719, 180392623488000000)
            and F(final_r['mass_lowers']['simple_guard']) > F(1, 125),
            'The same reweighted actual law has through41 mass greater than1/125')
    chain_r['simple_guard'] = {'rho_lower': '3/50', 'delta_upper': str(delta), 'T_lower': str(guard_T),
                               'E_lower': str(guard_E), 'mass41_lower': final_r['mass_lowers']['simple_guard'],
                               'certified_mass_floor': '1/125'}
    # Reuse the finite original construction, never its consumer-dependent
    # output certificate: that would introduce a data dependency cycle.
    sharp = load('own_test_sharp_family', base / 'frontier/source-budgets/source_mean_sharpness.py')
    finite = load('own_test_finite_source', base / 'frontier/source-budgets/irredundant_whole_j_finite_source.py')
    example = sharp.calculate_family(finite, src, 12)
    data_r = example['source']
    actual_cells = tuple(n * w for n, w in zip(data_r['n'], data_r['w']))
    actual_T = sum(v * m for v, m in zip(r, actual_cells))
    actual_E = head_e * actual_T - D_r
    actual_bound = (F(final_r['numerator_A']) * actual_T - F(final_r['numerator_B'])) / actual_E
    require(data_r['rho'] >= F(3, 50) and data_r['delta'] <= delta
            and actual_T >= mass_r(data_r['rho']) and actual_E > 0
            and actual_bound >= F(final_r['mass_lowers']['simple_guard'])
            and any(c['modulus'] == 7 for c in example['original_classes']),
            'Actual irredundant F12 supplies a nonempty reweighted through41 source domain')
    chain_r['actual_finite_source'] = {'construction': 'source_mean_sharpness.original_source', 'height': 12,
        'original_label_count': example['original_label_count'],
        'private_membership_checks': example['private_membership_checks'],
        'original_classes_sha256': sha256(json.dumps(example['original_classes'], sort_keys=True).encode()).hexdigest(),
        'mass': {k: str(data_r[k]) for k in ('S', 'S0', 'rho', 'qJ', 'delta')},
        'post7_cell_masses': [str(v) for v in actual_cells], 'T': str(actual_T),
        'E_lower': str(actual_E), 'mass41_lower': str(actual_bound),
        'scope': 'The actual finite noncover F12 meets the source guard; no extension to a covering family is claimed.'}
    chain_r['scope'] = 'Fixed positive mod9 reweighting of the same actual source, fixed full-Haar kernels, and one head normalization. Masses are relative to the reweighted supported13 probability. Through41 only; no optimality, through43, or unrestricted noncoverage conclusion.'
    # A coefficient proof covers every fixed nonnegative five-cell weight;
    # the fixed rational barriers cover every legal later scalar threshold.
    baseline_average = tuple(sum(F(b[l] ** 2 - 1, len(src.BASES)) for b in src.BASES)
                             for l in range(5))
    require(baseline_average == (F(23, 10),) * 5
            and F(23, 40) + F(7, 8) + F(5, 8) * F(23, 10) == F(231, 80)
            and F(23, 10) + F(231, 80) * F(4, 3) == F(123, 20),
            'Average-baseline lower coefficients for every nonnegative cell cost')
    for _, n, eta, _, _ in vertices:
        require(all(n[l] <= F(3, 4) * eta[l] for l in range(5)),
                'Uniform containing-face mass/pure-mass inequality')
    ratio_floor = F(2, 3) + (F(7, 15) + F(6, 5)) * F(123, 20)
    require(ratio_floor == F(131, 12) and ratio_floor > F(123, 20),
            'Every cell coefficient dominates (131/12) times its retained weight')
    J2 = src.moment(head_caps, 2)
    seed = 1 + (J2 * ratio_floor + J2 - 1) / head_e
    require(seed == F(216789167, 8944200) and seed > 24, 'All-cell assigned head bound')
    barriers = ((17, 24, 34), (19, 34, 48), (23, 48, 65), (29, 65, 83), (31, 83, 106),
                (37, 106, 131), (41, 131, 160), (43, 160, 197), (47, 197, 241),
                (53, 241, 291), (59, 291, 347), (61, 347, 417), (67, 417, 498),
                (71, 498, 596), (73, 596, 724), (79, 724, 879), (83, 879, 1079),
                (89, 1079, 1333), (97, 1333, 1649), (101, 1649, 2086), (103, 2086, 2756),
                (107, 2756, 3851), (109, 3851, 6062), (113, 6062, 12354), (127, 12354, 58341))
    primes = [p for p in range(17, 132) if all(p % d for d in range(2, p))]
    require([p for p, _, _ in barriers] + [131] == primes, 'Every intervening prime is retained')
    rows, carried = [], 24
    for p, f, k in barriers:
        ap, bp = F(3 * p - 1, (p - 1) ** 2), F(1, 4 * (p - 1) ** 2)
        A, B, C = F(k - f), F(f - k) + ap * f, bp * f * (k - 1)
        gap = 4 * A * C - B * B
        require(f == carried and 1 <= f < (p - 1) ** 2 and A > 0 and gap > 0
                and A * (B / (2 * A)) ** 2 + gap / (4 * A) == C,
                'Complete exact all-threshold quadratic barrier')
        rows.append({'prime': p, 'input_floor': f, 'output_strict_floor': k,
                     'quadratic': [str(v) for v in (A, B, C)], 'four_AC_minus_B_squared': str(gap)})
        carried = k
    require(carried == 58341 > (131 - 1) ** 2, 'Positive scalar denominator impossible at131')
    chain_r['all_cell_square_scalar_boundary'] = {
        'baseline_average': [str(v) for v in baseline_average], 'source_ratio_floor': str(ratio_floor),
        'head_square_multiplier': str(J2), 'assigned_head_floor': str(seed), 'scalar_quadratics': rows,
        'next_prime': 131, 'carried_floor': carried, 'strict_legal_input_cap': (131 - 1) ** 2,
        'scope': 'Every fixed nonnegative five-cell reweighting with T>0, the current WF/A2 square allocation and fixed(3,4) head. The assigned upper-bound procedure fails by131 for every legal scalar clipping schedule. This is not a lower bound on actual Gamma or a failure of actual survival or the complete-hinge chain.'}
    out['reweighted_full_haar_chain'] = chain_r
    proof_bytes = io.read_artifact_bytes(proof)
    out.update(schema='source-own-test-consumer-v1', scope='Ordinary finite-source comparison under effective9, qJ>=1-delta, delta<=1/4000, original noncontainment, and an original modulus-7 class. The main full-Haar head chain certifies through37 under rho>=7/125, with an actual finite noncover source satisfying this guard. Three supported13 reference chains remain as comparisons. A fixed mod9 reweighting certifies through41 under rho>=3/50, while every fixed nonnegative five-cell reweighting fails by131 within the stated assigned square/fixed-head/scalar procedure. Each chain retains complete product tails and its own original tests. No Lean, optimality, extremal-cover witness, or unrestricted noncoverage claim.', source_sha256={p: sha256(io.read_artifact_bytes(base / p)).hexdigest() for p in SOURCES}, ordinary_proof={'sha256': sha256(proof_bytes).hexdigest(), 'byte_count': len(proof_bytes)}, producer_sha256=sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(), source_weights=[str(w) for w in weights], vertex_count=len(vertices), pure7_rho_upper=str(rhomax), denominator_mass_coefficient=str(ec))
    return (io, out)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--proof', type=Path)
    parser.add_argument('--certificate', type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io, result = calculate(args.base, args.proof or args.base / DEFAULT_PROOF)
    certificate = args.certificate or args.base / DEFAULT_CERTIFICATE
    if args.write:
        io.write_certificate_text(certificate, json.dumps(result, indent=2) + '\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=io._unique), 'Full exact certificate replay')
    print('PASS', len(result['source_hinge_costs']), 'rational hinges; 9 source vertices; main chain and three reference chains through37')
    with localcontext() as ctx:
        ctx.prec = 24
        main = result['full_haar_head_chain']
        guard_mass = F(main['simple_guard']['mass37_lower'])
        benchmark_mass = F(main['benchmark_mass_lower'])
        print('full-Haar head', main['head']['schedule'], 'later schedule', main['schedule'],
              'through37 simple-guard mass', Decimal(guard_mass.numerator) / Decimal(guard_mass.denominator),
              'benchmark mass', Decimal(benchmark_mass.numerator) / Decimal(benchmark_mass.denominator))
        weighted = result['reweighted_full_haar_chain']
        wm = F(weighted['simple_guard']['mass41_lower'])
        print('reweighted through41 guard rho>=3/50 mass', Decimal(wm.numerator) / Decimal(wm.denominator))
        rho = F(result['fixed_schedule']['strict_source_threshold'])
        print('supported13 fixed reference', result['fixed_schedule']['schedule'], 'through37 strict rho threshold',
              rho, Decimal(rho.numerator) / Decimal(rho.denominator))
        for name, rows in result['schedules'].items():
            rho = F(rows[-1]['new_rho_critical'])
            print(name, 'through37 strict rho threshold', rho, Decimal(rho.numerator) / Decimal(rho.denominator))
if __name__ == '__main__':
    main()
