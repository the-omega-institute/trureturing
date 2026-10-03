#!/usr/bin/env python3
"""Exact32-vertex source with thresholds(2,4,6,8,8,12).

Reuses the pinned ordinary hinge geometry from Schroeder, Nine Prime Divisors
in Odd Distinct Covering Systems, edition1.0.1, DOI10.5281/zenodo.22759614.
All finite table integrity and rational arithmetic checks remain active under
Python -O. The inherited geometric maxima are not regenerated here; neither
ordinary all-height reduction nor Lean verification is performed by this code.
"""
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha256
from itertools import product
from math import prod
from collections import defaultdict
import argparse,json

SOURCE_PIN='0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1'
PS=(7,13,17,19,23,29)
TS=(2,4,4,8,8,12)
CAPS=tuple(Q(p-1,p-1-t) for p,t in zip(PS,TS))
RATIOS=tuple(sorted({Q(t,m) for t in TS for m in range(1,t)}))
MODS=(3,9,27,5,15,45)
SOURCE_ENVELOPES={}

def require(p, msg):
    if not p:
        raise ValueError(msg)

def ceil10(x):
    require(x >= 0, 'negative cost')
    return Q((x.numerator * 10 ** 10 + x.denominator - 1) // x.denominator, 10 ** 10)

def moments(p, positive, N):
    if not positive:
        return ([(0, Q(1))], (Q(1), Q(0)), (Q(0), Q(0)))
    kept = [(i, Q(p - 1, p ** (i + 1))) for i in range(1, N)]
    full = (Q(1, p), Q(1, p - 1))
    tail = (Q(1, p ** N), Q(1, p ** N) * (N + Q(1, p - 1)))
    require(tuple((sum((w * i ** k for i, w in kept)) + tail[k] for k in range(2))) == full, 'depth moments')
    return (kept, full, tail)

def linear(cells, weights, m3, m5):
    cap = [max((sum((w for x, w in zip(cells, weights) if x % d == r)) for r in range(d))) for d in MODS]
    a, u = m3
    b, v = m5
    return a * b * (sum(weights) + sum(cap)) + u * b * cap[2] + a * v * sum(cap[3:]) + (a + u) * (b + v) * max(weights)

def source_rows(geometry):
    raw = geometry.read_bytes()
    require(sha256(raw).hexdigest() == SOURCE_PIN, 'source geometry hash')
    geo = json.loads(raw)
    cache = geo['batches']
    seen = {}
    reads = 0
    dist = []
    table = {1: Q(1)}
    mean = Q(1)
    for p, C in zip(PS, CAPS):
        dist.append((dict(table), mean))
        nxt = defaultdict(Q)
        for m, w in table.items():
            for x in range(m, 32, m):
                n = x // m
                probability = 1 - C / p if n == 1 else C * Q(p - 1, p ** n)
                require(probability >= 0, 'multiplier mass')
                nxt[x] += w * probability
        table = nxt
        mean *= 1 + C / Q(p - 1)
    rows = {}
    for a, b in product((1, 2), (2, 4)):
        cells = [x for x in range(135) if x % 3 and x % 9 != 1 and (x % 27 != b) and x % 5 and (x % 15 != a)]
        for c, j in product((a, 3 - a), range(1, 5)):
            mass = Q(0)
            whole = Q(0)
            values = {t: Q(0) for t in RATIOS}
            for p3, p5 in product((False, True), repeat=2):
                ws = [(1 if p3 else 4) * (1 if p5 else 16 - 4 * (x % 5 == c) - (x % 5 == j)) for x in cells]
                labels = []
                payload = [str(len(cells))] + [f'{x} {w} 0' for x, w in zip(cells, ws)]
                for u, v in product(range(1, 12) if p3 else [0], range(1, 9) if p5 else [0]):
                    for t in RATIOS:
                        d = t.denominator
                        labels.append((u, v, t, d))
                        cs = [d, d, d * (1 + u), d * (1 + v), d * (1 + v), d * (1 + v), d * (1 + u) * (1 + v)]
                        payload.append(' '.join(map(str, [len(labels) - 1, d, d, *cs, t.numerator])))
                key = sha256(('\n'.join(payload) + '\n').encode()).hexdigest()
                record = cache[key]
                arr = record['integer_maxima']
                require(sha256((json.dumps(arr, separators=(',', ':')) + '\n').encode()).hexdigest() == record['cache_file_sha256'], 'hinge data hash')
                require(len(arr) == len(labels), 'hinge row count')
                seen[key] = len(arr)
                reads += len(arr)
                values_at = {}
                for idx, (row, lab) in enumerate(zip(arr, labels)):
                    u, v, t, d = lab
                    require(len(row) == 3 and row[:2] == [idx, d] and (0 <= row[2] < 2 ** 30), 'hinge row label')
                    values_at[u, v, t] = Q(row[2], d)
                us, um, ut = moments(3, p3, 12)
                vs, vm, vt = moments(5, p5, 9)
                ur = tuple((x - y for x, y in zip(um, ut)))
                scale = Q(1, (1 if p3 else 6) * (1 if p5 else 20))
                mass += scale * um[0] * vm[0] * sum(ws)
                whole += scale * linear(cells, ws, um, vm)
                remainder = linear(cells, ws, ut, vm) + linear(cells, ws, ur, vt)
                for t in RATIOS:
                    values[t] += scale * (sum((wu * wv * values_at[u, v, t] for u, wu in us for v, wv in vs)) + remainder)
            gamma = 3 * (a == 1) + (b % 3 == a % 3)
            reserve = Q(135, 4) + gamma + (9 - gamma) * (Q(c == a, 5) + Q(j == a, 20))
            SOURCE_ENVELOPES[a, b, c, j] = (mass, whole, dict(values), reserve)
            costs = []
            for p, t, (tab, mean) in zip(PS, TS, dist):
                small = {m: w for m, w in tab.items() if m < t}
                below = sum(small.values(), Q(0))
                first = sum((m * w for m, w in small.items()), Q(0))
                numerator = sum((m * w * values[Q(t, m)] for m, w in small.items()), Q(0)) + (mean - first) * whole - t * (1 - below) * mass
                costs.append(ceil10(numerator / (p - 1 - t)))
            live = (reserve - sum(costs, Q(0))) / 135
            require(live > 0, 'source positivity')
            rows[a, b, c, j] = live
    require(len(seen) == 72 and reads == 51840, f'source inherited dimensions: {len(seen)}, {reads}')
    require(min(rows.values()) == Q(10237584019, 168750000000), 'source minimum')
    return rows

def changed_source():
    thresholds = (2, 4, 6, 8, 8, 12)
    caps = tuple((Q(p - 1, p - 1 - t) for p, t in zip(PS, thresholds)))
    factors = tuple((1 + C * Q(3 * p - 1, (p - 1) ** 2) for p, C in zip(PS, caps)))
    table = {1: Q(1)}
    mean = Q(1)
    dist = []
    for p, C in zip(PS, caps):
        dist.append((dict(table), mean))
        nxt = defaultdict(Q)
        for m, w in table.items():
            for new in range(m, 12, m):
                n = new // m
                prob = 1 - C / p if n == 1 else C * Q(p - 1, p ** n)
                require(prob >= 0, 'negative new multiplier probability')
                nxt[new] += w * prob
        table = nxt
        mean *= 1 + C / (p - 1)
    masses = {}
    records = []
    for key, (mass, whole, values, reserve) in sorted(SOURCE_ENVELOPES.items()):
        costs = []
        for p, t, (tab, mean) in zip(PS, thresholds, dist):
            small = {m: w for m, w in tab.items() if m < t}
            require(all((Q(t, m) in values for m in small)), 'unavailable new hinge query')
            below = sum(small.values(), Q(0))
            first = sum((m * w for m, w in small.items()), Q(0))
            numerator = sum((m * w * values[Q(t, m)] for m, w in small.items()), Q(0)) + (mean - first) * whole - t * (1 - below) * mass
            costs.append(ceil10(numerator / (p - 1 - t)))
        live = (reserve - sum(costs, Q(0))) / 135
        require(live > 0, 'new source positivity')
        masses[key] = live
        records.append({'vertex': key, 'reserve_cell_units': str(reserve), 'costs_cell_units': list(map(str, costs)), 'mass_lower': str(live)})
    require(prod(caps) == Q(891, 50), 'new density cap')
    require(prod(factors) == Q(16535399, 2580480), 'new Gamma transfer')
    return (masses, records, thresholds, caps, factors)

def calculate(geometry=None):
    if geometry is None:
        geometry = Path(__file__).resolve().parent.parent / 'finite-prefix-sources/six_prime_prefix_geometry.json'
    SOURCE_ENVELOPES.clear()
    source_rows(geometry)
    masses,rows,thresholds,caps,factors=changed_source()
    minimum=min(masses.values());worst=[k for k,m in masses.items() if m==minimum]
    require(len(rows)==32,'vertex count')
    require(minimum==Q(89120862071,1350000000000),'new uniform source mass')
    require(all(1<=t<=p-2 for p,t in zip(PS,thresholds)),'kernel threshold conditions')
    require(all(C<p and C*(1-Q(1,p-1))>=1 for p,C in zip(PS,caps)),'kernel cap conditions')
    required17=[Q(6,m) for m in range(1,6)]
    require(all(x==Q(12,2*m) and x in RATIOS for m,x in enumerate(required17,1)),'17 query reuse')
    gamma=Q(65,16)*prod(factors)
    output={'scope':'Finite distinct odd numerical moduli on reference3,5,7,13,17,19,23,29, arbitrary original finite heights/residues/supports. Exact arithmetic source supplier; ordinary completion/comparison and inherited geometry maxima are supplied premises. No Lean verification.',
        'source_archive_sha256':'9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c',
        'source_geometry_sha256':SOURCE_PIN,'inherited_hinge_batches':72,'inherited_hinge_reads':51840,
        'geometry_search_reexecuted':False,'reference_primes':[3,5,*PS],
        'later_primes':PS,'thresholds':thresholds,'caps':list(map(str,caps)),
        'loss_denominators':[p-1-t for p,t in zip(PS,thresholds)],
        'required17_hinge_ratios':list(map(str,required17)),
        'interpolation_used':False,'source_vertex_count':32,'source_rows':rows,
        'uniform_source_mass_lower':str(minimum),'worst_vertices':worst,
        'joint_density_cap':str(prod(caps)),'later_Gamma_factors':list(map(str,factors)),
        'later_Gamma_product':str(prod(factors)),
        'product_query_Gamma_upper':str(gamma),
        'distorted_not_Haar_mass':True,'lean_verification':False}
    return output

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geometry', type=Path)
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(args.geometry), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    else:
        require(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
                'Retained source result matches complete recomputation')
    print(json.dumps({k:result[k] for k in ('source_vertex_count',
                     'uniform_source_mass_lower', 'joint_density_cap',
                     'product_query_Gamma_upper', 'lean_verification')}, indent=2))
