"""Simultaneous reference/anchor orbit audit for the fixed mixed-prime interface.

Checks actual prefix-tree maps, shared legal45/75 transport and individual
reserve credits. Infinite source transport is the accompanying ordinary proof.
"""
from pathlib import Path
from itertools import product
from collections import Counter, defaultdict
from fractions import Fraction as F
import importlib.util

def need(ok, message):
    if not ok:
        raise ValueError(message)

def swap(v, x, y):
    return y if v == x else x if v == y else v

def rep3(b):
    if b % 9 == 1:
        return 1
    if b == 4:
        return 4
    if b % 9 == 7:
        return 7
    need(b in (13, 22), 'orbit invariant: b in (13, 22)')
    return 13

def map3(a3, b3):
    target = rep3(b3)
    out = []
    for x in range(27):
        r = x % 3
        d = x // 3 % 3
        e = x // 9
        nd, ne = (d, e)
        if r == 2:
            nd = swap(d, a3 // 3 % 3, 0)
            if x % 9 == a3 % 9:
                ne = swap(e, a3 // 9, 0)
        if r == 1 and x % 9 == b3 % 9:
            ne = swap(e, b3 // 9, target // 9)
        out.append(r + 3 * nd + 9 * ne)
    need(out[a3] == 2 and out[b3] == target, 'orbit invariant: out[a3] == 2 and out[b3] == target')
    return tuple(out)

def map5(a5, b5):
    ar, br = (a5 % 5, b5 % 5)
    need(ar and br and (ar != br), 'orbit invariant: ar and br and (ar != br)')
    roots = list(range(5))
    other = [r for r in (ar, br) if r in (3, 4)]
    if other and other[0] == 4:
        roots[3], roots[4] = (4, 3)
    leaves = {}
    for v in (a5, b5):
        r = v % 5
        d = v // 5
        target = (0 if d == 0 else 1) if r == 1 else 0
        leaves[r] = (d, target)
    out = []
    for x in range(25):
        r = x % 5
        d = x // 5
        if r in leaves:
            d = swap(d, *leaves[r])
        out.append(roots[r] + 5 * d)
    return tuple(out)

def prefix_audit(m, p, E):
    need(sorted(m) == list(range(p ** E)), 'orbit invariant: sorted(m) == list(range(p ** E))')
    for e in range(E + 1):
        modulus = p ** e
        for x in range(p ** E):
            need(m[x] % modulus == m[x % modulus] % modulus, 'orbit invariant: m[x] % modulus == m[x % modulus] % modulus')

def preserves(m, p, E, residue, depth):
    modulus = p ** depth
    need(all(((x % modulus == residue) == (m[x] % modulus == residue) for x in range(p ** E))), 'orbit invariant: all(((x % modulus == residue) == (m[x] % modulus == residue) for x in range(p ** E)))')

def crt(x, m, y, n):
    return next((z for z in range(x, m * n, m) if z % n == y))

def audit(input_dir):
    BASE = Path(input_dir)
    spec = importlib.util.spec_from_file_location('e7_classes', BASE / 'all_first_root_source_types.py')
    a = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(a)
    maps3 = {}
    maps5 = {}
    for aa, bb in product(range(2, 27, 3), range(1, 27, 3)):
        m = map3(aa, bb)
        prefix_audit(m, 3, 3)
        for residue, depth in ((0, 1), (1, 2), (4, 3), (1, 1), (2, 1)):
            preserves(m, 3, 3, residue, depth)
        maps3[aa, bb] = m
    allowed5 = [x for x in range(25) if x % 5]
    for aa, bb in product(allowed5, repeat=2):
        if aa % 5 == bb % 5:
            continue
        m = map5(aa, bb)
        prefix_audit(m, 5, 2)
        for residue, depth in ((0, 1), (1, 2), (1, 1), (2, 1)):
            preserves(m, 5, 2, residue, depth)
        maps5[aa, bb] = m
    mass, vectors, classes = a.classes(2, 4, 1)
    need(mass == F(221, 675) and len(classes) == 44, 'orbit invariant: mass == F(221, 675) and len(classes) == 44')
    index = {v: i for i, v in enumerate(vectors)}
    c3A = tuple((x for x in range(27) if x % 3 == 2))
    c3B = tuple((x for x in range(27) if x % 3 == 1 and x % 9 != 1 and (x != 4)))
    c5A = tuple((x for x in range(25) if x % 5 and x != 1 and (x % 5 != 2)))
    c5B = tuple((x for x in range(25) if x % 5 and x != 1))
    s3A = {x: index[a.shell(3, 3, x, c3A)] for x in range(2, 27, 3)}
    s3B = {x: index[a.shell(3, 3, x, c3B)] for x in range(1, 27, 3)}
    s5 = {}
    others = {}
    for name, cells in (('A', c5A), ('B', c5B)):
        for v in allowed5:
            s5[name, v] = index[a.shell(5, 2, v, tuple((x for x in cells if x % 5 == v % 5)))]
        for aa, bb in maps5:
            vec = [F() for _ in range(a.MAX_FACTOR)]
            vec[1] = F(sum((x % 5 not in (aa % 5, bb % 5) for x in cells)), 25)
            others[name, aa, bb] = index[tuple(vec)]
    orbits = Counter()
    sig_to_orbit = defaultdict(set)
    orbit_to_sig = defaultdict(set)
    for (aa, bb), m3 in maps3.items():
        for (cc, dd), m5 in maps5.items():
            orbit = (m3[aa], m3[bb], m5[cc], m5[dd])
            sig = (s3A[aa], s3B[bb], s5['A', cc], s5['A', dd], others['A', cc, dd], s5['B', cc], s5['B', dd], others['B', cc, dd])
            orbits[orbit] += 1
            sig_to_orbit[sig].add(orbit)
            orbit_to_sig[orbit].add(sig)
    need(len(orbits) == 44 and sum(orbits.values()) == 24300, 'orbit invariant: len(orbits) == 44 and sum(orbits.values()) == 24300')
    need(set(sig_to_orbit) == set(classes), 'orbit invariant: set(sig_to_orbit) == set(classes)')
    need(all((len(x) == 1 for x in sig_to_orbit.values())) and all((len(x) == 1 for x in orbit_to_sig.values())), 'orbit invariant: all((len(x) == 1 for x in sig_to_orbit.values())) and all((len(x) == 1 for x in orbit_to_sig.values()))')
    for sig, meta in classes.items():
        orbit = next(iter(sig_to_orbit[sig]))
        need(orbit == tuple(meta['reference']), "orbit invariant: orbit == tuple(meta['reference'])")
        need(orbits[orbit] == meta['configuration_count'], "orbit invariant: orbits[orbit] == meta['configuration_count']")
    anchors = ((0, 3), (1, 9), (4, 27), (0, 5), (1, 25), (2, 15))
    A6 = tuple((n for n in range(675) if all((n % m != r for r, m in anchors))))
    F45 = tuple((r for r in range(45) if r % 3 and r % 9 != 1 and r % 5 and (r % 15 != 2)))
    F75 = tuple((r for r in range(75) if r % 3 and r % 5 and (r % 25 != 1) and (r % 15 != 2)))
    credit45 = {r: F(1, 45) - F(sum((n % 45 == r for n in A6)), 675) for r in F45}
    credit75 = {r: F(1, 75) - F(sum((n % 75 == r for n in A6)), 675) for r in F75}
    map45 = set()
    map75 = set()
    for m3 in set(maps3.values()):
        for m5 in set(maps5.values()):
            u = tuple((crt(m3[r % 9] % 9, 9, m5[r % 5] % 5, 5) for r in range(45)))
            v = tuple((crt(m3[r % 3] % 3, 3, m5[r % 25], 25) for r in range(75)))
            map45.add(u)
            map75.add(v)
    for m in map45:
        need(sorted(m) == list(range(45)) and set((m[r] for r in F45)) == set(F45), 'orbit invariant: sorted(m) == list(range(45)) and set((m[r] for r in F45)) == set(F45)')
        need(all((credit45[r] == credit45[m[r]] for r in F45)), 'orbit invariant: all((credit45[r] == credit45[m[r]] for r in F45))')
    for m in map75:
        need(sorted(m) == list(range(75)) and set((m[r] for r in F75)) == set(F75), 'orbit invariant: sorted(m) == list(range(75)) and set((m[r] for r in F75)) == set(F75)')
        need(all((credit75[r] == credit75[m[r]] for r in F75)), 'orbit invariant: all((credit75[r] == credit75[m[r]] for r in F75))')
    out = {'scope': __doc__, 'ordered_configurations': 24300, 'actual_stabilizer_orbits': 44, 'weight_class_partition_equals_actual_orbit_partition': True, 'canonical_representatives_match_existing_classes_exactly': True, 'A3_multiplicity': 9, 'B3_orbits': [[1, 10, 19], [4], [7, 16, 25], [13, 22]], 'quinary_representatives': [[*k, v] for k, v in sorted(Counter(((m[aa], m[bb]) for (aa, bb), m in maps5.items())).items())], 'orbits': [{'reference': list(k), 'configuration_count': v} for k, v in sorted(orbits.items())], 'legal45_count': len(F45), 'legal75_count': len(F75), 'legal_pairs': len(F45) * len(F75), 'distinct_projected45_maps': len(map45), 'distinct_projected75_maps': len(map75), 'all_projected_maps_preserve_legal_phases_and_each_credit': True, 'ternary_maps': [{'reference': list(k), 'image_reference': [2, rep3(k[1])], 'map_mod27': list(v)} for k, v in maps3.items()], 'quinary_maps': [{'reference': list(k), 'image_reference': [v[k[0]], v[k[1]]], 'map_mod25': list(v)} for k, v in maps5.items()], 'boundary': 'This module checks finite simultaneous orbit transport. Per-representative source comparisons and infinite source/selector transport are separate mathematical obligations, not Lean verification.'}
    return out
