#!/usr/bin/env python3
"""Exact common-source certificates for six fixed pair-activation patterns.

All certificate weights are fixed dyadic rationals. No numerical optimizer,
external Python package, prior exploratory artifact or inherited head scan is
needed. The accompanying proof supplies the all-height and phase quantifiers.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

OUTSIDE = (7, 11, 13, 17, 19)
CORE = (3, 5) + OUTSIDE
EDGES = tuple(combinations(range(5), 2))
EDGE_MASKS = tuple((1 << i) | (1 << j) for i, j in EDGES)
MATCHINGS = tuple((e, f) for e, f in combinations(range(10), 2)
                 if not EDGE_MASKS[e] & EDGE_MASKS[f])
OUTSIDE_TYPES = ((1, 1), (2, 1), (1, 2))
STAR_COLUMNS = (1, 2, 3, 3, 3)
THETA_DENOMINATOR = 2**24
SOURCE_JSON_SHA256 = '0cfa07bd80c2f5f5b753669c7a13be74a3c0c89d1bb6e822cdba8d26636bdc4c'
SOURCE_PRODUCER_SHA256 = 'e4466a57f5ad969b6a9f71c3bfbf1b6209303517c1f57bfe1ca12ffd62907898'
ENTRY_JSON_SHA256 = '2312048ed43413f9a64e37ddd94faa9958e78b67bc5f8fbee4fc4605d3fb933c'
ENTRY_PRODUCER_SHA256 = '7e8ab9bd5071e6434928083864a362c5634b18345caf38228f9b05af5f179186'
EXTRA_TEN_PATTERNS = ('concentrated_00', 'concentrated_12',
                      'cyclic_roles', 'separated_roles')

# Each row gives one retained mod9 leaf and its twenty mod25 leaves.
# The six matrices are sufficient witnesses, not claims of optimality.
THETA_NUMERATORS = {
    'concentrated_00': (
        (0, 0, 0, 0, 0, 14796581, 14796581, 14796581, 14796581, 13939041, 0, 15220134, 16777216, 15220134, 15220134, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13939041, 14796581, 13939041, 13939041, 14796581, 0, 15220134, 16777216, 15220134, 15220134, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 14796581, 13939041, 14796581, 14796581, 14796581, 0, 15220134, 16777216, 15220134, 15220134, 16777216, 16777216, 16777216, 16777216, 16777216),
        (14513124, 14513124, 14513124, 14513124, 14513124, 14079479, 14079479, 14079479, 14079479, 14079479, 0, 12886242, 16777216, 12886242, 12886242, 16092671, 16092671, 16092671, 16092671, 16092671),
        (9300297, 8127825, 9300297, 9300297, 9300297, 10211544, 10211544, 10211544, 10211544, 10211544, 0, 7497752, 12886242, 7497752, 7497752, 10193413, 10193413, 10193413, 10193413, 10193413),
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ),
    'concentrated_01': (
        (0, 0, 0, 0, 0, 13623004, 13623004, 13623004, 13623004, 9734659, 0, 13185957, 15597228, 13185957, 13185957, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 0, 13623004, 10374059, 0, 13623004, 0, 13185957, 15597228, 13185957, 13185957, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13623004, 10374059, 13623004, 13623004, 13623004, 0, 13185957, 15597228, 13185957, 13185957, 16777216, 16777216, 16777216, 16777216, 16777216),
        (12180818, 12180818, 12180818, 12180818, 12160688, 12780724, 12780724, 12780724, 12780724, 12780724, 0, 11200751, 14971747, 11200751, 11200751, 14384606, 14384606, 14384606, 14384606, 14384606),
        (7318049, 6745112, 7318049, 7318049, 7318049, 9793496, 9793496, 9793496, 9793496, 9793496, 0, 6618543, 11375163, 6618543, 6618543, 9086308, 9086308, 9086308, 9086308, 9086308),
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ),
    'concentrated_12': (
        (0, 0, 0, 0, 0, 13688294, 13688294, 13688294, 13688294, 13688294, 0, 14965349, 16777216, 14965349, 14965349, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13688294, 13688294, 13688294, 13688294, 13688294, 0, 14965349, 16777216, 14965349, 14965349, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13688294, 13688294, 13688294, 13688294, 13688294, 0, 14965349, 16777216, 14965349, 14965349, 16777216, 16777216, 16777216, 16777216, 16777216),
        (13481469, 13481469, 13481469, 13481469, 13481469, 13983010, 13983010, 13983010, 13983010, 13983010, 0, 13935303, 0, 13935303, 13935303, 16106345, 16106345, 16106345, 16106345, 16106345),
        (7745676, 7745676, 7745676, 7745676, 7745676, 9990644, 9990644, 9990644, 9990644, 9990644, 0, 9397830, 13935303, 9397830, 9397830, 9867433, 9867433, 9867433, 9867433, 9867433),
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ),
    'endpoint_star': (
        (0, 0, 0, 0, 0, 13054334, 13054334, 12886131, 12886131, 12549723, 0, 13151379, 15251775, 13151379, 13151379, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 12549723, 13054334, 13054334, 12717927, 13054334, 0, 13151379, 15251775, 13151379, 13151379, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13054334, 12549723, 12717927, 13054334, 13054334, 0, 13151379, 15251775, 13151379, 13151379, 16777216, 16777216, 16777216, 16777216, 16777216),
        (11895999, 11895999, 11895999, 11895999, 11895999, 12260904, 12260904, 12260904, 12260904, 12260904, 0, 11353522, 15123789, 11353522, 11353522, 14886866, 14886866, 14886866, 14886866, 14886866),
        (7324385, 5889223, 7324385, 7324385, 7324385, 8892570, 8892570, 8892570, 8892570, 8892570, 0, 6802809, 11353522, 6802809, 6802809, 9802737, 9802737, 9802737, 9802737, 9802737),
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ),
    'cyclic_roles': (
        (0, 0, 0, 0, 0, 13964659, 13964659, 13964659, 13964659, 13964659, 0, 14793732, 16777216, 14793732, 14793732, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13964659, 13964659, 13964659, 13964659, 13964659, 0, 14793732, 16777216, 14793732, 14793732, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13964659, 13964659, 13964659, 13964659, 13964659, 0, 14793732, 16777216, 14793732, 14793732, 16777216, 16777216, 16777216, 16777216, 16777216),
        (13831727, 13831727, 13831727, 13831727, 13708842, 13752606, 13752606, 13752606, 13752606, 13752606, 0, 12633634, 16532146, 12633634, 12633634, 15886759, 15886759, 15886759, 15886759, 15886759),
        (8588286, 5578758, 8588286, 8588286, 8588286, 10112310, 10112310, 10112310, 10112310, 10112310, 0, 7719095, 12707421, 7719095, 7719095, 9807898, 9807898, 9807898, 9807898, 9807898),
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ),
    'separated_roles': (
        (0, 0, 0, 0, 0, 13549103, 13549103, 13549103, 13549103, 13549103, 0, 14735754, 16777216, 14735754, 14735754, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13549103, 13549103, 13549103, 13549103, 13549103, 0, 14735754, 16777216, 14735754, 14735754, 16777216, 16777216, 16777216, 16777216, 16777216),
        (0, 0, 0, 0, 0, 13549103, 13549103, 13549103, 13549103, 13549103, 0, 14735754, 16777216, 14735754, 14735754, 16777216, 16777216, 16777216, 16777216, 16777216),
        (13252000, 13252000, 13252000, 13252000, 13252000, 13648738, 13648738, 13648738, 13648738, 13648738, 0, 13262928, 3738955, 13262928, 13262928, 15721313, 15721313, 15721313, 15721313, 15721313),
        (7615955, 7615955, 7615955, 7615955, 7615955, 9823325, 9823325, 9823325, 9823325, 9823325, 0, 7941497, 13262928, 7941497, 7941497, 9702178, 9702178, 9702178, 9702178, 9702178),
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    ),
}

class Checks:
    def __init__(self):
        self.predicates = {}
        self.evaluations = 0

    def require(self, name, condition):
        self.evaluations += 1
        if not condition:
            raise ArithmeticError(name)
        self.predicates[name] = True


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def inherited(source, checks):
    raw = source.read_bytes()
    obj = json.loads(raw)
    producer_hash = sha256(source.with_suffix('.py').read_bytes()).hexdigest()
    checks.require('pinned_source_json', sha256(raw).hexdigest() == SOURCE_JSON_SHA256)
    checks.require('pinned_source_producer', producer_hash == SOURCE_PRODUCER_SHA256
                   == obj['producer_sha256'])
    checks.require('source_recorded_checks', bool(obj['checks'])
                   and all(v is True for v in obj['checks'].values()))
    constants = obj['constants']
    c = F(constants['continuation_c'])
    density = F(constants['source_density_D'])
    multiplier = F(constants['continuation_density_multiplier'])
    checks.require('inherited_continuation_constants',
                   c == F(1084133, 201247200) and density == F(3458, 405)
                   and multiplier == F(200, 33))
    return c, density, multiplier, dict(file=source.name,
                                      sha256=sha256(raw).hexdigest(),
                                      producer_sha256=producer_hash,
                                      inherited_checks=len(obj['checks']),
                                      inherited_head_scan_rerun=False)


def central_source(checks):
    pure3 = ((3, 2), (9, 7), (27, 4), (81, 13), (243, 40), (729, 121))
    pure5 = ((5, 4), (25, 2))
    survivor3 = [x for x in range(729) if all(x % m != a for m, a in pure3)]
    checks.require('actual_ternary_survivor_count', len(survivor3) == 365)
    w = [F(sum(x % 9 == i + 3*t for x in survivor3), len(survivor3))
         for i, t in product(range(2), range(3))]
    density3 = F(729, len(survivor3))
    checks.require('actual_ternary_leaf_masses', w == [F(n, 365)
                   for n in (81, 81, 81, 81, 41, 0)])
    v, density5 = [], []
    for j in range(4):
        survivors = [x for x in range(25) if x % 5 == j
                     and all(x % m != a for m, a in pure5)]
        checks.require('positive_quinary_root_survivors', bool(survivors))
        density5.append(F(25, 4*len(survivors)))
        v.extend(F(1, 4*len(survivors)) if j+5*t in survivors else F()
                 for t in range(5))
    checks.require('actual_quinary_density_references',
                   density5 == [F(5, 4), F(5, 4), F(25, 16), F(5, 4)])
    checks.require('central_sources_are_probabilities', sum(w) == sum(v) == 1
                   and min(w+v) >= 0)
    checks.require('old_density_envelope_retained', density3 < 2
                   and max(density5) < F(5, 3))
    return w, v, density3, density5, dict(pure3=pure3, pure5=pure5,
        leaf_index3='l=3i+t represents i+3t modulo9',
        leaf_index5='m=5j+t represents j+5t modulo25',
        ternary_survivor_count=len(survivor3),
        masses3=w, masses5=v, density3=density3, density5_by_root=density5)


def retained_inventory(checks):
    retained = {}

    def put(mapping, kind):
        exps = tuple(mapping.get(p, 0) for p in CORE)
        checks.require('retained_exponents_distinct', exps not in retained)
        retained[exps] = kind

    put({3: 1, 5: 1}, 'central15')
    for q in OUTSIDE:
        for a, b, e in ((1,0,1), (0,1,1), (1,1,1), (1,0,2), (0,1,2)):
            put({3:a, 5:b, q:e}, 'old_star')
        put({3:2, q:1}, 'new9q')
        put({5:2, q:1}, 'new25q')
    for q, r in combinations(OUTSIDE, 2):
        for eq, er in OUTSIDE_TYPES:
            for a, b in product(range(2), repeat=2):
                put({3:a, 5:b, q:eq, r:er}, 'pair')
    rows = [dict(exponents=e, modulus=prod(p**a for p, a in zip(CORE, e)),
                 kind=kind) for e, kind in retained.items()]
    rows.sort(key=lambda r:r['modulus'])
    checks.require('retained156_and_pair120', len(rows) == 156
                   and sum(r['kind'] == 'pair' for r in rows) == 120)
    checks.require('retained_numerical_labels_distinct',
                   len({r['modulus'] for r in rows}) == 156)
    checks.require('ten_new_support_two_stars',
                   sum(r['kind'] in ('new9q', 'new25q') for r in rows) == 10)
    return retained, rows


def coefficient_arrays(retained, checks):
    loss, weighted = [F() for _ in range(512)], [F() for _ in range(512)]
    buckets = 0
    for powers in product(range(4), repeat=7):
        support = sum(e > 0 for e in powers)
        if support <= 1 or powers in retained:
            continue
        if not (max(powers) >= 3 or max(powers[:2]) <= 1 or support >= 5):
            continue
        mask = sum(1 << j for j, e in enumerate(powers[2:]) if e)
        weight = F(1, 9) if powers[0] == 3 else F(1)
        if powers[1] == 3:
            weight *= F(1, 60)
        for q, e in zip(OUTSIDE, powers[2:]):
            weight *= (F(1), F(1, q-1), F(1, q*(q-2)),
                       F(1, q*(q-1)*(q-2)))[e]
        loss[(4*powers[0]+powers[1])*32+mask] += weight
        buckets += 1
    for e3, e5, mask in product(range(4), range(4), range(32)):
        if e3 == e5 == mask == 0:
            continue
        weight = (F(1), F(3), F(5), F(8,9))[e3]
        weight *= (F(1), F(3), F(5), F(1,8))[e5]
        for j, q in enumerate(OUTSIDE):
            if mask >> j & 1:
                weight *= F(3, q-1) + F(5*q-3, (q-2)*(q-1)**2)
        weighted[(4*e3+e5)*32+mask] = weight
    checks.require('512_nonnegative_complete_coefficients',
                   len(loss) == len(weighted) == 512 and min(loss+weighted) >= 0)
    checks.require('unit_query_excluded_from_nonunit_weight', weighted[0] == 0)
    return loss, weighted, buckets


def pattern_roles(name):
    roles = []
    for edge_index, (i, j) in enumerate(EDGES):
        edge = []
        for t in range(3):
            if name.startswith('concentrated_'):
                row, column = map(int, name.rsplit('_', 1)[1])
                point = (row, column)
            elif name == 'endpoint_star':
                row, column = 0, STAR_COLUMNS[j]
                point = (0, STAR_COLUMNS[j])
            elif name == 'cyclic_roles':
                row, column = (edge_index+t) % 2, (2*edge_index+t) % 4
                point = ((edge_index+t+1) % 2, (edge_index+2*t+1) % 4)
            elif name == 'separated_roles':
                row, column, point = 1, 2, (0, (edge_index+t) % 4)
            else:
                raise ValueError(name)
            edge.append(dict(row=row, column=column, point=point))
        roles.append(edge)
    return roles


def actual_phase_examples(roles, checks, name):
    rows = []
    for edge, (i, j) in enumerate(EDGES):
        q, r = OUTSIDE[i], OUTSIDE[j]
        for t, (eq, er) in enumerate(OUTSIDE_TYPES):
            role = roles[edge][t]
            for kind in ('unconditional', 'row', 'column', 'point'):
                parts = [(q**eq, 0), (r**er, 0)]
                if kind == 'row':
                    parts.append((3, role['row']))
                elif kind == 'column':
                    parts.append((5, role['column']))
                elif kind == 'point':
                    parts.extend(((3, role['point'][0]), (5, role['point'][1])))
                modulus = prod(m for m, _ in parts)
                residue = sum(a*(modulus//m)*pow(modulus//m, -1, m)
                              for m, a in parts) % modulus
                checks.require(name+'_CRT_realizes_fixed_roles',
                               all(residue % m == a for m, a in parts))
                rows.append(dict(modulus=modulus, residue=residue,
                                 central_role=kind))
    checks.require(name+'_120_actual_pair_labels', len(rows) == 120
                   and len({r['modulus'] for r in rows}) == 120)
    return rows


def star_factors(l, m):
    i, j = l//3, m//5
    return [1-(F(1,q-1)+F(1,q*(q-2)))*(int(i == 0)+int(j == column))
            -F(1,q-1)*int((i,j) == (0,column))
            -F(1,q-1)*int(l == 3)-F(1,q-1)*int(m == 12)
            for q, column in zip(OUTSIDE, STAR_COLUMNS)]


def pair_caps(roles, l, m):
    i, j = l//3, m//5
    caps = []
    for edge, (a, b) in enumerate(EDGES):
        q, r = OUTSIDE[a], OUTSIDE[b]
        weights = (F(1,(q-1)*(r-1)), F(1,q*(q-2)*(r-1)),
                   F(1,(q-1)*r*(r-2)))
        caps.append(sum(weight*(1+int(i == role['row'])
                               +int(j == role['column'])
                               +int((i,j) == tuple(role['point'])))
                        for weight, role in zip(weights, roles[edge])))
    return caps


def query_grids(roles, checks, name):
    G = [[F() for _ in range(120)] for _ in range(32)]
    H = [[F() for _ in range(120)] for _ in range(32)]
    z_values, disjoint_sums = [], []
    for l, m in product(range(6), range(20)):
        if l//3 == m//5 == 0:
            continue
        b = star_factors(l, m)
        checks.require(name+'_positive_star_factors', min(b) > 0)
        beta = pair_caps(roles, l, m)
        u = [beta[e]/(b[i]*b[j]) for e, (i,j) in enumerate(EDGES)]
        z = 1-sum(u)+sum(u[e]*u[f] for e,f in MATCHINGS)
        disjoint = max(sum(u[f] for f in range(10)
                           if not EDGE_MASKS[e] & EDGE_MASKS[f]) for e in range(10))
        checks.require(name+'_strict_induced_polynomial_region', z > 0 and disjoint < 1)
        z_values.append(z)
        disjoint_sums.append(disjoint)
        cell = 20*l+m
        for mask in range(32):
            G[mask][cell] = prod(b[q] for q in range(5) if not mask >> q & 1)
        for mask in range(32):
            H[mask][cell] = G[mask][cell] - sum(
                beta[e]*G[mask|EDGE_MASKS[e]][cell]
                for e in range(10) if not mask & EDGE_MASKS[e]) + sum(
                beta[e]*beta[f]*G[mask|EDGE_MASKS[e]|EDGE_MASKS[f]][cell]
                for e,f in MATCHINGS if not mask & (EDGE_MASKS[e]|EDGE_MASKS[f]))
            outside = [e for e in range(10) if not mask & EDGE_MASKS[e]]
            induced = 1-sum(u[e] for e in outside)+sum(
                u[e]*u[f] for e,f in MATCHINGS if e in outside and f in outside)
            checks.require(name+'_cavity_polynomial_identity',
                           H[mask][cell] == G[mask][cell]*induced)
            checks.require(name+'_positive_query_grids',
                           0 <= H[mask][cell] <= G[mask][cell])
        checks.require(name+'_exact_chosen_mass_grid', H[0][cell] == G[0][cell]*z)
    checks.require(name+'_all105_unmasked_cells_strict', len(z_values) == 105)
    return G, H, dict(strict_cells=len(z_values), central_masked_cells=15,
                     minimum_full_polynomial=min(z_values),
                     maximum_disjoint_sum=max(disjoint_sums))


def selectors(size, root_size, masses, deep_references, mode):
    if mode == 0:
        return [list(enumerate(masses))]
    if mode == 1:
        return [[(j, masses[j]) for j in range(k, k+root_size)]
                for k in range(0, size, root_size)]
    if mode == 2:
        return [[(j, masses[j])] for j in range(size)]
    return [[(j, deep_references[j//root_size])] for j in range(size)]


def exact_gate(G, H, theta, loss, weighted, w, v, density3, density5, c):
    s3 = [selectors(6, 3, w, [density3/2]*2, mode) for mode in range(4)]
    s5 = [selectors(20, 5, v, [3*d/5 for d in density5], mode) for mode in range(4)]
    mass = sum(w[l]*v[m]*theta[20*l+m]*H[0][20*l+m]
               for l,m in product(range(6), range(20)))
    debit, query = F(), F()
    for e3,e5,mask in product(range(4),range(4),range(32)):
        index = (4*e3+e5)*32+mask
        if not (loss[index] or weighted[index]):
            continue
        screen = max(sum(a*b*theta[20*l+m]*H[mask][20*l+m]
                         for l,a in left for m,b in right)
                     for left in s3[e3] for right in s5[e5])
        debit += loss[index]*screen
        query += weighted[index]*screen
    return dict(chosen_pair_mass=mass, remaining_original_loss_upper=debit,
                weighted_nonunit_query_upper=query,
                gate_lower=(1-c)*(mass-debit)-c*query)


def branch_inputs(path, c, density, multiplier, checks):
    raw = path.read_bytes()
    data = json.loads(raw)
    producer = sha256(path.with_suffix('.py').read_bytes()).hexdigest()
    checks.require('pinned_entry_source_json', sha256(raw).hexdigest() == ENTRY_JSON_SHA256)
    checks.require('pinned_entry_source_producer', producer == ENTRY_PRODUCER_SHA256
                   == data['producer_sha256'])
    checks.require('entry_source_checks', bool(data['checks'])
                   and all(v is True for v in data['checks'].values()))
    constants = data['constants']
    checks.require('same_entry_continuation_constants',
                   F(constants['c']) == c and F(constants['density_D']) == density
                   and F(constants['continuation_multiplier']) == multiplier
                   and F(constants['early_pair_density']) == F(10,3))
    early = F(data['fee_tables']['3_5']['total_fee'])
    late = F(data['fee_tables']['3_23']['total_fee'])
    ordinary = F(data['consequence']['ordinary_attachment_fee'])
    checks.require('certified_entry_fee_thresholds', early < F(1,2600)
                   and late < F(1,125000) and ordinary == F(1,131072))
    return early, late, ordinary, dict(file=path.name, sha256=sha256(raw).hexdigest(),
        producer_sha256=producer, inherited_checks=len(data['checks']),
        inherited_entry_enumerator_rerun=False)


def support160_inventory(retained, checks):
    rows = []
    for central in (3,5):
        for triple in combinations(OUTSIDE,3):
            for heights in product((1,2),repeat=3):
                exps = {central:2, **dict(zip(triple,heights))}
                modulus = prod(q**e for q,e in exps.items())
                cap = F(2,9) if central == 3 else F(1,15)
                for q,e in zip(triple,heights):
                    cap *= F(1,q-1) if e == 1 else F(1,q*(q-2))
                vector = tuple(exps.get(q,0) for q in CORE)
                checks.require('support160_disjoint_from_retained', vector not in retained)
                rows.append(dict(modulus=modulus, exponents=vector, source_cap=cap))
    rows.sort(key=lambda row:row['modulus'])
    checks.require('support160_complete_distinct', len(rows) == 160
                   and len({row['modulus'] for row in rows}) == 160)
    cap = sum(row['source_cap'] for row in rows)
    independent = F(13,45)*sum(prod(F(1,q-1)+F(1,q*(q-2)) for q in triple)
                                for triple in combinations(OUTSIDE,3))
    checks.require('support160_exact_geometric_cap',
                   cap == independent == F(2261681116741,813717439920000))
    return rows, cap


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path,
                        default=Path(__file__).with_name('central_high_support_augmentation.json'))
    parser.add_argument('--entry-source', type=Path,
                        default=Path(__file__).with_name('staged_two_parent_attachment.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = Checks()
    c, density, multiplier, source = inherited(args.source, checks)
    w, v, density3, density5, source_record = central_source(checks)
    checks.require('complete_product_density_envelope',
                   2*F(5,3)*prod(F(q,q-2) for q in OUTSIDE) == density)
    checks.require('deep_original_cap_scaling', density3/2*F(1,9) == density3/18
                   and all(3*d/5*F(1,60) == d/100 for d in density5))
    checks.require('deep_query_cap_scaling', density3/2*F(8,9) == 4*density3/9
                   and all(3*d/5*F(1,8) == 3*d/40 for d in density5))
    early_fee, late_fee, ordinary_fee, entry_source = branch_inputs(
        args.entry_source, c, density, multiplier, checks)
    retained, inventory = retained_inventory(checks)
    support160, cap160 = support160_inventory(retained, checks)
    checks.require('actual_source_support160_caps', max(w) <= F(2,9)
                   and max(v) <= F(1,15))
    loss, weighted, buckets = coefficient_arrays(retained, checks)
    alpha = 1/(density*multiplier)
    checks.require('base_gate_to_Haar', alpha*F(11,1000) > F(1,5000))
    checks.require('extra_ten_gate_to_Haar', alpha*F(1,100) > F(1,5500))
    extra_fee = (max(w)+max(v))*sum(F(1,q*(q-2)) for q in OUTSIDE)
    checks.require('extra_ten_literal_cap_sum', extra_fee == F(6808439,454381200))
    coarse_combined = alpha*(F(1,100)-(1-c)*(cap160+F(1,780)))-F(1,125000)-ordinary_fee
    checks.require('combined_160_and_branches_simple_bound',
                   coarse_combined == F(1687238234614993717021,16948040294649784320000000)
                   and coarse_combined > F(1,11000))
    results = {}
    for name, matrix in THETA_NUMERATORS.items():
        theta = [F(x, THETA_DENOMINATOR) for row in matrix for x in row]
        checks.require(name+'_one_bounded_common_theta', len(matrix) == 6
                       and all(len(row) == 20 for row in matrix)
                       and len(theta) == 120 and min(theta) >= 0 and max(theta) <= 1)
        roles = pattern_roles(name)
        examples = actual_phase_examples(roles, checks, name)
        G, H, region = query_grids(roles, checks, name)
        checks.require(name+'_null_source_has_zero_theta',
                       all(not theta[20*l+m] for l,m in product(range(6),range(20))
                           if not G[0][20*l+m] or not w[l]*v[m]))
        value = exact_gate(G,H,theta,loss,weighted,w,v,density3,density5,c)
        checks.require(name+'_positive_exact_gate', value['gate_lower'] > F(11,1000))
        value['head_Haar_lower'] = alpha*value['gate_lower']
        value['strict_head_lower'] = F(1,5000)
        if name in EXTRA_TEN_PATTERNS:
            gate_after = value['gate_lower']-(1-c)*extra_fee
            checks.require(name+'_extra_ten_gate', gate_after > F(1,100))
            combined_gate = gate_after-(1-c)*(cap160+F(10,3)*early_fee)
            combined_head = alpha*combined_gate-late_fee-ordinary_fee
            checks.require(name+'_combined_support160_and_branches',
                           combined_head > coarse_combined > F(1,11000))
            combined = dict(support160_deletion_upper=cap160,
                            early_blocker_deletion_upper=F(10,3)*early_fee,
                            core_gate_before_continuation_lower=combined_gate,
                            late_blocker_fee_upper=late_fee, ordinary_branch_fee_upper=ordinary_fee,
                            extendible_head_lower=combined_head,
                            common_simple_head_lower=coarse_combined,
                            strict_head_lower=F(1,11000),
                            full_density_lower='1/(11000 Q_off)',
                            scope='Same fixed central roles; all160 one-central support-four labels; Report601 separated branches with entry q>=37')
            extra = dict(original_labels=[t*q*q for t in (9,25) for q in OUTSIDE],
                         residue_scope='Arbitrary globally fixed residues at all ten labels',
                         raw_source_deletion_upper=extra_fee,
                         gate_loss_upper=(1-c)*extra_fee,
                         gate_lower=gate_after, head_Haar_lower=alpha*gate_after,
                         strict_head_lower=F(1,5500), combined_extension=combined)
        else:
            extra = None
        results[name] = dict(roles=roles,
                            role_order=dict(outside_edges=[(OUTSIDE[i],OUTSIDE[j]) for i,j in EDGES],
                                            exponent_types=OUTSIDE_TYPES),
                            phase_examples=examples,
                            phase_examples_scope='Concrete realization only; theorem permits arbitrary outside components',
                            theta_numerators=matrix, theta_denominator=THETA_DENOMINATOR,
                            strict_region=region, consequence=value, extra_ten=extra)
    result = dict(schema='actual-pair-activation-certificate-v1', source=source,
                  scope=dict(head_primes=CORE+(23,29,31),
                             central_pure_inventory='Subset of the fixed listed pure3 and pure5 originals; no others',
                             retained_roles='Central15=0; fixed star columns1,2,3,3,3; new9q central1 mod9, new25q central12 mod25; one of six pair tables',
                             unspecified_phases='All outside components and remaining admitted original phases arbitrary and globally fixed',
                             remaining_inventory='Report598 head inventory; late23,29,31 originals unrestricted',
                             all_original_and_query_heights='Unbounded finite except the explicitly restricted pure3/pure5 inventory',
                             exact_certificate='Fixed bounded common dyadic theta; no optimality assertion',
                             excluded='Arbitrary central phases; unrestricted odd covering; arbitrary additional support',
                             lean_verified=False),
                  branch_source=entry_source,
                  central_source=source_record,
                  support160_inventory=support160,
                  constants=dict(continuation_c=c, source_density_D=density,
                                 continuation_multiplier=multiplier, Haar_factor=alpha),
                  retained_inventory=inventory,
                  complete_coefficients=dict(bucket_meaning='0=absent,1=first,2=second,3=all heights>=3',
                                             index='(4 e3+e5)*32+outside_support_mask',
                                             remaining_buckets=buckets,
                                             loss=loss, weighted_nonunit_query=weighted),
                  patterns=results, checks=checks.predicates,
                  predicate_evaluations=checks.evaluations,
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print(json.dumps(encode(dict(output=str(args.output), patterns=len(results),
                                extra_ten_patterns=len(EXTRA_TEN_PATTERNS),
                                checks=len(checks.predicates), evaluations=checks.evaluations,
                                min_gate=min(v['consequence']['gate_lower'] for v in results.values()),
                                head_strict_lower=F(1,5000), extra_ten_head_strict_lower=F(1,5500),
                                combined_head_strict_lower=F(1,11000)))))


if __name__ == '__main__':
    main()
