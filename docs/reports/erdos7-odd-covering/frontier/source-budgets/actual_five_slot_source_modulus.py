#!/usr/bin/env python3
"""Actual original-label slot perturbation and a corrected mean modulus.

Profile133 keeps all source parameters fixed while moving one original
pure5 cylinder from Q to H. Exact finite fixtures refute a Delta-only
slot modulus; a finite height9 source also refutes the sigma-only mean
claim. The replacement retains the same two shallow defect coordinates.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/actual_five_slot_source_modulus.json'
CELLS = (0, 3, 1, 4, 7)
SLOTS = (1, 2, 3, 0, 4)
ROOT = (0, 0, 1, 1, 1)
QSTAR = (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5))
ETA_STAR = (F(1, 18),)+(F(1, 9),)*4
WITNESS = (1, 2, 4, 0, 4, 1, 4)
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
    'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
    'frontier/comparison-bounds/complete_off_face_cost.py': '0d53ac6dc99eac6db322525d94375c498e61cb1c5cacd8776327c70d311306c8',
    'frontier/retained-transport/finite_source_face_transport.py': '04c99f1a0c6e1781734531923705863fbc9843c610f6d4933a81c89429aa5291',
    'frontier/retained-transport/joint_deep_mean_transport.py': 'efbb0825f227e5cc97a0fc24b71acf3e16a35f6b3db662f0e4b392afb8e3d0d0',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def source_labels(constructor, N, depth):
    require(N >= max(5, depth) and depth >= 4, 'Move one deep original label in the concentrated finite source')
    before = tuple(constructor.source_label(a, b, 398)
                   for a, b in product(range(N+1), repeat=2) if a+b)
    after = tuple((a, ra, b, 4) if a == 0 and b == depth else (a, ra, b, rb)
                  for a, ra, b, rb in before)
    old = 5**(depth-1)
    checks = 0
    for a, ra, b, rb in before:
        if b == 0 or (a == 0 and b == depth):
            continue
        modulus = 5**min(b, depth)
        require((old-rb) % modulus != 0 and (4-rb) % modulus != 0,
                'Both moved five cylinders avoid every other original positive-five source label')
        checks += 2
    require(len(before) == len({(a, b) for a, _, b, _ in before}) == (N+1)**2-1
            and sum(x != y for x, y in zip(before, after)) == 1,
            'Exactly one residue changes; every original modulus is retained')
    mixed_checks = 0
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0 or b == 0:
            continue
        _, aa, ra, bb, rb = constructor.mixed_label(a, b)
        modulus = 5**min(bb, depth)
        old_hits = (old-rb) % modulus == 0
        new_hits = (4-rb) % modulus == 0
        require(not old_hits and new_hits == (bb == 1), 'Only the original first-five mixed labels lose the new H slice')
        mixed_checks += 1
    return before, after, {'source_disjointness_checks': checks, 'mixed_label_checks': mixed_checks,
                           'source_label_count': len(before), 'full357_label_count': (N+1)**3-1,
                           'old_residue': old, 'new_residue': 4, 'original_modulus': 5**depth}


def grid_source(labels, N):
    """Independent literal residue-space unions, including assigned budgets."""
    A, B = 3**N, 5**N
    all5 = (1 << B)-1
    masks = {(b, rb): sum(1 << y for y in range(rb, B, 5**b)) for _, _, b, rb in labels}
    states, pure3, pure5 = [all5]*A, [True]*A, all5
    alpha_masks, beta_masks = [0]*3, [0]*9
    for a, ra, b, rb in labels:
        mask = masks[b, rb]
        for x in range(ra, A, 3**a):
            states[x] &= all5 ^ mask
            if b == 0:
                pure3[x] = False
        if a == 0:
            pure5 &= all5 ^ mask
        elif a == 1 and b > 0:
            alpha_masks[ra] |= mask
        elif a == 2 and b > 0:
            beta_masks[ra] |= mask
    eta = tuple(F(sum(pure3[x] for x in range(c, A, 9)), A) for c in CELLS)
    alpha = tuple(F((pure5 & alpha_masks[r]).bit_count(), B) for r in (0, 1))
    beta = tuple(F((pure5 & ~alpha_masks[c % 3] & beta_masks[c]).bit_count(), B) for c in CELLS)
    n, late = [], []
    for c in CELLS:
        raw = sum(states[x].bit_count() for x in range(c, A, 9))
        prelate = sum((pure5 & ~alpha_masks[x % 3] & ~beta_masks[x % 9]).bit_count()
                      for x in range(c, A, 9) if pure3[x])
        n.append(F(raw, A*B))
        late.append(F(prelate-raw, A*B))
    z = F(pure5.bit_count(), B)
    parameter = (tuple(1-9*v for v in eta), alpha, beta, tuple(late), z)
    slot_masks = tuple(sum(1 << y for y in range(slot, B, 5)) for slot in SLOTS)
    qslots = tuple(F((pure5 & sm).bit_count(), B) for sm in slot_masks)
    rawslots = tuple(F(sum((mask & sm).bit_count() for mask in states), A*B) for sm in slot_masks)
    h, h1 = sum(eta), sum(eta[2:])
    root1H = F(sum((states[x] & slot_masks[4]).bit_count() for x in range(1, A, 3)), A*B)
    require(rawslots[4] == max(rawslots), 'H remains an actual best first-five source slot')
    return {'parameter': parameter, 'eta': eta, 'n': tuple(n), 'raw_mass': sum(n), 'qslots': qslots,
            'rawslots': rawslots, 'r': h/5-rawslots[4], 'r1': h1/5-root1H,
            'literal_grid_size': A*B}


def head_weights(layout):
    r3, c9, s5, r15, s15, c45, s45 = layout
    I, J, c, K = int(r3 == 0), int(r15 == 0), int(c9 == 1), int(c45 == 1)
    weights = tuple(F(int(j == s5)+J*int(j == s15), 90)+F(K*int(j == s45), 135) for j in range(5))
    return weights, F(I, 90)+F(c, 135)


def corrected_mean_price(sigma, radius, eta, p, a, b, qslots, r, r1, layout, source_error):
    require(0 <= sigma <= radius <= F(2, 27), 'One fixed concentrated neighborhood radius')
    h0, h1, h = sum(eta[:2]), sum(eta[2:]), sum(eta)
    u = min(r/h, r1/h1, (r-r1)/h0)
    deltaA, deltaB, deltaH = (F(1, 5)-qslots[j] for j in (1, 2, 4))
    require(qslots[0] == 0 and 0 <= deltaA <= a and 0 <= deltaB <= b and 0 <= deltaH <= u
            and qslots[3] == F(3, 20)+p+deltaA+deltaB+deltaH,
            'Actual five-slot packing and exact conserved marginal')
    weights, zprice = head_weights(layout)
    r3, c9 = layout[:2]
    def A5(e):
        return ((1+r3)*(sum(e[:2]), sum(e[2:]))[r3]+(1+ROOT[c9])*e[c9])/100
    difference5 = A5(ETA_STAR)-A5(eta)
    exact = (difference5-p*(zprice+weights[3])+deltaA*(weights[1]-weights[3])
             +deltaB*(weights[2]-weights[3])+deltaH*(weights[4]-weights[3])+source_error)
    priceA, priceB, priceH = (max(weights[j]-weights[3], F(0)) for j in (1, 2, 4))
    refined = difference5+a*priceA+b*priceB+u*priceH+source_error
    sigma_part = F(299, 10800)*sigma
    uniform = sigma_part+F(4, 135)*u
    price12 = 90*priceH/(15-radius)
    price1 = 10*priceH
    require(sum(weights) <= F(4, 135) and priceA+priceB <= F(4, 135)
            and difference5 <= sigma/450 and source_error <= 13*sigma/720
            and exact <= refined <= uniform and price12 <= F(8)/(45-3*radius) and price1 <= F(8, 27),
            'Same-head signed identity and the explicit common-budget replacement prices')
    return {'exact_source_loss': exact, 'signed_head_upper': refined, 'uniform_upper': uniform,
            'best_slot_modulus': u, 'slot_H_price': priceH, 'added_E5_E15_price': price12,
            'added_first_shifted_coordinate_price': price1,
            'added_two_shifted_coordinate_price': price12}


def actual_case(constructor, actual, finite, source, mean, N, depth, literal):
    labels, moved, label_checks = source_labels(constructor, N, depth)
    base = actual.actual_398_case(finite, source, N)
    eps = F(1, 5**depth)
    parameter, dat, sigma = base['parameter'], base['dat'], base['sigma']
    d, n, eta, s, _ = dat
    h, h1, h0 = sum(eta), sum(eta[2:]), sum(eta[:2])
    r, r1 = h*eps, h1*eps
    qslots = list(base['qslots']); qslots[3] += eps; qslots[4] -= eps
    qslots = tuple(qslots)
    point = finite.source_point(parameter, base['pi'], r, 2, r1)
    require(point['d'] == d and point['n'] == n and point['eta'] == eta
            and r < F(1, 520) and min(r/h, r1/h1, (r-r1)/h0) == eps,
            'Unchanged actual source parameters, valid small-r packing and exact H modulus')
    grid = None
    if literal:
        before, after = grid_source(labels, N), grid_source(moved, N)
        require(before['parameter'] == after['parameter'] == parameter
                and before['eta'] == after['eta'] == eta and before['n'] == after['n'] == n
                and before['qslots'] == base['qslots'] and after['qslots'] == qslots
                and after['r'] == r and after['r1'] == r1,
                'Literal independent source unions verify every assigned budget and moved slot')
        grid = {'before': before, 'after': after}
    t = sum((F(1, 3**a) for a in range(3, N+1)), F(0))
    q = sum((F(1, 5**b) for b in range(1, N+1)), F(0))
    v7 = F(1, 7**N); u7, actual7 = (1-v7)/5, (1-v7)/(5+v7)
    H = F(4, 9)+t+q/9-t*q
    require(h+h1+F(1, 9)+t == 1, 'The complete changed mixed old-label mass is exactly epsilon')
    defects = dict(base['defects'])
    defects['E5'] += u7*h*eps
    defects['E15'] += u7*h1*eps
    defects['omega'] = (u7-actual7)*(H-eps)
    defects['rho'] += actual7*eps
    require(min(defects.values()) >= 0
            and sum(defects[k] for k in ('E5', 'E15', 'E3', 'E5d', 'E15d', 'omega')) <= defects['rho']
            and defects['E5'] >= r/5 and defects['E15'] >= r1/5,
            'One actual complete budget, including all missing old and seven depths')
    p, a, b = point['p'], point['a'], point['b']
    require(eps > p+a+b, 'The actual H marginal refutes the Delta-only modulus')
    radius, rstar = F(2, 27), F(1, 520)
    hs, es = F(1, 3)-radius/18, F(1, 9)-radius/18
    gbar = min(F(1, 10)-rstar, hs/5-rstar, es/5-rstar, hs*(F(1, 10)-3*radius/4)-2*rstar)
    q5, q15 = base['q']
    y1, y2 = defects['E5']-gbar*q5, defects['E15']-gbar*q15
    require(gbar > 0 and y1 >= r/5 and y2 >= r1/5
            and y1+y2+sum(defects[k] for k in ('E3', 'E5d', 'E15d', 'omega'))
                <= defects['rho']-gbar*(q5+q15), 'DP7 retains the slot losses inside the same shifted residual budget')
    maximum, digest, witness = F(0), sha256(), None
    for layout in mean.layouts():
        current = mean.mean_data(sigma, max(d), max(d[2:]), parameter[4], eta, qslots, layout)
        star = mean.mean_data(0, F(3, 4), F(1, 2), F(3, 4), ETA_STAR, QSTAR, layout)
        observed = star['reference']-current['reference']+current['source_error']
        repaired = corrected_mean_price(sigma, F(2, 27), eta, p, a, b, qslots, r, r1, layout, current['source_error'])
        require(observed == repaired['exact_source_loss'], '124 independently reproduces the signed slot identity')
        rho_upper = F(299, 10800)*sigma+repaired['added_E5_E15_price']*(defects['E5']+defects['E15'])
        require(observed <= rho_upper, 'The repair consumes the original two shallow defect coordinates')
        require(observed <= F(299, 10800)*sigma+repaired['added_first_shifted_coordinate_price']*y1
                and observed <= F(299, 10800)*sigma+repaired['added_two_shifted_coordinate_price']*(y1+y2),
                'Both shifted-coordinate repairs need no new wrong-slot shift payment')
        maximum = max(maximum, observed)
        digest.update(json.dumps(encode([layout, observed, repaired]), separators=(',', ':')).encode())
        if layout == WITNESS:
            witness = {'layout': layout, 'actual_source_loss': observed, 'proposed_sigma_only_upper': 17*sigma/400,
                       'refutes_sigma_only_mean_claim': observed > 17*sigma/400, 'corrected': repaired}
    require(witness is not None and witness['actual_source_loss'] == 4*eps/135, 'One explicit original head has the exact lost H mass')
    require(witness['refutes_sigma_only_mean_claim'] == (N >= 9), 'Finite height9 and10 refute the stated sigma-only mean claim')
    return {'source_height': N, 'moved_original_depth': depth, 'epsilon': eps, 'label_checks': label_checks,
            'parameter_unchanged': parameter, 'sigma_unchanged': sigma, 'qslots_before': base['qslots'],
            'qslots_after': qslots, 'r': r, 'r1': r1, 'Delta': p+a+b,
            'literal_source_fixture': grid, 'actual_complete_defects': defects,
            'shifted_slot_repair': {'uniform_gap': gbar, 'q5': q5, 'q15': q15, 'y1': y1, 'y2': y2,
                                   'shared_residual_budget': defects['rho']-gbar*(q5+q15)},
            'survivor_mass': base['survivor_mass']+actual7*eps,
            'mean_counterexample': witness, 'mean_identity_checks': 12500,
            'maximum_observed_mean_source_loss': maximum, 'all_head_source_moduli_sha256': digest.hexdigest()}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('slot_modulus_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    constructor = module('slot_modulus_source_labels', base/'frontier/source-budgets/source_mass_compatibility.py')
    actual = module('slot_modulus_actual', base/'frontier/comparison-bounds/complete_off_face_cost.py')
    finite = module('slot_modulus_finite', base/'frontier/retained-transport/finite_source_face_transport.py')
    source = module('slot_modulus_source', base/'verify_joint_frontier.py')
    mean = module('slot_modulus_mean', base/'frontier/retained-transport/joint_deep_mean_transport.py')
    cases = [actual_case(constructor, actual, finite, source, mean, N, depth, literal)
             for N, depth, literal in ((5, 4, True), (6, 5, True), (9, 4, False), (10, 4, False))]
    require(F(1, 135)+F(1, 450)+F(13, 720) == F(299, 10800), 'Uniform source coefficient keeps shared head weights')
    eps = F(1, 625)
    limit = {'moved_original_depth': 4, 'epsilon': eps, 'sigma': F(0), 'Delta': F(0),
             'r': eps/2, 'r1': eps/3, 'rho': eps/5, 'omega': F(0),
             'qslots': QSTAR[:3]+(QSTAR[3]+eps, QSTAR[4]-eps), 'mean_source_loss': 4*eps/135,
             'scope': 'Ordinary complete-cylinder construction and limit formula, not inferred from finite tests.'}
    return {'schema': 'erdos7-actual-five-slot-source-modulus-v1', 'source_sha256': PINS,
            'actual_original_label_cases': cases, 'complete_source_limit': limit,
            'corrected_uniform_sigma_coefficient': F(299, 10800),
            'corrected_uniform_H_coefficient': F(4, 135),
            'full_radius_added_shallow_defect_price': F(8)/(45-3*F(2, 27)),
            'uniform_first_shifted_coordinate_price': F(8, 27),
            'scope': 'Actual original-source counterexamples to Delta-only five-slot and sigma-only124 mean-reference moduli. Corrected signed same-head identity retains the best-slot loss and pays it through E5+E15 in the existing single budget. All source labels and exponent tails retained. No Lean verification, new global K, or validation of any other unproved uniform-source estimates.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('slot_modulus_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact actual-source counterexample and repaired modulus certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: actual original-label slot counterexamples, finite mean refutations,50000 signed mean checks and shared-budget repair.')
    print('The H-slot loss is an independent observable; no other uniform-source theorem is certified here.')


if __name__ == '__main__':
    main()
