#!/usr/bin/env python3
"""Common-budget mask bounds, exact tails and an actual coefficient obstruction.

The ordinary proof supplies the all-family inequalities and all-height
sharpness. This program reconstructs their rational constants, a literal
distinct-odd family, every ordered original-label pair cap, and its current
coordinate distribution. It does not enumerate the full common period or
assert Lean verification. Python 3.9+ standard library only.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
from math import lcm, prod
from pathlib import Path
import argparse
import json


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def unique(pairs):
    out = {}
    for key, value in pairs:
        need(key not in out, 'duplicate JSON key')
        out[key] = value
    return out


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def actual27(S, theta, b, lam, rho, kappa):
    family = [(9, 3), (27, 8), (19, 0), (57, 20), (171, 2), (513, 326)]
    need(len({m for m, _ in family}) == 6 and all(m > 1 and m % 2 for m, _ in family),
         'six literal distinct odd original classes')
    source = [x for x in range(27) if x % 9 != 3 and x != 8]
    need(len(source) == 23, 'actual old27 survivors')
    deletion_counts = {x: sum(x % m == 2 for m in (3, 9, 27)) for x in source}
    final = [z for z in range(513) if all(z % m != a for m, a in family)]
    need(len(final) == 402, 'literal complete survivor set')
    for x in source:
        good = {z % 19 for z in final if z % 27 == x}
        expected = {y for y in range(1, 19)
                    if all(x % m != 2 or y != a for m, a in ((3, 1), (9, 2), (27, 3)))}
        need(good == expected and len(good) == 18-deletion_counts[x], 'same actual row from CRT labels')
        need(F(deletion_counts[x], 18) < F(7, 17), 'zero assigned19 charge from the literal mask')
    cs = {k: F(19, 18-k) for k in set(deletion_counts.values())}
    vs = {k: lam*c+rho for k, c in cs.items()}
    ws = {k: c-theta*(c-1) for k, c in cs.items()}
    gs = {k: 1+S*c*c/vs[k] for k, c in cs.items()}
    layouts = []
    for residues in product(range(3), range(9), range(27)):
        counts = {}
        for x in source:
            n = 1+sum(x % m == a for m, a in zip((3, 9, 27), residues))
            key = (deletion_counts[x], n)
            counts[key] = counts.get(key, 0)+1
        layouts.append((residues, counts))
    need(len(layouts) == 729, 'all independent old residue layouts')

    def weighted_max(weights):
        return max((sum(count*weights[k]*n*n for (k, n), count in counts.items())/23,
                    tuple(-r for r in residues)) for residues, counts in layouts)

    def witness(value):
        return tuple(-r for r in value[1])

    gc, gw, gg = (weighted_max(f) for f in (cs, ws, gs))
    Br = (b-kappa)*gc[0]+kappa*gw[0]
    Utheta = Br+gg[0]
    U0 = weighted_max({k: 1+S*c for k, c in cs.items()})[0]+b*gc[0]
    active = next(counts for residues, counts in layouts if residues == witness(gg))
    # A fixed active branch is convex in rho. Its negative endpoint tangent
    # bounds the entire interval, as proved in the accompanying text.
    derivative = sum(count*S*cs[k]**2*(cs[k]-1)/vs[k]**2*n*n
                     for (k, n), count in active.items())/23+S/theta*(gw[0]-gc[0])
    need(derivative < 0, 'global minimum over all r occurs at theta')
    need(Utheta == F(4903795219637565032713, 1321543170681494545890), 'exact optimized MW bound')
    price = S
    fs = {k: 1+S*cs[k]**2/(vs[k]+price*gs[k]) for k in cs}
    scalar = Br+S*price*gg[0]+weighted_max(fs)[0]

    def integer_max(t):
        costs = {(k, n): F(n*n)+S*max(2*cs[k]*j*n-(vs[k]+t*gs[k])*j*j
                                    for j in range(1, 5))
                 for k in cs for n in range(1, 5)}
        return max(sum(count*costs[key] for key, count in counts.items())/23
                   for _, counts in layouts)

    integer0 = Br+integer_max(F())
    integer_price = Br+S*price*gg[0]+integer_max(price)
    need(integer0 == integer_price == F(424158493, 114332310), 'integer budgets coincide in this example')
    need(integer_price < scalar < F('3.710035') < F('3.710658') < Utheta < U0,
         'actual scalar budget improves the globally optimized old MW family')
    return {'original_forbidden_classes': family, 'old_period': 27, 'period': 513,
            'old_survivors': source, 'final_survivor_count': len(final), 'eta_mass': 1,
            'assigned_mixed_charge19': 0, 'old_layout_count': len(layouts),
            'row_cofactors': (3, 9, 27), 'row_active_counts': deletion_counts,
            'G_c': gc[0], 'G_w': gw[0], 'G_g': gg[0],
            'G_c_maximizer': witness(gc), 'G_w_maximizer': witness(gw), 'G_g_maximizer': witness(gg),
            'U0': U0, 'minimum_over_all_r': Utheta,
            'active_convex_branch_endpoint_derivative': derivative,
            'price': price, 'budgeted_scalar': scalar,
            'scalar_gain_over_all_r': Utheta-scalar,
            'unbudgeted_integer': integer0, 'budgeted_integer': integer_price,
            'scope': 'Actual nonconstant row weights and all729 original old layouts. The tangent proves a continuous parameter minimum. This example improves optimized MW with the scalar budget; the older integer bound already attains its budgeted integer value. No complete final-layout maximum is asserted.'}


def compute():
    p = 19
    S, theta, b = F(1, 18), F(18, 37), F(19, 162)
    lam = S/(S+theta)
    rho = 1-lam
    kappa = S*rho/theta
    need(lam == kappa == F(37, 361), 'same MW parameter')
    need(b-kappa == F(865, 58482), 'same nonnegative remaining coefficient')
    ustar = F(18, 19)
    dstar = lam+rho*ustar
    estar = ustar*dstar+S
    tstar = dstar*(1-dstar)/estar
    gamma = S*(1-dstar)**2/estar
    astar = 1-S*tstar/dstar
    need(tstar == F(38112120, 811405621), 'exact budget price')
    need(gamma == F(104976, 811405621), 'exact coefficient improvement')
    need(0 <= astar <= 1 and 1-gamma == astar+S*tstar, 'nonnegative upper coefficients')

    # Literal family: forbid0 at every nonunit divisor of Q0*19^3.
    old_primes = (3, 5, 7, 11, 13, 17)
    Q0 = prod(old_primes)
    old_labels = sorted(prod(r for r, bit in zip(old_primes, bits) if bit)
                        for bits in product((0, 1), repeat=len(old_primes)))
    H = 3
    labels = sorted(m*p**e for m in old_labels for e in range(H+1))
    N = len(old_labels)
    period = Q0*p**H
    need(N == 64 and len(labels) == len(set(labels)) == 256, 'complete original inventory')
    need(all(m > 1 and m % 2 == 1 for m in labels[1:]), 'distinct odd nonunit forbidden moduli')
    need(lcm(*labels) == period == 1750794045, 'literal common period')

    def phi(m):
        out = m
        for r in old_primes+(p,):
            if m % r == 0:
                out = out//r*(r-1)
        return out

    # For arbitrary residues each pair has this cap; the common unit centre1
    # attains all caps simultaneously, by the ordinary CRT proof.
    pair_sum = sum((F(1, phi(lcm(m, n))) for m in labels for n in labels), F())
    old_square = prod(1+F(3, r-1) for r in old_primes)
    current_load_squares = sum(
        (1+sum(y % p**e == 1 for e in range(1, H+1)))**2
        for y in range(p**H) if y % p)
    current_factor = F(current_load_squares, phi(p**H))
    a = S+b
    aH = sum((F(2*e+1, p**e) for e in range(1, H+1)), F())
    c, q = F(19, 18), F(1)
    need(current_factor == 1+c*aH, 'literal current-coordinate scan')
    actual = old_square*current_factor
    need(pair_sum == actual == F(1165255, 77824), 'all65536 original pair caps attain the same maximum')
    need(old_square == F(25935, 2048), 'complete old square maximum')

    # Exact old centered-load distribution. Convex concentration proves
    # this maximizes each F_t over all independent original old residues.
    pm = {}
    for bits in product((0, 1), repeat=len(old_primes)):
        mass = prod(F(1, r-1) if bit else F(r-2, r-1)
                    for r, bit in zip(old_primes, bits))
        n = 2**sum(bits)
        pm[n] = pm.get(n, F())+mass
    need(sum(pm.values()) == 1 and sum(w*n*n for n, w in pm.items()) == old_square,
         'same actual product-unit old law')
    v = lam*c+rho*q
    w = c-theta*(c-q)
    g = q+S*c*c/v
    need(v+tstar*g == c, 'budgeted integer optimizer j=n at every old load')

    def cost(n, price, ceiling=N):
        return q*n*n+S*max(2*c*j*n-(v+price*g)*j*j for j in range(1, ceiling+1))

    Br = ((b-kappa)*c+kappa*w)*old_square
    raw = Br+g*old_square
    unbudgeted = Br+sum(mass*cost(n, F()) for n, mass in pm.items())
    budgeted = Br+S*tstar*g*old_square+sum(mass*cost(n, tstar) for n, mass in pm.items())
    sharp_upper = Br+(1-gamma)*g*old_square
    need(budgeted == sharp_upper == old_square*(1+c*a) == F(3725995, 248832),
         'coefficient endpoint equals split comparison limit in this family')
    need(unbudgeted-budgeted == F(3499529, 10779402240) > 0,
         'strict actual integer-interface gain')
    tail = c*old_square*F(1, p**H)*(2*H*S+a)
    need(sharp_upper-actual == tail > 0, 'complete current comparison tail')
    violation = actual-(raw-2*gamma*g*old_square)
    need(violation == F(18605587, 24716980224) > 0, 'actual refutation of doubling the coefficient')
    need(cost(1, F(100)) < 0, 'F_t may be negative although its relaxed square weight is nonnegative')
    need(cost(16, F(), N) != cost(16, F(), 16), 'full original ceiling cannot be replaced by a box ceiling')

    # Universal actual row caps, using BOTH q<=1 and c<=9/5.
    cmax = F(9, 5)
    g_endpoints = [q0+S*cmax*cmax/(lam*cmax+rho*q0) for q0 in (F(), F(1))]
    gmax = max(g_endpoints)
    wmax = (1-theta)*cmax+theta
    vmax = lam*cmax+rho
    need(gmax == F(2531, 2170) and wmax == F(261, 185) and vmax == F(1953, 1805),
         'subprobability-aware caps')
    cost_slope = gmax+S*vmax/12
    factors = {
        'MW': 110*(gmax+kappa*wmax+(b-kappa)*cmax),
        'pure19_coefficient': 110*((1-gamma)*gmax+kappa*wmax+(b-kappa)*cmax),
        'integer_at_tstar': 110*(S*tstar*gmax+cost_slope+kappa*wmax+(b-kappa)*cmax),
    }
    need(factors['MW'] == F(103734290, 705033) < F(2090, 9), 'improved complete tail coefficient')
    rounded = {
        16: ('0.000357927', '0.000357886', '0.000360082'),
        20: ('0.000005399757', '0.000005399147', '0.000005432265'),
    }
    errors = {}
    full = prod(F(r*(r+1), (r-1)**2) for r in old_primes)
    need(full == F(357357, 20480), 'full pair product')
    for box, safe in rounded.items():
        core = prod(sum((F(2*j+1, r**j) for j in range(box+1)), F()) for r in old_primes)
        for r in old_primes:
            need(F(r*(r+1), (r-1)**2)-sum((F(2*j+1, r**j) for j in range(box+1)), F())
                 == F((2*box+3)*r-(2*box+1), r**box*(r-1)**2), 'complete single-prime pair tail')
        errors[box] = {'pair_tail': full-core, 'bounds': {}}
        for (name, factor), upper in zip(factors.items(), safe):
            value = factor*(full-core)
            need(value < F(upper), 'strict complete old-test error')
            errors[box]['bounds'][name] = {'exact': value, 'strict_upper': upper}
    return encode({
        'schema': 'erdos7-budgeted-mask-square-v1',
        'pure19': {'S': S, 'theta': theta, 'lambda': lam, 'rho': rho, 'kappa': kappa,
                   'remaining_coefficient': b-kappa, 'u_star': ustar, 'd_star': dstar,
                   'e_star': estar, 't_star': tstar, 'gamma_star': gamma, 'a_star': astar},
        'actual_family': {'old_period': Q0, 'current_height': H, 'period': period,
                         'forbidden_residue_at_every_nonunit_divisor': 0,
                         'original_forbidden_moduli': labels[1:], 'original_test_count': len(labels),
                         'old_test_moduli': old_labels, 'old_label_ceiling': N,
                         'ordered_pair_caps': len(labels)**2, 'old_unit_count': phi(Q0),
                         'current_unit_count': phi(p**H), 'current_centered_square_sum': current_load_squares,
                         'assigned_mixed_charge17': 0, 'assigned_mixed_charge19': 0,
                         'eta_mass': 1, 'q': q, 'c': c, 'old_square': old_square,
                         'old_centered_load_distribution': pm, 'actual_full_maximum': actual,
                         'raw_MW': raw, 'unbudgeted_integer': unbudgeted, 'budgeted_integer': budgeted,
                         'integer_gain': unbudgeted-budgeted, 'comparison_tail': tail,
                         'doubled_coefficient_violation': violation},
        'actual_caps': {'g_endpoints': g_endpoints, 'g': gmax, 'w': wmax, 'v': vmax,
                        'integer_difference_slope': cost_slope},
        'tail_coefficients': factors, 'test_box_errors': errors,
        'actual_nonconstant_mask_example': actual27(S, theta, b, lam, rho, kappa),
        'scope': 'General budget and tail formulae use one actual law with all original labels and comparison tails. Numeric coefficient requires an original modulus19 class. The literal finite family refutes a larger coefficient, not the484 target. Ordinary proofs plus exact arithmetic; no Lean endpoint.',
    })


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/budgeted_mask_square_certificate.json'))
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = compute()
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2)+'\n')
    else:
        need(result == json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique),
             'whole certificate differs from reconstruction')
    print('PASS budget constants, actual255-class obstruction, 65536 pairs, '
          '729 actual27 layouts with continuous parameter minimum, and complete box16/20 tails')


if __name__ == '__main__':
    main()
