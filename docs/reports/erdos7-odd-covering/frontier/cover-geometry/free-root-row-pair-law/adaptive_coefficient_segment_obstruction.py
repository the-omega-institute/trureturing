#!/usr/bin/env python3
"""Exact two-layout lower certificates for a segment of two actual laws.

The generic checker accepts one actual source, two supported probabilities,
and two independently legal original-divisor layouts. It minimizes the
maximum of their affine expectations over the complete mixture segment,
and returns one fixed two-layout dual probability attaining the same bound.

The source-family controls import the existing sharpness_source constructor.
They do not copy its source or component laws. Standard-library exact
arithmetic; explicit validation remains active under -O. No files are written.
"""
from fractions import Fraction as F
import copy
import json

import prime_layout_mixture_certificate as original
import three_fifths_tree_common_law as sharpness


def need(condition, message):
    if not condition:
        raise ValueError(message)


def exact(value, name):
    need(type(value) in (int, F), name+' must be an integer or Fraction')
    return F(value)


def height(value, minimum=0):
    need(type(value) is int and value >= minimum,
         'height must be a literal integer >= '+str(minimum))
    return value


def two_affine_minimax(endpoints):
    """Each of two rows is (value at alpha=1, value at alpha=0).

    Return both the exact minimum of the maximum and a dual mixture of
    the two rows, valid simultaneously at both alpha endpoints.
    """
    need(type(endpoints) in (tuple, list) and len(endpoints) == 2
         and all(type(row) in (tuple, list) and len(row) == 2 for row in endpoints),
         'two pairs of affine endpoint values required')
    (u_a, v_a), (u_b, v_b) = tuple(tuple(exact(x, 'affine endpoint') for x in row)
                                  for row in endpoints)
    s_a, s_b = u_a-v_a, u_b-v_b
    candidates = {F(0), F(1)}
    if s_a != s_b:
        crossing = (v_b-v_a)/(s_a-s_b)
        if 0 <= crossing <= 1:
            candidates.add(crossing)
    lower, alpha = min((max(v_a+a*s_a, v_b+a*s_b), a) for a in candidates)

    # A dual chooses layout A with theta and B with 1-theta. Its minimum
    # over the law segment is the smaller of its two endpoint expectations.
    dual_candidates = {F(0), F(1)}
    denominator = (u_a-u_b)-(v_a-v_b)
    if denominator:
        crossing = (v_b-u_b)/denominator
        if 0 <= crossing <= 1:
            dual_candidates.add(crossing)
    dual_value = max(min(t*u_a+(1-t)*u_b, t*v_a+(1-t)*v_b) for t in dual_candidates)
    theta = min(t for t in dual_candidates
                if min(t*u_a+(1-t)*u_b, t*v_a+(1-t)*v_b) == dual_value)
    dual_endpoints = (theta*u_a+(1-theta)*u_b, theta*v_a+(1-theta)*v_b)
    need(lower == dual_value and all(x >= lower for x in dual_endpoints),
         'exact two-line primal/dual certificate mismatch')
    return {'lower_bound': lower, 'minimizing_alpha': alpha,
            'primal_layout_values': (v_a+alpha*s_a, v_b+alpha*s_b),
            'dual_layout_weights': (theta, 1-theta),
            'dual_endpoint_expectations': dual_endpoints,
            'affine_endpoints_mu_omega': ((u_a, v_a), (u_b, v_b))}


def two_layout_segment_lower(K, source, mu, omega, layout_a, layout_b):
    """Exact lower bound for every alpha*mu+(1-alpha)*omega, alpha in [0,1].

    Every input probability and layout is validated on this same source.
    This does not lower-bound all other source-supported probabilities.
    """
    height(K)
    source = sharpness._common.validate_source(K, source)
    sharpness._common._probability(mu, source, 'mu')
    sharpness._common._probability(omega, source, 'omega')
    layouts = (original.validate_layout(K, layout_a), original.validate_layout(K, layout_b))
    endpoints = []
    for layout in layouts:
        costs = {p: original.literal_layout_cost(K, layout, p) for p in source}
        endpoints.append(tuple(sum((mass*costs[p] for p, mass in law.items()), F())
                               for law in (mu, omega)))
    result = two_affine_minimax(endpoints)
    result.update({'height': K, 'source_points': len(source),
                   'original_divisors': original.original_divisors(K),
                   'layouts': layouts,
                   'scope': 'one lower certificate for the entire specified two-law segment; not a source minimax bound'})
    return result


def aligned_layout(K, row, residue):
    """Actual original phases sharing this centre; permitted as lower witnesses."""
    height(K)
    need(type(row) is int and row in (1, 2, 3, 4) and type(residue) is int
         and 0 <= residue < 7**K, 'literal row and seven-adic centre required')
    phases = []
    for j in range(K+1):
        q = 7**j
        z = residue % q
        phases.extend((z, z+q*((row-z)*pow(q, -1, 5) % 5)))
    return original.validate_layout(K, tuple(phases))


def family_formula(K):
    """Evaluate exact all-height formulas without constructing exponentially many leaves."""
    height(K, 1)
    s_f = sum((F(2*j+1, 5**j) for j in range(K+1)), F())
    s_q = sum((F(2*j+1, 3**j) for j in range(K+1)), F())
    alpha = 2*s_q/(3+2*s_q)
    theta = (20*s_f-3-7*s_q)/(9+6*s_q)
    lower = s_q*(8*s_f+3)/(3+2*s_q)
    target = 2*s_q
    gap = s_q*(F(4*(K+2), 3**K)-F(4*K+7, 5**K))/(3+2*s_q)
    need(0 < alpha < 1 and 0 < theta < 1, 'interior family coefficient certificate')
    need(lower-target == gap > 0 and lower < 6,
         'family formula must exceed the finite target while remaining below six')
    endpoints = ((4*s_f-F(12, 5), F(13, 5)*s_q),
                 (4*s_f-F(3, 5), F(7, 5)*s_q))
    solved = two_affine_minimax(endpoints)
    need(solved['lower_bound'] == lower and solved['minimizing_alpha'] == alpha
         and solved['dual_layout_weights'] == (theta, 1-theta),
         'closed-form family primal/dual mismatch')
    return {'height': K, 'S_f': s_f, 'S_q': s_q, 'alpha_star': alpha,
            'dual_layout_weights': (theta, 1-theta), 'lower_bound': lower,
            'finite_target': target, 'strict_gap': gap, 'gap_below_six': 6-lower,
            'affine_endpoints_mu_omega': endpoints}


def family_control(K, four_active=False):
    """Check imported actual laws and layouts against the analytic formulas."""
    height(K, 1)
    need(type(four_active) is bool, 'literal four-active option required')
    supplied = sharpness.sharpness_source(K, four_active)
    source = supplied['source']
    components = supplied['certificate']['components']
    mu, omega = components['mu'], components['omega']
    layout_a, layout_b = aligned_layout(K, 1, 0), aligned_layout(K, 2, 1)
    certificate = two_layout_segment_lower(K, source, mu, omega, layout_a, layout_b)
    formula = family_formula(K)
    need(certificate['affine_endpoints_mu_omega'] == formula['affine_endpoints_mu_omega'],
         'actual literal-layout affine expectations differ from family formulas')
    need(certificate['lower_bound'] == formula['lower_bound']
         and certificate['minimizing_alpha'] == formula['alpha_star']
         and certificate['dual_layout_weights'] == formula['dual_layout_weights'],
         'actual segment certificate differs from analytic family result')
    need(certificate['dual_endpoint_expectations'] == (formula['lower_bound'],)*2,
         'one common layout mixture must attain the same bound on both actual laws')
    need(len({r for r, _ in source}) == (4 if four_active else 3), 'wrong actual active-row count')
    return {'four_active': four_active, 'formula': formula, 'certificate': certificate}


def rejected(name, action):
    try:
        action()
    except ValueError:
        return name
    raise ValueError('malformed input accepted: '+name)


def malformed_controls():
    supplied = sharpness.sharpness_source(1)
    source = supplied['source'];components = supplied['certificate']['components']
    mu, omega = components['mu'], components['omega']
    la, lb = aligned_layout(1, 1, 0), aligned_layout(1, 2, 1)
    def check(law=mu, source_arg=source, left=la):
        return two_layout_segment_lower(1, source_arg, law, omega, left, lb)
    floating = copy.deepcopy(mu);p = next(iter(floating));floating[p] = float(floating[p])
    negative = copy.deepcopy(mu);negative[p] = -negative[p]
    wrong_total = copy.deepcopy(mu);wrong_total[p] += F(1, 5)
    outside = copy.deepcopy(mu);mass = outside.pop(p)
    absent = next((r, y) for r in range(1, 5) for y in range(7) if (r, y) not in source)
    outside[absent] = mass
    bad_residue = list(la);bad_residue[-1] = 35
    cases = [('boolean_height', lambda: family_formula(True)),
             ('floating_law_mass', lambda: check(floating)),
             ('negative_law_mass', lambda: check(negative)),
             ('unnormalized_law', lambda: check(wrong_total)),
             ('unsupported_law_mass', lambda: check(outside)),
             ('duplicate_source_point', lambda: check(source_arg=list(source)+[next(iter(source))])),
             ('missing_original_label', lambda: check(left=la[:-1])),
             ('noncanonical_original_phase', lambda: check(left=bad_residue)),
             ('floating_affine_endpoint', lambda: two_affine_minimax(((1., 0), (0, 1)))),
             ('wrong_endpoint_shape', lambda: two_affine_minimax(((1, 0),))),
             ('nonboolean_four_active', lambda: family_control(1, 1))]
    return [rejected(name, action) for name, action in cases]


def self_check():
    generic = []
    for endpoints, expected in ((((0, 2), (2, 0)), F(1)),
                                (((2, 1), (3, 2)), F(2)),
                                (((1, 1), (2, 2)), F(2)),
                                (((4, 0), (4, 0)), F(0)),
                                (((0, 4), (0, 4)), F(0))):
        result = two_affine_minimax(endpoints)
        need(result['lower_bound'] == expected, 'generic boundary/parallel affine control')
        generic.append(result)
    controls = []
    for K in range(1, 6):
        plain, four = family_control(K), family_control(K, True)
        need(plain['certificate']['affine_endpoints_mu_omega'] == four['certificate']['affine_endpoints_mu_omega'],
             'adding the unused fourth-row point changed either actual law')
        controls.extend((plain, four))
    return {'generic_affine_controls': generic, 'actual_family_controls': controls,
            'malformed_inputs_rejected': malformed_controls(),
            'scope': 'actual finite checks of the two-law segment obstruction; all-height positivity is analytic, not finite enumeration'}


def jsonable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [jsonable(v) for v in value]
    return value


if __name__ == '__main__':
    print(json.dumps(jsonable(self_check()), indent=2, sort_keys=True))
