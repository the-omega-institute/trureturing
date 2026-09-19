#!/usr/bin/env python3
"""One assigned-source conservation bound and one complete whole-J defect budget."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_assigned_joint_error_reserve.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/j-geometry/j_source_labelwise_neighborhood.py': '8569c38190dc48089a7e4587467564cc00cb69e916f0cf89a0bb5d8c294fe67a', 'frontier/j-geometry/j_family_error_reserve.py': 'b13e04593cf9e13fe2dce5a0bfed3b71806c533a447200453329a50fbf0db540', 'frontier/j-geometry/j_affine_margin_reserve.py': 'a4acf2224003a6f8cd04b4cada10818a113644812406c20dcb125a81a998d659', 'certificates/source_norms/j-geometry/j_source_labelwise_neighborhood.json': 'd6b2ecef58fa93ac79d1e15845fa5a4dd1c9fb9ae69b40d15c411ba49b68b328', 'certificates/source_norms/j-geometry/j_affine_margin_reserve.json': '16b4d4e4ba7a9f6bcc5304f68917c58780ba5516feb5ae7e6efde5ea7b8d00c9', 'profile-notes/065-128/85-a-broad-five-slot-source-deletion-tradeoff.md': '70472fec1d274101b387f9d8fba98c1707cc39770af79f269f4f11a41657d377', 'profile-notes/065-128/88-a-weighted-source-comparison-on-the-broad-slab.md': '972263edec12e318502eee7a3a0f776d41e7f09c9a32efd16f4d79fe08c9b657', 'profile-notes/129-192/136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md': '845d9a84f41391240f05f8c5be35cf074d6614abf1dfc493046e8619521f3945', 'profile-notes/193-256/197-the-whole-j-reserve-keeps-each-original-family-error.md': '9480a9921773085a9c21cee529818aa368e68a06810e7e98086745e787064ebd', 'profile-notes/193-256/212-a-supporting-affine-margin-sharpens-the-whole-j-reserve.md': '1d5f9aae11202a8aa4deca7e96ad9695da00dbb1bed9eef8541157cf986e1509'}
TAU = F(1, 1000)
NAMES = ('E5', 'E15', 'E5d', 'E15d', 'E3', 'omega')
L = F(3169, 600)-F(1, 1458)-F(1, 30*5**9)
TAIL_CONSTANT = F(1, 9720)+F(17, 120*5**9)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original proof provider')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def polynomial_sum(*polynomials):
    out = {}
    for polynomial in polynomials:
        for powers, coefficient in polynomial.items():
            out[powers] = out.get(powers, F(0))+coefficient
    return {powers: coefficient for powers, coefficient in out.items() if coefficient}


def polynomial_product(left, right):
    return polynomial_sum(*[{tuple(sorted(a+b)): x*y} for a, x in left.items() for b, y in right.items()])


def conservation_identity():
    """Check the symbolic conservation identity after the two exact set partitions."""
    v = lambda name: {(name,): F(1)}
    k = lambda value: {(): F(value)}
    neg = lambda polynomial: {powers: -coefficient for powers, coefficient in polynomial.items()}
    h0, h1, p, a, b = (v(name) for name in ('h0', 'h1', 'p', 'a', 'b'))
    A5, B5, H5, BR, HR = (v(name) for name in ('R5A', 'R5B', 'R5H', 'RB', 'RH'))
    LB, LH, lam, ell = (v(name) for name in ('LB', 'LH', 'lambda', 'ell'))
    q0 = polynomial_sum(p, A5, B5, H5)
    q1 = polynomial_sum(p, a, BR, HR)
    bgap = polynomial_sum(k(F(1, 90)), neg(LB))
    raw_gap = polynomial_sum(polynomial_product(h0, q0), polynomial_product(h1, q1), bgap)
    target = polynomial_sum(polynomial_product(polynomial_sum(h0, h1), polynomial_sum(p, a, b)),
                            ell, polynomial_product(k(5), lam))
    slacks = [polynomial_product(h0, polynomial_sum(a, neg(A5))),
              polynomial_product(h0, polynomial_sum(b, neg(B5))),
              polynomial_product(h1, polynomial_sum(b, neg(BR))),
              polynomial_sum(ell, neg(polynomial_product(h0, H5)), neg(polynomial_product(h1, HR)), neg(LH)),
              polynomial_sum(LB, LH, polynomial_product(k(5), lam), k(-F(1, 90)))]
    require(polynomial_sum(target, neg(raw_gap)) == polynomial_sum(*slacks),
            'Exact symbolic Q/B source-conservation slack identity')
    # Positive parts are bounded separately by Delta+R5H, Delta+RH and
    # 5lambda+LH, all nonnegative. Their weighted sum then uses the same
    # H-union inequality. The displayed identity never licenses cancelling
    # a negative gap against another gap before taking positive parts.
    show = lambda poly: {'*'.join(powers) if powers else '1': coefficient for powers, coefficient in sorted(poly.items())}
    return {'target_minus_unclipped_gaps': show(polynomial_sum(target, neg(raw_gap))),
            'nonnegative_slack_terms': [show(row) for row in slacks],
            'positive_part_bounds': ['(1/20-|R5 intersect Q|)_+<=Delta+|R5 intersect H|',
                                    '(1/10-|R intersect Q|)_+<=Delta+|R intersect H|',
                                    '(1/90-LB)_+<=5lambda+LH'],
            'actual_disjoint_H_pieces': ['root0 times(R5 intersect H)', 'root1 times(R intersect H)',
                                        'later assigned b=1 late deletion in H'],
            'required_set_facts': ['|R5|=1/20-p', '|R|=1/10-p-a', '|R5 intersect A|<=a',
                                   '|R5 intersect B|<=b', '|R intersect B|<=b',
                                   'h0|R5 intersect H|+h1|R intersect H|+LH<=ell',
                                   'LB+LH>=1/90-5lambda'],
            'view_scope': 'Full columns and root-columns with0<=w<=1 and w=1 on root1/B; no arbitrary cellwise B allocation or raw-family disjointness claim.'}


def coefficients(delta):
    d = F(delta)
    require(0 <= d <= TAU, 'Original136 source radius')
    chi = F(6)/(3-2*d)
    c5, c15 = 5+5*d/9, F(30)/(6-d)
    carrier = d*(F(1, 18)+d/90)
    P = (F(1), chi, F(1), chi, F(0), F(1))
    Q = (F(0), F(0), F(0), F(0), F(1), F(1))
    shallow = (P, P, (c5+F(46, 9), c15, F(0), F(0), F(1), F(1)),
               (c5+5, c15, F(0), F(0), F(0), F(1)))
    drifts = (2*d, 2*d, d/2+carrier, 179*d/360+carrier)
    prices = tuple(sum(row[i] for row in shallow)+5*P[i]+8*Q[i] for i in range(6))
    expected = ((244+10*d)/9, F(42)/(3-2*d)+F(60)/(6-d), F(7), F(42)/(3-2*d), F(9), F(17))
    require(prices == expected and max(prices) == prices[0], 'All six exact combined defect prices and their common dual cap')
    ternary_drift = 3*sum(F(1, 3**a) for a in range(3, 8))
    five_drift = F(2, 15)*sum(F(1, 5**b) for b in range(2, 10))
    constants = (F(9, 20)*F(1, 2*3**7), F(17, 30)*F(1, 4*5**9))
    require(ternary_drift == F(1, 6)-F(1, 1458)
            and five_drift == F(1, 150)-F(1, 30*5**9)
            and constants == (F(1, 9720), F(17, 120*5**9))
            and sum(drifts)+(ternary_drift+five_drift)*d == L*d+d*d/45,
            'Four shallow drifts, all finite axis terms and both full infinite continuations')
    return {'delta': d, 'wrong_root_price': chi, 'shallow5_price': c5, 'shallow15_price': c15,
            'carrier_error': carrier, 'P_coefficients': P, 'Q_coefficients': Q,
            'shallow_coefficients': shallow, 'shallow_drifts': drifts,
            'joint_defect_prices': dict(zip(NAMES, prices)), 'maximum_defect_price': prices[0],
            'axis_linear_delta_coefficients': (ternary_drift, five_drift),
            'axis_defect_multipliers': (5, 8), 'axis_complete_remainder_constants': constants}


def joint_error_upper(delta, rho):
    d, r = map(F, (delta, rho))
    require(d >= 0 and r >= 0 and d+r <= TAU, 'Whole original136 triangle; no enlarged domain')
    R = r+7*d/36
    c = coefficients(d)
    U = L*d+d*d/45+c['maximum_defect_price']*R+TAIL_CONSTANT
    require(U == sum(c['shallow_drifts'])+sum(c['axis_linear_delta_coefficients'])*d
                    +c['maximum_defect_price']*R+sum(c['axis_complete_remainder_constants']),
            'The complete single-budget upper is assembled from all original family errors')
    return {'source_radius': d, 'residual_radius': r, 'single_actual_capacity_budget_upper': R,
            'coefficients': c, 'complete_zero7_error_upper': U}


def reserve_bound(delta, rho):
    row = joint_error_upper(delta, rho)
    d, r, U = row['source_radius'], row['residual_radius'], row['complete_zero7_error_upper']
    coarse = F(79, 1944)+5*r-F(359, 60)*d-U
    sharp = F(79, 1944)+5*r-F(527, 90)*d+d*d/40-U
    require(sharp-coarse == 23*d/180+d*d/40 >= 0,
            'Retaining212 signed quadratic support can only improve the same replacement')
    return {**row, 'coarse_old49_replacement_reserve_lower': coarse,
            'old49_replacement_reserve_lower': sharp,
            'sharp_affine_support_gain': sharp-coarse,
            'identity_margin_lower': F(13, 50)+5*r-F(239, 60)*d-U,
            'old49_margin_upper': F(10661, 48600)+F(337, 180)*d-d*d/40,
            'favorable_actual_residual_margin_coefficient': F(5)}


def actual_vector_error(delta, rho, vector, family):
    row = joint_error_upper(delta, rho)
    c = row['coefficients']
    e = tuple(map(F, vector))
    require(len(e) == 6 and min(e) >= 0 and sum(e) <= row['single_actual_capacity_budget_upper'],
            'One admissible actual six-defect vector')
    dot = lambda x: sum(a*b for a, b in zip(x, e))
    caps = (F(29, 120), F(1, 15), F(11, 75), F(2, 75))
    shallow = tuple(min(d+dot(v), cap) for d, v, cap in zip(c['shallow_drifts'], c['shallow_coefficients'], caps))
    P, Q, d = dot(c['P_coefficients']), dot(c['Q_coefficients']), F(delta)
    axes = [family.complete_axis_error(3, 3, F(9, 20), 3*d, P),
            family.complete_axis_error(5, 2, F(17, 30), 2*d/15, Q)]
    for axis in axes:
        require(axis['value'] == family.independent_axis_error(axis['prime'], axis['first_depth'],
                    axis['cap_coefficient'], axis['drift_coefficient'], axis['residual_error']),
                'Two independent exact evaluations keep each entire clipped axis')
    axis_dual = [c['axis_linear_delta_coefficients'][i]*d+c['axis_defect_multipliers'][i]*v
                 +c['axis_complete_remainder_constants'][i] for i, v in enumerate((P, Q))]
    require(all(axis['value'] <= upper for axis, upper in zip(axes, axis_dual)),
            'Complete clipped tails obey the finite-error-plus-full-continuation dual')
    value = sum(shallow)+sum(axis['value'] for axis in axes)
    require(value <= row['complete_zero7_error_upper'], 'Whole common-vector error below one-budget dual')
    return {'defects': dict(zip(NAMES, e)), 'shallow_clipped_errors': shallow, 'complete_axes': axes,
            'axis_dual_uppers': axis_dual, 'complete_vector_error': value,
            'joint_dual_upper': row['complete_zero7_error_upper']}


def domain_proof(original):
    old = original.guard_and_prices()
    d = TAU
    hmax, h1min, h0max, emin = F(1, 2)+d/18, F(1, 3)-d/18, F(1, 6)+d/18, F(1, 9)-d/18
    gaps15 = (h1min/5, h1min/5, emin/5, h1min/25, (h1min-h0max)/5)
    g15 = (6-d)/450
    require(min(gaps15) == g15 and (h1min-h0max)/5-g15 == (1-d)/50 > 0
            and emin/5-g15 == 2*(1-d)/225 > 0,
            'All P,A,B,Q and wrong-root cofactor15 gaps, including missing labels')
    require(hmax/5*50 == 5+5*d/9 and F(1, 15)/g15 == F(30)/(6-d)
            and F(1, 3)/(h1min-h0max) == F(6)/(3-2*d),
            'Whole-domain target-section and wrong-root ratios')
    require(5*d < F(1, 50) and 5*d < min(F(1, 10), h1min/5, emin/5)
            and 3*d/4 < F(1, 18) and d/4 < F(1, 25),
            'Every existing first-label and H-packing guard remains inside136')
    require(F(1, 90)+F(5, 9)*F(3, 4)+F(5, 72) == F(179, 360)
            and F(179, 360)+F(1, 360) == F(1, 2)
            and (1+F(1, 45))*5 == F(46, 9),
            'Assigned Q/B table error and the separate actual pure5 projection discrepancy')
    prices = tuple(coefficients(d)['joint_defect_prices'].values())
    dominance = F(244, 9)-max(prices[1:])
    require(dominance > 0, 'Increasing rational competitors at tau stay below the minimum leading price')
    boundary_linear = -5-F(359, 60)-L-F(10, 9)*TAU+F(29, 36)*F(244, 9)
    boundary_square = F(29, 36)*F(10, 9)-F(1, 45)
    minimum = F(79, 1944)+5*TAU-F(244, 9)*TAU-TAIL_CONSTANT
    # For the sharper reserve, d/d(delta) is
    # -527/90-L+delta/180-(10/9)*(rho+7delta/36)-(7/36)*C(delta).
    # Use delta<=TAU, rho>=0 and C(delta)>=(244/9) termwise.
    delta_derivative_upper = -F(527, 90)-L+TAU/180-F(7, 36)*F(244, 9)
    require(boundary_linear == F(317461329097, 56953125000) > 0
            and boundary_square == F(707, 810) > 0 and 5-F(244, 9) < 0
            and delta_derivative_upper < 0
            and minimum == F(43720531, 2373046875) > F(9, 500),
            'Strict rho decrease and positive boundary derivative prove the whole triangle minimum')
    for d0 in (F(0), TAU/3, TAU/2, TAU):
        bound = reserve_bound(d0, TAU-d0)
        require(bound['coarse_old49_replacement_reserve_lower']
                == minimum+boundary_linear*d0+boundary_square*d0*d0,
                'Independent exact boundary polynomial reconstruction')
    return {'original136_guards': old, 'domain_delta_plus_rho': TAU,
            'five_cofactor15_gap_lowers': gaps15, 'minimum_cofactor15_gap': g15,
            'defect_price_dominance_margin': dominance,
            'delta_derivative_upper': delta_derivative_upper,
            'rho_derivative_upper': 5-F(244, 9),
            'rectangle_proof': 'R4_delta=-527/90-L+delta/180-(10/9)(rho+7delta/36)-(7/36)C(delta), C(delta)=(244+10delta)/9. Bound delta/180 by tau/180, discard the nonpositive residual term and use C>=244/9. R4_rho=5-C<=5-244/9. Both partials are negative on the whole triangle; a rectangle inside it has its lower envelope at its upper corner. R3_delta=R4_delta-23/180-delta/20 is smaller and R3_rho=R4_rho.',
            'boundary_reserve_polynomial': [minimum, boundary_linear, boundary_square],
            'boundary_derivative_lower': boundary_linear,
            'whole_triangle_reserve_lower': minimum, 'strict_margin_over9_div500': minimum-F(9, 500),
            'minimum_location': {'delta': F(0), 'rho': TAU},
            'proof': 'For fixed delta both reserves decrease in rho; set rho=tau-delta. The coarse boundary polynomial has positive linear and quadratic coefficients. The sharper support adds23delta/180+delta^2/40. Thus both attain their certified lower envelope minimum at(0,tau).'}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical reader and source proofs')
    io = module('j_assigned_io', base/'certificate_io.py')
    read = lambda n: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', n+'.json')))
    previous, source = read('j_affine_margin_reserve'), read('j_source_labelwise_neighborhood')
    pins = dict(PINS)
    for data in (previous, source):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original proof input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    original = module('j_assigned_original', base/'frontier/j-geometry/j_source_labelwise_neighborhood.py')
    affine = module('j_assigned_affine', base/'frontier/j-geometry/j_affine_margin_reserve.py')
    family = module('j_assigned_tails', base/'frontier/j-geometry/j_family_error_reserve.py')
    require(affine.calculate(base) == previous and encode(original.guard_and_prices()) == source['domain_and_prices'],
            'The entire212 affine proof and all original136 domain guards are unchanged')
    conservation = conservation_identity()
    domain = domain_proof(original)
    points = []
    for d, r in ((F(0), F(0)), (F(0), TAU), (TAU, F(0)), (TAU/2, TAU/2),
                 (F(1, 1112), F(317, 25000000)), (F(493, 500000), F(7, 500000))):
        bound = reserve_bound(d, r)
        R = bound['single_actual_capacity_budget_upper']
        vectors = [(F(0),)*6]+[tuple(R if i == j else F(0) for i in range(6)) for j in range(6)]+[(R/6,)*6]
        checks = [actual_vector_error(d, r, vector, family) for vector in vectors]
        require(bound['old49_replacement_reserve_lower'] >= bound['coarse_old49_replacement_reserve_lower']
                >= domain['whole_triangle_reserve_lower'], 'Recorded points respect the already proved continuous-domain floor')
        points.append({'bound': bound, 'complete_tail_and_dual_checks': checks})
    return encode({'schema': 'erdos7-j-assigned-joint-error-reserve-v1', 'source_sha256': pins,
        'source_conservation': conservation, 'domain_proof': domain,
        'zero7_linear_delta_coefficient': L, 'zero7_quadratic_delta_coefficient': F(1, 45),
        'full_axis_remainder_constant': TAIL_CONSTANT,
        'six_defect_order': NAMES, 'complete_point_checks': points,
        'unchanged_mixed_family_errors': {'3_times_deep5': F(0), '9_times5': F(0), 'deep35': F(0)},
        'scope': 'Ordinary whole-J direction40 replacement on the entire original136 triangle delta+rho<=1/1000. Root0 pure5 and root1 union-deletion H pieces are separated by their actual ternary roots; later assigned late deletion is disjoint from both. No raw overlapping source families are treated as disjoint. All six mixed-seven defects share one actual budget, all original independent test residues and both infinite axes remain. The analytic dual is an upper, not an exact optimizer of the clipped error supremum. The positive reserve replaces old49 once. No enlarged source domain, complete global comparison, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_assigned_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact assigned-source joint-error certificate')
    print('PASS: whole original136 triangle, one six-defect budget, complete tails; reserve>='
          +str(result['domain_proof']['whole_triangle_reserve_lower'])+' >9/500.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
