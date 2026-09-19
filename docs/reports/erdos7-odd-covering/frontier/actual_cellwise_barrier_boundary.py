#!/usr/bin/env python3
"""Exact inherited barrier boundary on the actual off-diagonal source family.

Standard library, read-only by default; --output writes exact rational JSON.
Reconstructs control404's source and fixed profile43 numerator independently
of control402. Checks the actual construction's cell-mass formulas and its
weighted-cap support vector. The theorem for arbitrary finite barrier
vectors, including vectors diverging with the family height, is proved in
note50; it is not inferred by sampling barriers or finite families here.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
INHERITED = 'frontier/absorbed_barrier_boundary.py'
PIN = 'a313d75be472e198c130084a2486da859cad086eb84f9f869c429236df1d89cc'
CONTROL = 404
ROOT = (0, 0, 1, 1, 1)
OMEGA = (F(1, 5), F(2, 5), F(0), F(0), F(0))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def support_pieces(d, eta):
    """One explicit point from each summand of the inherited cap support."""
    return (
        tuple(v/20 for v in eta),
        tuple(eta[l]/20 if ROOT[l] == 1 else F(0) for l in range(5)),
        tuple(eta[l]/20 if l == 1 else F(0) for l in range(5)),
        tuple(d[l]/90 if l == 0 else F(0) for l in range(5)),
        tuple(F(1, 360) if l == 4 else F(0) for l in range(5)),
    )


def construction(source, t, q, kappa, carrier_weight):
    """All-height formulas proved from the off-diagonal original labels."""
    parameter = ((9*t, F(0), F(0), F(0), F(0)), (F(0), q),
                 (F(0), F(0), q, F(0), F(0)),
                 (F(0), F(0), F(0), t*q, F(0)), 1-q)
    dat = source.data(parameter)
    d, n, eta, s, D = dat
    pure3 = ((eta[0]+t)*(1-q), 2*eta[1]*(1-q), F(0), F(0), F(0))
    positive5 = (
        tuple(v*q for v in eta),
        tuple(eta[l]*q if ROOT[l] == 1 else F(0) for l in range(5)),
        (F(0), q/9, F(0), F(0), F(0)),
        (F(0), F(0), F(0), F(0), t*q),
    )
    carriers = tuple(pure3[l]+sum(piece[l] for piece in positive5)
                     for l in range(5))
    mass = tuple(n[l]-kappa*carriers[l] for l in range(5))
    omega = tuple(carrier_weight*w for w in OMEGA)
    remainder = tuple((1-omega[l])*n[l]-mass[l] for l in range(5))
    pieces = support_pieces(d, eta)
    cap_vector = tuple(sum(piece[l] for piece in pieces) for l in range(5))
    require(s == sum(n) == F(5, 9)-t-q, 'Complete off-diagonal source mass')
    require(sum(carriers) == F(1, 3)+2*q/3, 'Complete old-carrier mass sum')
    require(sum(mass) == s-kappa*sum(carriers), 'Actual normalized survivor total')
    require(all(0 < mass[l] <= n[l] for l in range(5)), 'Actual survivor cell boxes')
    require(all(remainder[l] <= cap_vector[l] for l in range(5)),
            'Explicit support vector dominates every nonnegative weighted deletion')
    require(0 <= carrier_weight <= 1 and sum(mass) >= D,
            'Normalized carrier mixture and inherited lower survivor bound')
    return {
        'parameter': parameter, 'source_data': dat,
        'pure3_carrier_vector': pure3, 'positive5_carrier_vectors': positive5,
        'old_carrier_vector': carriers, 'old_carrier_total': sum(carriers),
        'survivor_vector': mass, 'survivor_total': sum(mass),
        'carrier_cap_weight': carrier_weight, 'empty_cap_weight': 1-carrier_weight,
        'omega': omega, 'remainder_vector': remainder,
        'support_pieces': pieces, 'dominating_support_vector': cap_vector,
    }


def calculate(base):
    path = base/INHERITED
    require(sha256(path.read_bytes()).hexdigest() == PIN, 'Inherited comparator source SHA256')
    spec = importlib.util.spec_from_file_location('actual_cellwise_inherited', path)
    require(spec is not None and spec.loader is not None, 'Loadable inherited comparator')
    inherited = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(inherited)
    # This verifies all inherited code and logical-certificate pins before reuse.
    old = inherited.calculate(base)
    io = inherited.module('actual_cellwise_io', base/'certificate_io.py')
    source = inherited.module('actual_cellwise_source', base/'verify_joint_frontier.py')
    fixed = inherited.module('actual_cellwise_fixed', base/'frontier/fixed_cost.py')
    square = inherited.module('actual_cellwise_square', base/'frontier/shared_square_barrier.py')
    previous = json.loads(io.read_artifact_bytes(base/inherited.CERTIFICATE43),
                          object_pairs_hook=inherited.unique)
    survival = json.loads(io.read_artifact_bytes(base/inherited.CERTIFICATE41),
                          object_pairs_hook=inherited.unique)
    require(ROOT == source.ROOT and inherited.LAYOUTS == source.BASES,
            'Same original five-cell baseline domain')
    parameters = list(source.vertices())
    require(len(parameters) == 1296, 'Complete parameter-vertex inventory')
    dat = source.data(parameters[CONTROL])
    d, n, eta, s, D = dat
    require(dat == ((F(3, 4), F(3, 4), F(1, 4), F(1, 2), F(1, 2)),
                    (F(1, 24), F(1, 12), F(1, 36), F(1, 24), F(1, 18)),
                    (F(1, 18), F(1, 9), F(1, 9), F(1, 9), F(1, 9)),
                    F(1, 4), F(3, 20)), 'Exact off-diagonal control404 data')
    full_row = previous['full_absorbed_hinges']['rows'][CONTROL]
    survival_row = survival['survival_hinge']['rows'][CONTROL]
    require(full_row['index'] == survival_row['index'] == CONTROL
            and [CONTROL, 'D'] in previous['maximizer_endpoints']['bound']
            and F(previous['q_effective']) == F(23, 42),
            'Published profile43 bound is attained at control404 D endpoint')
    m25 = F(survival_row['margin'])
    require(m25 == F(68963, 441000) == old['m25'], 'Control404 inherited m25')
    losses = {}
    for threshold in (4, 5):
        scalar = inherited.operator(threshold, (0, 0, 0, 0, 0), dat)
        tag = ('seven_block', (('h', F(threshold)), 0))
        require(scalar == source.zero5_raw(tag, dat)
                == F(full_row[str(threshold)]['zero5_raw']),
                'Independent control404 complete zero7-source reconstruction')
        positive7 = source.raw357(F(threshold), dat)-scalar
        require(positive7 == F(full_row[str(threshold)]['positive7_complement']),
                'Control404 complete positive7 complement')
        starred = inherited.operator(threshold, inherited.CARRIER, dat)
        losses[threshold] = {'positive7': positive7, 'F_star': starred,
                             'constant_loss': positive7+starred}
        require(losses[threshold] == old['source_losses'][threshold],
                'Independently evaluated off-diagonal and aligned source constants agree')
    delta43 = F(23, 42)*D+m25/22+F(full_row['4']['margin'])/6
    delta43 += F(4, 33)*F(full_row['5']['margin'])
    require(delta43 > 0, 'Positive inherited denominator at control404')
    numerator_J = (F(previous['bound'])-source.WHOLE_CONST)*delta43
    G = F(previous['source_G357'])
    # The reused arithmetic helper has an aligned-control guard; supply the
    # separate off-diagonal guard before applying its formula to actual404 data.
    require(CONTROL not in square.SELECTED and square.SOURCE_NORM == G
            and G == F(102715, 2916) and square.BARRIER == 45
            and F(previous['source_comparison_barrier']) == 45,
            'Control404 uses the unrefined inherited square formula')
    mg, old_mg = inherited.inherited_square_margin(source, fixed, square, dat, G)
    finite, tails = source.ap_product_distribution(((11, F(5, 3)), (13, F(12, 7))), 9)
    cG, A81 = F(previous['cG']), F(previous['A81'])
    require(cG == tails[2]+sum(k*k*finite[k] for k in (7, 8)), 'Complete AP square tail')
    raw81 = sum(prob*k*k*source.square357(F(81, k*k), dat)
                for k, prob in finite.items() if k < 7)
    numerator_T = A81*D+raw81-cG*mg
    numerator = numerator_J+numerator_T
    require(numerator_J > 0 and numerator_T > 0
            and numerator == old['numerator_combined']
            == F(235676572069506444982211913251473065480803,
                 6360462916399256045941092769236000000000),
            'Combined numerator independently reconstructed at control404')
    limit = construction(source, F(1, 18), F(1, 4), F(1, 5), F(1))
    require(limit['parameter'] == parameters[CONTROL] and limit['source_data'] == dat,
            'Actual construction limit is the independently selected control404')
    require(limit['old_carrier_vector'] ==
            (F(7, 72), F(2, 9), F(1, 18), F(1, 18), F(5, 72)),
            'Complete actual limiting old-carrier vector')
    require(limit['survivor_vector'] ==
            (F(1, 45), F(7, 180), F(1, 60), F(11, 360), F(1, 24)),
            'Complete actual limiting survivor vector')
    remainder = limit['remainder_vector']
    require(remainder == limit['dominating_support_vector']
            == (F(1, 90), F(1, 90), F(1, 90), F(1, 90), F(1, 72)),
            'Actual limiting remainder lies in the explicit support set')
    complete_cap = max(d)/90+(sum(eta)+max(sum(eta[:2]), sum(eta[2:]))+max(eta))/20+F(1, 360)
    require(sum(remainder) == complete_cap == F(7, 120)
            and limit['survivor_total'] == D, 'Actual limit attains total cap and mass endpoint')
    rows = []
    for height in (3, 4, 5, 6):
        tail = F(1, 7**height)
        row = construction(source, (1-F(1, 3**(height-2)))/18,
                           (1-F(1, 5**height))/4, (1-tail)/(5+tail), 1-tail)
        row['height'] = height
        rows.append(row)
    upper = F(193, 231)*D+m25/22
    upper -= losses[4]['constant_loss']/6+F(4, 33)*losses[5]['constant_loss']
    require(upper == old['denominator_upper_at_D'] == F(2025618599, 26741137500) > 0,
            'Same limiting all-vector denominator ceiling on the actual family')
    boundary = source.WHOLE_CONST+numerator/upper
    require(boundary == old['combined_family_lower_bound']
            == F(1208994069650187954348450703035483220540461139,
                 2367081918117057277892487238031745380160000) > 510 > 403,
            'Exact inherited comparison boundary remains above403')
    return {
        'schema': 'erdos7-actual-cellwise-barrier-boundary-v1', 'control': CONTROL,
        'source_data': dat, 'selected_carrier': [0, 1], 'actual_limit': limit,
        'finite_formula_checks': rows, 'm25': m25, 'delta43': delta43,
        'source_losses': losses, 'source_margin_before45': old_mg,
        'source_margin_inherited45': mg, 'Raw81': raw81,
        'numerator_J': numerator_J, 'numerator_T81': numerator_T,
        'numerator_combined': numerator, 'denominator_upper_at_limit': upper,
        'combined_family_lower_bound': boundary, 'gap_above403': boundary-403,
        'source_layout_checks': 100, 'scalar_reconstruction_checks': 2,
        'input_sha256': {INHERITED: PIN, **inherited.PINS},
        'scope': ('Actual source/cell-mass/carrier closure witness for the fixed profile43 '
                  'numerator, old m25 and inherited source envelopes. Note50 proves the '
                  'uniform comparison boundary for arbitrary finite nonnegative cell '
                  'barriers, including barriers diverging with height. No attainment of '
                  'actual test-cost envelopes is claimed. Changed numerator comparisons '
                  'such as profile47 are outside this boundary. Arithmetic checks use '
                  'the proved construction formulas; independent original-label CRT '
                  'verification is in sharp_source_mass_endpoints.py. No Lean proof or '
                  'unrestricted Erdos7 resolution is claimed.'),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(Path(__file__).resolve().parents[1])
    if args.output is not None:
        args.output.write_text(json.dumps(result, default=str, indent=2)+'\n')
    print('PASS: independent control404 source/numerator, actual cell support, four finite mass formulas and exact carrier tails.')
    print('The old comparison boundary is510.75294876651606...; actual test-cost attainment and unrestricted Erdos7 remain unproved.')


if __name__ == '__main__':
    main()
