#!/usr/bin/env python3
"""Exact uniform Gamma35 and Gamma357 bounds from shared actual parameters.

Python3.9+ standard library only. The accompanying proof gives the layout
inequality and the continuous linear-fractional vertex reduction. This checks
all72 old branches,103680 shared branches,12960 original signed
layout-vertices,12960 weighted-cross layout-vertices and16848
same-original5 endpoint/layout pairs, plus all missing-class cases. No solver or finite original-height cutoff is used.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json


def require(condition,message):
    if not condition:
        raise ValueError(message)


def joint_three_prime_bound():
    """One actual five-cell domain controls the old square and cylinder sums."""
    def simplex(size, budget):
        yield (F(0),)*size
        for j in range(size):
            yield tuple(budget if i == j else F(0) for i in range(size))

    roots = (0, 0, 1, 1, 1)
    cap = F(937, 24)
    counts = vertices = 0
    minimum_denominator = minimum_margin = None
    maximum = F(0)
    witness = None
    for deficits, alpha, beta, late, z in product(
            simplex(5, F(1, 2)), simplex(2, F(1, 4)),
            simplex(5, F(1, 4)), simplex(5, F(1, 72)), (F(3, 4), F(1))):
        widths = [1-d for d in deficits]
        x = sum(widths)/9
        cells = [widths[j]*(z-alpha[roots[j]]-beta[j])/9-late[j]
                 for j in range(5)]
        s = sum(cells)
        root_mass = [sum(cells[j] for j in range(5) if roots[j] == r)
                     for r in (0, 1)]
        root_width = [sum(widths[j] for j in range(5) if roots[j] == r)/3
                      for r in (0, 1)]
        require(min(cells) >= 0 and s >= F(1, 4), 'actual five-cell positivity')
        require(sum(root_width) == 3*x and min(root_width) >= F(1, 2),
                'same pure-ternary roots in the square and cylinder bounds')
        for selected, tail_choice, norm_choice, cap_root, cap_cell in product(
                range(2), range(2), range(2), range(2), range(5)):
            d = z-alpha[selected]
            e = z-alpha[1-selected]
            extra = d if tail_choice == 0 else F(2, 3)*e
            U = (s+3*root_mass[selected]+extra
                 +F(1, 4)*(x+root_width[selected]+1)
                 +F(5, 8)*(x+root_width[norm_choice]+1))
            T = root_mass[cap_root]+cells[cap_cell]+z/18+x/4+F(1, 8)
            denominator = s-T/5
            numerator = F(5, 3)*U-T/5
            require(U >= s and T >= 0 and denominator > 0,
                    'positive branch domain and monotonicity in the cylinder cap')
            margin = cap*denominator-numerator
            require(margin >= 0, 'joint square/cylinder branch proves Gamma357<=937/24')
            value = numerator/denominator
            counts += 1
            minimum_denominator = denominator if minimum_denominator is None else min(minimum_denominator, denominator)
            minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
            if value > maximum:
                maximum = value
                witness = {
                    'deficits': list(map(str, deficits)), 'alpha': list(map(str, alpha)),
                    'beta': list(map(str, beta)), 'late': list(map(str, late)), 'z': str(z),
                    'cell_masses': list(map(str, cells)), 's': str(s),
                    'raw_old_square_bound': str(U), 'raw_cylinder_cap': str(T),
                    'old_square_bound': str(U/s), 'old_cylinder_cap': str(T/s),
                    'branches': [selected, tail_choice, norm_choice, cap_root, cap_cell],
                }
        vertices += 1
    require(vertices == 1296 and counts == 103680 and maximum == cap,
            'complete multi-affine vertex and branch domain')
    require(minimum_margin == 0 and minimum_denominator == F(53, 360),
            'exact relaxed margin and positive denominator')
    missing = []
    for name, G, R in (
            ('modulus3_absent', F(215, 24), F(17, 12)),
            ('modulus9_absent_or_ineffective', F(55, 4), F(47, 24))):
        bound = (F(5, 3)*G-R/5)/(1-R/5)
        require(R < 5 and bound < cap, 'missing pure-class branch is strictly smaller')
        missing.append({'case': name, 'old_square': str(G), 'old_cylinder_cap': str(R),
                        'three_prime_square': str(bound)})
    require(witness['old_square_bound'] == '191/14'
            and witness['old_cylinder_cap'] == '15/7',
            'the joint extremum does not independently attain the old square maximum55/4')
    return {
        'law': 'uniform on the complete actual survivor set, arbitrary finite powers of3,5,7',
        'Gamma357_upper': str(cap), 'previous_separate_upper': str(F(1889, 48)),
        'strict_improvement': str(F(1889, 48)-cap),
        'parameter_vertices': vertices, 'affine_branches': counts,
        'minimum_denominator': str(minimum_denominator), 'minimum_scaled_margin': str(minimum_margin),
        'relaxation_maximizer': witness, 'missing_pure_cases': missing,
        'scope': 'Upper bound from a shared actual-parameter relaxation; no actual-family sharpness or new tail cutoff asserted.',
    }


def signed_two_level_three_prime_bound():
    """Signed mixed-7 deletion retains the actual zero-7 test root and cell."""
    def simplex(size, budget):
        yield (F(0),)*size
        for j in range(size):
            yield tuple(budget if i == j else F(0) for i in range(size))

    roots = (0, 0, 1, 1, 1)
    cap = F(3849, 106)
    vertices = layouts = 0
    minimum_margin = minimum_denominator = None
    maximum_old_bound = F(0)
    witness = None
    for deficits, alpha, beta, late, z in product(
            simplex(5, F(1, 2)), simplex(2, F(1, 4)),
            simplex(5, F(1, 4)), simplex(5, F(1, 72)), (F(3, 4), F(1))):
        widths = [1-d for d in deficits]
        x = sum(widths)/9
        available = [z-alpha[roots[j]]-beta[j] for j in range(5)]
        cells = [widths[j]*available[j]/9-late[j] for j in range(5)]
        s = sum(cells)
        root_mass = [sum(cells[j] for j in range(5) if roots[j] == r)
                     for r in (0, 1)]
        root_width = [sum(widths[j] for j in range(5) if roots[j] == r)/3
                      for r in (0, 1)]
        require(min(cells) >= 0 and s >= F(1, 4), 'signed-bound actual-cell positivity')
        require(min(available) >= F(1, 4), 'positive residual 5-availability')
        raw_square = {}
        for selected, cell in product(range(2), range(5)):
            coefficients = [3+2*(roots[j] == selected)+2*(j == cell) for j in range(5)]
            pure_square = (s+3*root_mass[selected]
                           +(3+2*(roots[cell] == selected))*cells[cell]
                           +(max(coefficients[j]*available[j] for j in range(5))
                             +max(available))/18)
            eta_square = (x+root_width[selected]
                          +(3+2*(roots[cell] == selected))*widths[cell]/9
                          +F(max(coefficients)+1, 18))
            raw_square[selected, cell] = (pure_square+eta_square/4
                                         +5*(x+max(root_width)+1)/8)
        global_square = max(raw_square.values())
        maximum_old_bound = max(maximum_old_bound, global_square/s)
        unweighted_cap = (max(root_mass)+max(cells)+max(available)/18
                          +sum(widths)/36+max(root_width)/12+max(widths)/36+F(1, 72))
        denominator = s-unweighted_cap/5
        require(denominator > 0, 'all weighted-max branch slopes are positive')
        minimum_denominator = denominator if minimum_denominator is None else min(minimum_denominator, denominator)
        for selected, cell in product(range(2), range(5)):
            weights = [cap-(1+(roots[j] == selected)+(j == cell))**2 for j in range(5)]
            require(min(weights) >= 0 and max(weights) == cap-1, 'valid signed deletion weights')
            weighted_parts = [
                max(sum(weights[j]*cells[j] for j in range(5) if roots[j] == r) for r in (0, 1)),
                max(weights[j]*cells[j] for j in range(5)),
                max(weights[j]*available[j] for j in range(5))/18,
                sum(weights[j]*widths[j] for j in range(5))/36,
                max(sum(weights[j]*widths[j] for j in range(5) if roots[j] == r) for r in (0, 1))/36,
                max(weights[j]*widths[j] for j in range(5))/36,
                (cap-1)/72,
            ]
            weighted_cap = sum(weighted_parts)
            margin = cap*s-F(6, 5)*raw_square[selected, cell]-F(7, 15)*global_square-weighted_cap/5
            require(margin >= 0, 'signed two-level Gamma357 bound')
            if minimum_margin is None or margin < minimum_margin:
                minimum_margin = margin
                witness = {
                    'deficits': list(map(str, deficits)), 'alpha': list(map(str, alpha)),
                    'beta': list(map(str, beta)), 'late': list(map(str, late)), 'z': str(z),
                    'selected_root_cell': [selected, cell],
                    'cell_masses': list(map(str, cells)), 's': str(s),
                    'selected_raw_square': str(raw_square[selected, cell]),
                    'global_raw_square': str(global_square),
                    'weighted_cap_parts': list(map(str, weighted_parts)),
                    'weighted_cap': str(weighted_cap), 'scaled_margin': str(margin),
                }
            layouts += 1
        vertices += 1
    require(vertices == 1296 and layouts == 12960 and minimum_margin == 0,
            'complete signed vertex/layout domain with exact relaxed equality')
    missing = []
    for name, G, R in (
            ('modulus3_absent', F(215, 24), F(17, 12)),
            ('modulus9_absent_or_ineffective', F(593, 48), F(47, 24))):
        bound = (F(5, 3)*G-R/5)/(1-R/5)
        require(R < 5 and bound < cap, 'same-law missing-class fallback')
        missing.append({'case': name, 'old_square': str(G), 'old_cylinder_cap': str(R),
                        'three_prime_square': str(bound)})
    return {
        'law': 'uniform on the complete actual survivor set, arbitrary finite powers of3,5,7',
        'Gamma357_upper': str(cap), 'previous_joint_upper': str(F(937, 24)),
        'strict_improvement': str(F(937, 24)-cap),
        'zero_seven_square_coefficient': str(F(6, 5)),
        'remaining_old_square_coefficient': str(F(7, 15)),
        'parameter_vertices': vertices, 'selected_layout_vertex_pairs': layouts,
        'minimum_scaled_margin': str(minimum_margin),
        'minimum_unweighted_denominator': str(minimum_denominator),
        'two_level_old_square_envelope_maximum': str(maximum_old_bound),
        'relaxation_equality': witness, 'missing_pure_cases': missing,
        'scope': 'Continuous-domain ordinary proof with exact vertices; no actual-family sharpness, optimal supported-law, or new tail cutoff claim.',
    }


def signed_young_three_prime_bound(vertex_data=None):
    """Fixed Young weights retain the two actual zero-five source norms.

    The ordinary proof supplies the actual-family extraction, complete
    tails and separate convexity. Every rational target margin is checked
    here; the source hash identifies this verifier, not a Lean proof.
    """
    def simplex(size, budget):
        yield (F(0),)*size
        for j in range(size):
            yield tuple(budget if i == j else F(0) for i in range(size))

    roots = (0, 0, 1, 1, 1)
    choices = tuple(product(range(2), range(5)))
    bases = {choice: tuple(1+int(roots[l] == choice[0])+int(l == choice[1])
                           for l in range(5)) for choice in choices}
    cap, previous = F(4351, 120), F(3849, 106)
    young = (F(9, 8), F(1))
    minimum_margin = minimum_denominator = None
    witnesses = []
    records = []
    old_obstruction = None
    vertices = 0
    for index, (deficits, alpha, beta, late, z) in enumerate(product(
            simplex(5, F(1, 2)), simplex(2, F(1, 4)),
            simplex(5, F(1, 4)), simplex(5, F(1, 72)), (F(3, 4), F(1)))):
        widths = tuple(1-d for d in deficits)
        eta = tuple(w/9 for w in widths)
        available = tuple(z-alpha[roots[l]]-beta[l] for l in range(5))
        cells = tuple(widths[l]*available[l]/9-late[l] for l in range(5))
        s = sum(cells)
        require(min(cells) >= 0 and s >= F(1, 4) and min(available) >= F(1, 4),
                'Young-bound actual five-cell domain')
        pure_maximum = max(sum(w*b*b for w,b in zip(eta,bb))
                           +max(F(b+1,9) for b in bb) for bb in bases.values())
        square = {}
        for (r,j), bb in bases.items():
            t = young[r]
            square[r,j] = (sum(n*b*b for n,b in zip(cells,bb))
                +(t/4)*sum(w*b*b for w,b in zip(eta,bb))
                +max((d+t/4)*F(b+1,9) for d,b in zip(available,bb))
                +(F(3,8)+1/(4*t))*pure_maximum)
        global_square = max(square.values())
        unweighted = (max(sum(cells[l] for l in range(5) if roots[l] == r)
                          for r in range(2))+max(cells)+max(available)/18
            +sum(widths)/36
            +max(sum(widths[l] for l in range(5) if roots[l] == r)
                 for r in range(2))/36+max(widths)/36+F(1,72))
        denominator = s-unweighted/5
        require(denominator > 0, 'Young-bound positive surviving denominator')
        minimum_denominator = denominator if minimum_denominator is None else min(minimum_denominator,denominator)
        for (r,j), bb in bases.items():
            weights = tuple(cap-b*b for b in bb)
            require(min(weights) >= 0 and max(weights) == cap-1,
                    'Young-bound same original root/cell deletion floor')
            parts = (
                max(sum(weights[l]*cells[l] for l in range(5) if roots[l] == rr)
                    for rr in range(2)),
                max(weights[l]*cells[l] for l in range(5)),
                max(weights[l]*available[l] for l in range(5))/18,
                sum(weights[l]*widths[l] for l in range(5))/36,
                max(sum(weights[l]*widths[l] for l in range(5) if roots[l] == rr)
                    for rr in range(2))/36,
                max(weights[l]*widths[l] for l in range(5))/36,
                (cap-1)/72)
            weighted_cap = sum(parts)
            margin = cap*s-F(6,5)*square[r,j]-F(7,15)*global_square-weighted_cap/5
            require(margin >= 0, 'Every weighted-cross signed357 target margin')
            minimum_margin = margin if minimum_margin is None else min(minimum_margin,margin)
            records.append([index,r,j,str(square[r,j]),str(global_square),
                            str(weighted_cap),str(margin)])
            witness = {'vertex': index, 'selected_root_cell': [r,j],
                       's': str(s), 'selected_raw_square': str(square[r,j]),
                       'global_raw_square': str(global_square),
                       'weighted_cap_parts': list(map(str,parts)),
                       'scaled_margin': str(margin)}
            if margin == 0:
                witnesses.append(witness)
            if index == 398 and (r,j) == (0,1):
                require(square[r,j] == F(61,18) and pure_maximum == F(5,2)
                        and margin == F(163,43200), 'Strictly improved old obstruction')
                old_obstruction = witness
        if vertex_data is not None:
            vertex_data.append((index,alpha,beta,late,widths,eta,available,cells,
                                s,pure_maximum,square,global_square))
        vertices += 1
    require(vertices == 1296 and len(records) == 12960 and minimum_margin == 0,
            'Complete weighted-cross continuous-domain certificate')
    require(minimum_denominator == F(53,360) and len(witnesses) == 12,
            'Exact weighted-cross denominator and equality count')
    missing = []
    for name,G,R in (
            ('modulus3_absent',F(215,24),F(17,12)),
            ('modulus9_absent_or_ineffective',F(593,48),F(47,24))):
        bound = (F(5,3)*G-R/5)/(1-R/5)
        require(R < 5 and bound < cap, 'Weighted-cross same-law missing-class fallback')
        missing.append({'case':name,'old_square':str(G),'old_cylinder_cap':str(R),
                        'three_prime_square':str(bound)})
    return {
        'law':'uniform on the complete actual survivor set, arbitrary finite powers of3,5,7',
        'Gamma357_upper':str(cap),'previous_signed_upper':str(previous),
        'strict_improvement':str(previous-cap),'young_weights_by_root':list(map(str,young)),
        'positive_five_diagonal_coefficient':'1/4',
        'positive_five_pair_coefficient':'1/8',
        'zero_seven_square_coefficient':'6/5','remaining_old_square_coefficient':'7/15',
        'parameter_vertices':vertices,'selected_layout_vertex_pairs':len(records),
        'minimum_scaled_margin':str(minimum_margin),
        'minimum_unweighted_denominator':str(minimum_denominator),
        'layout_margin_sha256':hashlib.sha256(json.dumps(records,separators=(',',':')).encode()).hexdigest(),
        'relaxation_equalities':witnesses,'previous_obstruction':old_obstruction,
        'missing_pure_cases':missing,
        'verifier_sha256':hashlib.sha256(read_artifact_bytes(Path(__file__))).hexdigest(),
        'scope':'Same actual probability and original-label floors; full geometric tails and separately concave target margins; ordinary proof, not Lean, sharpness or unrestricted resolution.',
    }


def same_original5_deletion_three_prime_bound(source, vertices):
    """Retain the original unit-cofactor5 test in square and pure3 deletion.

    Only the original unit-cofactor5 label has its cap reduced to h.
    The strip comparison subtracts (1/5-h)*sum eta*(2*b+1) from
    the previous selected Young square, retaining every other label cap.
    The incident test uses h in [0,1/5] and the signed actual-cell lower
    bound eta*(h-alpha1-beta)-late. The fixed-target margin is separately
    concave in the original five parameter groups and h. Its two h endpoints
    therefore suffice; the other seven layouts keep the previous formulas.
    """
    roots = (0, 0, 1, 1, 1)
    choices = tuple(product(range(2), range(5)))
    bases = {choice: tuple(1+int(roots[l] == choice[0])+int(l == choice[1])
                           for l in range(5)) for choice in choices}
    cap, previous = F(5761,159), F(4351,120)
    require(F(source['Gamma357_upper']) == previous and cap >= 16,
            'Same-original5 source and nonnegative pointwise deletion bound')
    counts = {'incident':0, 'other':0}
    minima = {'incident':None, 'other':None}
    endpoint_minima = {'0':None, '1/5':None}
    records, witnesses = [], []
    for row in vertices:
        index, alpha, beta, late, widths, eta, available, cells, s, pure_maximum, square, global_square = row
        require(F(1,2) <= sum(eta) <= F(5,9) and 0 < s <= sum(eta),
                'Same-original5 raw source domain')
        for (r,j), bb in bases.items():
            incident = r == 1 and j >= 2
            group = 'incident' if incident else 'other'
            weights = tuple(cap-b*b for b in bb)
            require(min(weights) >= 0 and min(cap-(b+1)**2 for b in bb) >= 0,
                    'Original5 pointwise signed square floor is nonnegative')
            root_caps = tuple(sum(weights[l]*cells[l] for l in range(5) if roots[l] == rr)
                              for rr in range(2))
            remaining_parts = (
                max(weights[l]*cells[l] for l in range(5)),
                max(weights[l]*available[l] for l in range(5))/18,
                sum(weights[l]*widths[l] for l in range(5))/36,
                max(sum(weights[l]*widths[l] for l in range(5) if roots[l] == rr)
                    for rr in range(2))/36,
                max(weights[l]*widths[l] for l in range(5))/36,
                (cap-1)/72)
            for h in ((F(0),F(1,5)) if incident else (None,)):
                selected_square = square[r,j]
                root_cap = max(root_caps)
                joint_lower = None
                if incident:
                    strip_coefficient = sum(w*(2*b+1) for w,b in zip(eta,bb))
                    selected_square = square[r,j]-(F(1,5)-h)*strip_coefficient
                    joint_lower = sum((2*bb[l]+1)
                        *(eta[l]*(h-alpha[1]-beta[l])-late[l]) for l in (2,3,4))
                    # Signed lower bounds preserve separate affinity even
                    # when the relaxed lower bound is negative.
                    root_cap = max(root_caps[0],root_caps[1]-joint_lower)
                weighted_cap = root_cap+sum(remaining_parts)
                margin = cap*s-F(6,5)*selected_square-F(7,15)*global_square-weighted_cap/5
                require(margin >= 0, 'Every same-original5 endpoint/layout target margin')
                counts[group] += 1
                minima[group] = margin if minima[group] is None else min(minima[group],margin)
                if incident:
                    key = str(h)
                    endpoint_minima[key] = margin if endpoint_minima[key] is None else min(endpoint_minima[key],margin)
                records.append([index,r,j,None if h is None else str(h),
                                str(selected_square),str(global_square),str(weighted_cap),str(margin)])
                if margin == 0:
                    witnesses.append({'vertex':index,'selected_root_cell':[r,j],
                        'original_five_mass':None if h is None else str(h),
                        's':str(s),'selected_raw_square':str(selected_square),
                        'global_raw_square':str(global_square),'weighted_cap':str(weighted_cap),
                        'scaled_margin':str(margin)})
    require(len(vertices) == 1296 and counts == {'incident':7776,'other':9072},
            'All original layouts and original5 endpoint vertices')
    require(minima == {'incident':F(1,10800),'other':F(0)} and len(witnesses) == 6,
            'Exact same-original5 margins and relaxation equalities')
    missing = source['missing_pure_cases']
    for case in missing:
        require(F(case['three_prime_square']) < cap, 'Same-original5 missing-class fallback')
    return {
        'law':'uniform on the complete actual survivor set, arbitrary finite powers of3,5,7',
        'Gamma357_upper':str(cap),'previous_signed_young_upper':str(previous),
        'strict_improvement':str(previous-cap),'original_five_mass_endpoints':['0','1/5'],
        'separately_concave_parameter_groups':['pure_three_deficits','mixed_five_root_removal',
            'mixed_five_cell_removal','deeper_mixed_removal','pure_five_survivor_mass',
            'original_unit_five_test_mass'],
        'signed_joint_lower_bound':'eta_l*(h-alpha_1-beta_l)-late_l',
        'pure_three_root_cap':'max(A_0,A_1-sum_root1 (2*b_l+1)*signed_joint_lower_bound)',
        'incident_selected_layouts':[[1,j] for j in (2,3,4)],
        'selected_young_weight':'1',
        'selected_square_strip_gain':'(1/5-h)*sum_l eta_l*(2*b_l+1)',
        'reduced_five_cap_label':'original unit-cofactor5 only',
        'positive_five_pair_coefficient':'1/8','zero_seven_square_coefficient':'6/5',
        'remaining_old_square_coefficient':'7/15','pure_three_deletion_coefficient':'1/5',
        'parameter_vertices':len(vertices),'selected_layout_endpoint_pairs':len(records),
        'layout_group_counts':counts,'minimum_scaled_margin':{k:str(v) for k,v in minima.items()},
        'incident_endpoint_minima':{k:str(v) for k,v in endpoint_minima.items()},
        'minimum_unweighted_denominator':source['minimum_unweighted_denominator'],
        'layout_margin_sha256':hashlib.sha256(json.dumps(records,separators=(',',':')).encode()).hexdigest(),
        'relaxation_equalities':witnesses,'missing_pure_cases':missing,
        'verifier_sha256':hashlib.sha256(read_artifact_bytes(Path(__file__))).hexdigest(),
        'scope':'The same original5 event constrains selected square and pure3 deletion; global positive7 square retains its independent test; complete tails and separately concave endpoint reduction; ordinary proof, not Lean, actual-family sharpness or unrestricted resolution.',
    }


def compute_certificate():
    y,a=F(1,4),F(7,8)
    cap=F(55,4)
    require(a-2*y==F(3,8)>0,'positive-positive lcm coefficient mismatch')
    require(a-y==F(5,8)>0,'combined lcm coefficient mismatch')
    records=[]
    denominators=[]
    for (w,v),(alpha,beta),z in product(
            ((F(1,2),F(1)),(F(1),F(1,2)),(F(1),F(1))),
            ((F(0),F(0)),(y,F(0)),(F(0),y)),(1-y,F(1))):
        x=(w+v)/3
        d,e=z-alpha,z-beta
        # Shift all deep mixed deletion to the unselected root, then
        # enlarge it to y/6. The proof shows both operations increase
        # the selected-root envelope while preserving positive denominators.
        n=w*d/3
        m=v*e/3-y/6
        require(n>=F(1,12)>0 and m>=F(1,24)>0,
                'relaxed root positivity failed')
        s=n+m
        denominators.append(s)
        for pure_branch,extra in (('selected',d),('other',F(2,3)*e)):
            for norm_branch,root_width in (('selected',w),('other',v)):
                # The actual full bound takes the maximum over these
                # four affine branches. Every branch is checked separately.
                numerator=3*n+extra+y*(x+w+1)+(a-y)*(x+root_width+1)
                value=1+numerator/s
                require(value<=cap,'a coupled uniform Gamma branch exceeds55/4')
                records.append({'w_v_alpha_beta_z':list(map(str,(w,v,alpha,beta,z))),
                                'pure_branch':pure_branch,'norm_branch':norm_branch,
                                'value':str(value)})
    require(len(denominators)==18 and len(records)==72,'vertex/branch count mismatch')
    maximum=max(F(row['value']) for row in records)
    require(maximum==cap,'exact coupled envelope maximum mismatch')
    x,z=F(5,6),1-y
    absent_denominator=x*z-y/2
    require(absent_denominator>0,'absent-modulus-3 denominator is not positive')
    absent=1+(2*z+a*x+2*a)/absent_denominator
    require(absent==F(215,24)<cap,'absent-modulus-3 branch failed')
    # The old57/4 budget vertex is realizable as an infinite-height limit.
    w,v,alpha,beta,z=F(1,2),F(1),F(0),y,1-y
    x=(w+v)/3
    n=w*(z-alpha)/3
    m=v*(z-beta)/3-y/6
    old=1+(3*n+(z-alpha)+a*x+2*a)/(n+m)
    new=1+(3*n+(z-alpha)+y*(x+w+1)+(a-y)*(x+v+1))/(n+m)
    require(old==F(57,4) and new==F(55,4),'shared-layout improvement at old extremum failed')
    young_vertex_data=[]
    young_source=signed_young_three_prime_bound(young_vertex_data)
    return {'schema':'uniform-gamma-cofactor-coupling-v1','prime_support':[3,5],
            'Gamma_bound':str(cap),'same_law':'uniform complete survivor law',
            'positive_lcm_coefficient':str(a),'zero_to_positive_coefficient':str(y),
            'remaining_Gamma_coefficient':str(a-y),
            'parameter_vertex_count':18,'affine_branch_count':72,
            'minimum_vertex_survivor_density':str(min(denominators)),
            'maximizers':[row for row in records if F(row['value'])==maximum],
            'absent_modulus_3_bound':str(absent),
            'absent_modulus_3_denominator':str(absent_denominator),
            'old_budget_extremum':{'old_envelope':str(old),'coupled_envelope':str(new),
                                   'n':str(n),'m':str(m)},
            'shared_three_prime_parameters':joint_three_prime_bound(),
            'signed_two_level_three_prime_parameters':signed_two_level_three_prime_bound(),
            'signed_young_three_prime_parameters':young_source,
            'same_original5_deletion_three_prime_parameters':
                same_original5_deletion_three_prime_bound(young_source,young_vertex_data)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--write',action='store_true',help='Regenerate the full exact certificate.')
    mode.add_argument('--check',action='store_true',help='Check the full certificate; this is the default.')
    args=parser.parse_args()
    path=(Path(__file__).resolve().parent / 'certificates/uniform_gamma_cofactor_certificate.json')
    expected=compute_certificate()
    if args.write:
        write_certificate_text(path, json.dumps(expected,indent=2)+'\n', encoding='utf-8')
    else:
        def unique(pairs):
            values={}
            for key,value in pairs:
                require(key not in values,'Duplicate certificate key: '+key)
                values[key]=value
            return values
        data=json.loads(read_artifact_text(path),object_pairs_hook=unique)
        require(data==expected,'fixed certificate differs from exact recomputation')
    print('Verified all72 continuous-envelope branches: uniform Gamma35 <=55/4.')
    print('Positive denominators and absent-modulus-3 bound215/24 verified; '
          'the old57/4 extremal budget now has coupled bound55/4.')
    print('Verified103680 shared-parameter branches: uniform Gamma357<=937/24; '
          'all denominator and missing-pure-class checks passed.')
    print('Verified12960 signed two-level layout-vertices: uniform Gamma357<=3849/106; '
          'both missing-pure-class bounds are smaller on the same law.')
    print('Verified12960 weighted-cross layout-vertices: uniform Gamma357<=4351/120; '
          'same original floors, complete tails and both missing-pure-class bounds.')
    print('Verified16848 original-unit5 endpoint/layout pairs: uniform Gamma357<=5761/159; '
          'only the original unit5 cap is reduced; all other labels and complete tails remain.')


if __name__=='__main__':
    main()
