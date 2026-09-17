#!/usr/bin/env python3
"""Verify exact constants for general head laws and block tail obstructions.

Only the standard library is used. All comparisons use integers or
fractions. The arbitrary-height block theorem and cylinder estimates
remain ordinary mathematical proofs; this is not Lean certification.
The default run reads and checks the fixed adjacent JSON certificate.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product as cartesian_product
from math import gcd, isqrt, prod
from pathlib import Path
import argparse
import json

HEAD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
               37, 41, 43, 47, 53, 59, 61, 67, 71, 73)


from star_block.base import *

def head_mixed_mass_improvement():
    """Couple actual head density and cylinder load before deleting prime 7."""
    from runpy import run_path
    source = run_path(str((Path(__file__).resolve().parents[1] / 'elementary-checks/verify_joint_density_certificate.py')))
    vertices = source['budget_vertices']
    roots = (0, 0, 1, 1, 1)
    minimum, witness, count = None, None, 0
    for deficits, alpha, beta, late, z in cartesian_product(
            vertices(5, F(1, 2)), vertices(2, F(1, 4)),
            vertices(5, F(1, 4)), vertices(5, F(1, 72)), (F(3, 4), F(1))):
        w = [1-d for d in deficits]
        x = sum(w)/9
        cells = [w[j]*(z-alpha[roots[j]]-beta[j])/9-late[j] for j in range(5)]
        mass = sum(cells)
        require(min(cells) >= 0 and mass >= F(1, 4) and x*z > 0,
                'positive actual-cell parameter domain')
        root_mass = max(sum(cells[j] for j in range(5) if roots[j] == r)
                        for r in (0, 1))
        raw_load = root_mass+max(cells)+z/18+x/4+F(1, 8)
        lower = (mass-raw_load/5)/(x*z)
        require(lower >= F(53, 135), 'coupled mixed-head survival lower bound')
        if minimum is None or lower < minimum:
            minimum = lower
            witness = {'pure_ternary_deficits': list(map(str, deficits)),
                       'first_deletions': list(map(str, alpha)),
                       'second_deletions': list(map(str, beta)),
                       'late_deletions': list(map(str, late)), 'z': str(z),
                       'x': str(x), 'cells': list(map(str, cells)),
                       'mass': str(mass), 'raw_load_upper': str(raw_load)}
        count += 1
    require(count == 1296 and minimum == F(53, 135), 'sharp coupled relaxation')
    missing = []
    for name, x in [('modulus3_absent', F(5, 6)),
                    ('modulus9_absent_or_ineffective', F(11, 18))]:
        z = F(3, 4)
        lower = (x*z-F(1, 8)-(z/2+x/4+F(1, 8))/5)/(x*z)
        require(lower >= minimum, 'missing low-pure-class branch')
        missing.append({'case': name, 'survival_lower': str(lower)})
    # Positive actual head and tail violations can be disjoint.
    r, q = 23, 29
    moduli = [3, 5, 7, 15]+[3*r**f*q for f in range(1, q+1)]
    require(len(set(moduli)) == len(moduli), 'disjoint-event original moduli')
    current_residues = []
    for f in range(1, q+1):
        power = r**f
        multiplier = next(k for k in range(3*q)
                          if power*k % 3 == 2 and power*k % q == f-1)
        residue = power*multiplier
        require(residue % 3 == 2 and residue % power == 0,
                'tail classes all miss the mixed-head ternary root')
        current_residues.append(residue % q)
    require(set(current_residues) == set(range(q)), 'entire forced tail fibre')
    return {'vertices_checked': count, 'pure_product_survival_lower': str(minimum),
            'mixed_head_mass_upper': str(1-minimum), 'relaxation_minimizer': witness,
            'missing_pure_branches': missing,
            'disjoint_actual_events': {'mixed_head_class': '1 mod 15',
                'pure_head_classes': ['0 mod 3', '0 mod 5', '0 mod 7'],
                'head_bad_mass': '1/8', 'tail_bad_mass_lower': str(F(1, 2*r**q)),
                'intersection_mass': '0', 'tail_primes': [r, q],
                'original_modulus_count': len(moduli)},
            'scope': 'Exact P12 parameter extrema plus actual CRT regression; the arbitrary-height density inequality is an ordinary proof.'}



def cm1_actual_head_sharpness():
    """Actual CRT families make the mixed-357 pure-product bound sharp."""
    rows = []
    head_cases = {}
    for height, five_height in cartesian_product((3, 4, 5), (1, 2, 3)):
        ternary, quinary = 3**height, 5**five_height
        period = ternary*quinary
        pure_three = [(3, 0), (9, 4)] + [
            (3**a, 3**(a-1)-8) for a in range(3, height+1)]
        pure_five = [(5**b, 5**(b-1)-1) for b in range(1, five_height+1)]
        classes = pure_three + pure_five
        for b in range(1, five_height+1):
            first, second = 2*5**(b-1)-1, 3*5**(b-1)-1
            mixed = [(3, 2, first), (9, 2, second)] + [
                (3**a, 2*3**(a-1)-8, first) for a in range(3, height+1)]
            for modulus, residue, five_residue in mixed:
                joint = residue + modulus*(
                    (five_residue-residue)*pow(modulus, -1, 5**b) % 5**b)
                require(joint % modulus == residue and joint % 5**b == five_residue,
                        'actual CM2 mixed residue satisfies both CRT conditions')
                classes.append((modulus*5**b, joint))
        expected_moduli = {3**a*5**b for a in range(height+1)
                           for b in range(five_height+1) if a or b}
        require({modulus for modulus, residue in classes} == expected_moduli
                and len(classes) == len(expected_moduli),
                'CM2 construction has one class per nonunit divisor')
        pure_x = [value for value in range(ternary)
                  if all(value % modulus != residue for modulus, residue in pure_three)]
        pure_y = [value for value in range(quinary)
                  if all(value % modulus != residue for modulus, residue in pure_five)]
        survivors = [value for value in range(period)
                     if all(value % modulus != residue for modulus, residue in classes)]
        a_sum = sum((F(1, 3**a) for a in range(3, height+1)), F(0))
        r_sum = sum((F(1, 5**b) for b in range(1, five_height+1)), F(0))
        x, z = F(5, 9)-a_sum, 1-r_sum
        mass = x-r_sum
        require(F(len(pure_x), ternary) == x and F(len(pure_y), quinary) == z,
                'actual CM2 pure survivor densities')
        require(F(len(survivors), period) == mass, 'actual CM2 complete density')
        cell_order = (1, 7, 2, 5, 8)
        cells = [F(sum(value % 9 == cell for value in survivors), period)
                 for cell in cell_order]
        require(cells == [z/9-a_sum, z/9, (1-3*r_sum)/9,
                          (1-2*r_sum)/9, (1-2*r_sum)/9],
                'all five actual CM2 cell masses')
        first_max, second_max = (3-7*r_sum)/9, z/9
        raw_load = F(0)
        layout = []
        for a in range(height+1):
            for b in range(five_height+1):
                if not (a or b):
                    continue
                modulus = 3**a*5**b
                counts = Counter(value % modulus for value in survivors)
                actual = F(max(counts.values()), period)
                if b == 0:
                    expected = first_max if a == 1 else second_max if a == 2 else z/3**a
                else:
                    expected = x/5**b if a == 0 else F(1, modulus)
                require(actual == expected, 'actual CM2 maximum for every divisor cylinder')
                three_residue = (0 if a == 0 else 2 if a == 1 else
                                 7 if a == 2 else 3**(a-1)-2)
                five_residue = 0 if b == 0 else 4*5**(b-1)-1
                residue = three_residue if b == 0 else three_residue + 3**a*(
                    (five_residue-three_residue)*pow(3**a, -1, 5**b) % 5**b)
                color = ((1 if a <= 2 else 2) if b == 0 else
                         3 if a == 0 else 4 if a <= 2 else 5)
                require(F(counts[residue], period) == expected,
                        'five-color layout realizes each actual cylinder maximum')
                layout.append((modulus, residue, color))
                raw_load += actual
        for left, right in combinations(layout, 2):
            if left[2] == right[2]:
                require((left[1]-right[1]) % gcd(left[0], right[0]) != 0,
                        'old cylinders of the same color are disjoint')
        require(raw_load == (4+r_sum)/9+(1-r_sum)*a_sum,
                'complete actual CM2 cylinder sum')
        quotient = (mass-raw_load/5)/(x*z)
        require(quotient > F(53, 135), 'finite CM2 input above its limiting minimum')
        rows.append({'ternary_height': height, 'quinary_height': five_height,
                     'period': period, 'original_classes': len(classes),
                     'survivors': len(survivors), 'x': str(x), 'z': str(z),
                     'cell_order': list(cell_order), 'cell_masses': list(map(str, cells)),
                     'survivor_density': str(mass), 'raw_cylinder_sum': str(raw_load),
                     'CM2_expression': str(quotient)})
        head_cases[height, five_height] = (classes, layout, len(pure_x), len(pure_y),
                                          len(survivors), x, z, mass, raw_load)
    full_rows = []
    for height, five_height, seven_height in cartesian_product((3, 4), (1, 2), (1, 2)):
        (head_classes, layout, pure_x_count, pure_y_count, head_count,
         x, z, mass, raw_load) = head_cases[height, five_height]
        seven_period = 7**seven_height
        head_period = 3**height*5**five_height
        period = head_period*seven_period
        pure_seven = [(7**e, 7**(e-1)-1) for e in range(1, seven_height+1)]
        classes = head_classes + pure_seven
        mixed_seven = []
        for modulus, residue, color in layout:
            for e in range(1, seven_height+1):
                seven_residue = (color+1)*7**(e-1)-1
                joint = residue + modulus*(
                    (seven_residue-residue)*pow(modulus, -1, 7**e) % 7**e)
                require(joint % modulus == residue and joint % 7**e == seven_residue,
                        'actual colored prime-7 CRT class')
                mixed_seven.append((modulus*7**e, joint))
        classes += mixed_seven
        expected_moduli = {3**a*5**b*7**e for a in range(height+1)
                           for b in range(five_height+1) for e in range(seven_height+1)
                           if a or b or e}
        require({modulus for modulus, residue in classes} == expected_moduli
                and len(classes) == len(expected_moduli),
                'one actual class per nonunit 357 divisor')
        for left, right in combinations(mixed_seven, 2):
            require((left[1]-right[1]) % gcd(left[0], right[0]) != 0,
                    'all colored prime-7 mixed classes are pairwise disjoint')
        pure_z = [value for value in range(seven_period)
                  if all(value % modulus != residue for modulus, residue in pure_seven)]
        survivor_count = sum(all(value % modulus != residue for modulus, residue in classes)
                             for value in range(period))
        seven_sum = sum((F(1, 7**e) for e in range(1, seven_height+1)), F(0))
        seven_density = 1-seven_sum
        require(F(len(pure_z), seven_period) == seven_density,
                'actual pure-7 survivor density')
        actual_deleted = F(head_count*len(pure_z)-survivor_count, period)
        require(actual_deleted == raw_load*seven_sum,
                'final prime-7 union bound is an exact equality')
        survival = F(survivor_count, pure_x_count*pure_y_count*len(pure_z))
        ambient_survival = F(survivor_count, period)
        formula = (mass-raw_load*seven_sum/seven_density)/(x*z)
        require(survival == formula > F(53, 135), 'actual pure-product survivor probability')
        require(ambient_survival > F(53, 432), 'actual finite ambient survivor density')
        full_rows.append({'ternary_height': height, 'quinary_height': five_height,
                          'septenary_height': seven_height, 'period': period,
                          'original_classes': len(classes), 'survivors': survivor_count,
                          'prime7_mixed_classes': len(mixed_seven),
                          'prime7_deleted_ambient_density': str(actual_deleted),
                          'ambient_uncovered_density': str(ambient_survival),
                          'pure_product_survival': str(survival),
                          'pure_product_mixed_mass': str(1-survival)})
    a_sum, r_sum = F(1, 18), F(1, 4)
    x, z = F(5, 9)-a_sum, 1-r_sum
    mass = x-r_sum
    raw_load = (4+r_sum)/9+(1-r_sum)*a_sum
    require((mass, raw_load, (mass-raw_load/5)/(x*z)) ==
            (F(1, 4), F(37, 72), F(53, 135)), 'exact limiting CM2 input values')
    require(F(1, 6)/(1-F(1, 6)) == F(1, 5), 'limiting pure-7 normalized cylinder sum')
    ambient_limit = mass*F(5, 6)-raw_load*F(1, 6)
    require(ambient_limit == F(53, 135)*F(1, 2)*F(3, 4)*F(5, 6) == F(53, 432)
            and ambient_limit > F(5, 42), 'sharp uniform density and prior-density comparison')
    return {'actual_35_residue_cases': len(rows),
            'actual_cylinder_maxima_checked': sum(row['original_classes'] for row in rows),
            'limit_survivor_density': str(mass), 'limit_raw_cylinder_sum': str(raw_load),
            'old_cylinder_colors': 5, 'actual_357_residue_cases': len(full_rows),
            'limit_pure_product_survival': str((mass-raw_load/5)/(x*z)),
            'limit_pure_product_mixed_mass': str(1-(mass-raw_load/5)/(x*z)),
            'infimum_ambient_uncovered_density': str(ambient_limit),
            'head_cases': rows, 'full_head_cases': full_rows,
            'scope': 'Actual 357 families approach mixed mass 82/135 under their pure-survivor product law and ambient uncovered density 53/432. Every finite prime-7 union bound is exact; arbitrary-height sharpness is an ordinary proof.'}


def finite_head_sharp_density(actual_sharpness):
    """Exact all-parameter CM2 bound for heads dividing 3^H*35, H>=2."""
    import hashlib

    def add(*polynomials):
        out = [F(0)]*max(map(len, polynomials))
        for polynomial in polynomials:
            for i, coefficient in enumerate(polynomial):
                out[i] += coefficient
        return tuple(out)

    def scale(c, polynomial):
        return tuple(c*coefficient for coefficient in polynomial)

    def mul(left, right):
        out = [F(0)]*(len(left)+len(right)-1)
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                out[i+j] += a*b
        return tuple(out)

    def value(polynomial, a):
        return sum((c*a**i for i, c in enumerate(polynomial)), F(0))

    def vertex(size, index, budget):
        out = [(F(0),)]*size
        if index:
            out[index-1] = budget
        return out

    lower, upper = F(1, 27), F(1, 18)
    denominator, numerator = (F(40), F(-72)), (F(25), F(-102))
    roots = (0, 0, 1, 1, 1)
    unique, branch_count, zero_count = {}, 0, 0
    h2_count, h2_minimum = 0, None
    minimum_cell = F(1)

    def bernstein(polynomial):
        require(len(polynomial) == 3, 'degree at most two after clearing the target denominator')
        a, b, c = polynomial
        return (value(polynomial, lower),
                value(polynomial, lower)+(upper-lower)*(b+2*c*lower)/2,
                value(polynomial, upper))

    # For fixed A, each branch is affine separately in every simplex block
    # and z. Its complete vertex values therefore interpolate the whole domain.
    # Each such value is a quadratic in A; nonnegative Bernstein coefficients
    # certify every A in [1/27,1/18], rather than only sampled heights.
    for di, ai, bi, ti, z in cartesian_product(
            range(6), range(3), range(6), range(6), (F(4, 5), F(1))):
        deficits = vertex(5, di, (F(0), F(9)))
        alpha = vertex(2, ai, (F(1, 5),))
        beta = vertex(5, bi, (F(1, 5),))
        late = vertex(5, ti, (F(0), F(1, 5)))
        weights = [add((F(1),), scale(-1, d)) for d in deficits]
        x = scale(F(1, 9), add(*weights))
        cells = [add(scale(F(1, 9), mul(weights[j], add(
                    (z,), scale(-1, alpha[roots[j]]), scale(-1, beta[j])))),
                    scale(-1, late[j])) for j in range(5)]
        mass = add(*cells)
        base = add((F(0), z), scale(F(1, 5), x), (F(4, 45), F(1, 5)))
        for cell in cells:
            cell_min = min(value(cell, lower), value(cell, upper))
            require(cell_min > 0, 'positive cells throughout the A interval')
            minimum_cell = min(minimum_cell, cell_min)
        for root, cell in cartesian_product((0, 1), range(5)):
            root_mass = add(*(cells[j] for j in range(5) if roots[j] == root))
            load = add(base, root_mass, cells[cell])
            surviving = add(mass, scale(F(-1, 6), load))
            polynomial = add(mul(denominator, surviving),
                             scale(-1, mul(numerator, scale(z, x))))
            coefficients = bernstein(polynomial)
            require(min(coefficients) >= 0, 'all-height sharp-density Bernstein certificate')
            unique[polynomial] = coefficients
            branch_count += 1
            zero_count += int(all(c == 0 for c in polynomial))
            if di == ti == 0:
                h2_value = value(surviving, F(0))/(value(x, F(0))*z)
                require(h2_value >= F(37, 60), 'height-two exact vertex bound')
                h2_minimum = h2_value if h2_minimum is None else min(h2_minimum, h2_value)
                h2_count += 1
    require(branch_count == 12960 and len(unique) == 656 and zero_count == 20,
            'complete universal parameter and root-cell branch set')
    require(h2_count == 360 and h2_minimum == F(37, 60), 'sharp height-two vertex minimum')
    require(minimum_cell == F(1, 90), 'exact common vertex-cell lower bound')

    missing = []
    for name, x in [('modulus3_absent', (F(8, 9), F(-1))),
                    ('modulus9_absent_or_ineffective', (F(2, 3), F(-1)))]:
        z, u = F(4, 5), (F(4, 9), F(1))
        load = add(scale(z, u), scale(F(1, 5), x), scale(F(1, 5), u))
        surviving = add(scale(z, x), scale(F(-1, 5), u), scale(F(-1, 6), load))
        polynomial = add(mul(denominator, surviving),
                         scale(-1, mul(numerator, scale(z, x))))
        coefficients = bernstein(polynomial)
        require(min(coefficients) > 0, 'missing low-pure-class branch throughout the interval')
        h2_value = value(surviving, F(0))/(value(x, F(0))*z)
        require(h2_value >= F(37, 60), 'height-two missing-pure branch')
        missing.append({'case': name, 'polynomial_coefficients': list(map(str, polynomial)),
                        'Bernstein_coefficients': list(map(str, coefficients)),
                        'height_two_survival_lower': str(h2_value)})

    # The CM3--CM7 family attains equality symbolically for every H>=3.
    x, z = (F(5, 9), F(-1)), F(4, 5)
    mass, load = (F(16, 45), F(-1)), (F(7, 15), F(4, 5))
    require(all(c == 0 for c in add(
        mul(denominator, add(mass, scale(F(-1, 6), load))),
        scale(-1, mul(numerator, scale(z, x))))), 'all-height CM7 equality identity')
    ambient = add(scale(F(6, 7), mass), scale(F(-1, 7), load))
    require(ambient == (F(5, 21), F(-34, 35)), 'sharp ambient density as a function of A')
    require(value(ambient, F(1, 18)) == F(58, 315), 'sharp infinite-height density infimum')
    family_rows = []
    for row in actual_sharpness['full_head_cases']:
        if row['quinary_height'] != 1 or row['septenary_height'] != 1:
            continue
        height = row['ternary_height']
        require(height >= 3, 'CM7 sharp-family height domain')
        a_sum = F(1, 18)*(1-F(1, 3**(height-2)))
        expected_count = 58*3**(height-2)+17
        require(row['period'] == 35*3**height and row['survivors'] == expected_count,
                'reuse actual CM7 sharp-family residue counts')
        require(F(row['ambient_uncovered_density']) == value(ambient, a_sum)
                and F(row['pure_product_survival']) ==
                value(numerator, a_sum)/value(denominator, a_sum),
                'actual CM7 families attain both universal lower bounds')
        family_rows.append({'ternary_height': height, 'period': row['period'],
                            'survivors': expected_count,
                            'pure_product_survival': row['pure_product_survival']})
    require({row['ternary_height'] for row in family_rows} == {3, 4},
            'both existing squarefree-five-seven CM7 cases reused')

    classes315 = [(3, 0), (9, 4), (5, 0), (15, 11), (45, 37), (7, 0),
                  (21, 8), (63, 16), (35, 3), (105, 53), (315, 313)]
    expected_moduli = {3**a*5**b*7**c for a in range(3) for b in range(2)
                       for c in range(2) if a or b or c}
    require(len(classes315) == len(expected_moduli)
            and {m for m, r in classes315} == expected_moduli
            and all(0 <= r < m for m, r in classes315), 'one valid class per nonunit315 divisor')
    count315 = sum(all(v % m != r for m, r in classes315) for v in range(315))
    pure315 = [(3, 0), (9, 4), (5, 0), (7, 0)]
    pure_count = sum(all(v % m != r for m, r in pure315) for v in range(315))
    require(count315 == 74 and pure_count == 120 and F(count315, pure_count) == h2_minimum,
            'actual315 family attains the sharp height-two density')
    polynomial_rows = [{'coefficients': list(map(str, p)),
                        'Bernstein_coefficients': list(map(str, unique[p]))} for p in sorted(unique)]
    return {'parameter_interval': [str(lower), str(upper)],
            'all_height_survival_lower': '(25-102*A)/(40-72*A)',
            'all_height_mixed_mass_upper': '(15+30*A)/(40-72*A)',
            'ambient_density_lower': '5/21-34*A/35',
            'survivor_count_lower': '58*3^(H-2)+17 for H>=3',
            'infinite_height_density_infimum': '58/315',
            'parameter_vertices': 1296, 'root_cell_branches': branch_count,
            'unique_quadratics': len(unique), 'identically_zero_branches': zero_count,
            'minimum_Bernstein_coefficient': str(min(c for bs in unique.values() for c in bs)),
            'minimum_cell': str(minimum_cell),
            'coefficient_encoding': 'JSON sorted rational coefficient/Bernstein rows, separators comma and colon',
            'coefficient_sha256': hashlib.sha256(json.dumps(
                polynomial_rows, separators=(',', ':')).encode()).hexdigest(),
            'missing_pure_branches': missing,
            'height_two': {'parameter_vertices': 36, 'root_cell_branches': h2_count,
                           'pure_product_survival_lower': str(h2_minimum),
                           'mixed_mass_upper': str(1-h2_minimum),
                           'ambient_density_lower': str(F(74, 315)),
                           'period': 315, 'survivors': count315,
                           'pure_survivors': pure_count,
                           'extremizing_classes': [list(pair) for pair in classes315]},
            'actual_CM7_equality_cases': family_rows,
            'scope': 'For any distinct nonunit moduli dividing 3^H*35, all H>=2, arbitrary residues. Universal polynomial bounds are certified on the entire A interval; all-height CRT sharpness uses the ordinary CM3--CM7 construction. This is not a Lean kernel proof.'}


def sharp_head_unmarked_comparison(actual_sharpness):
    """The CM7 families simultaneously attain the full unmarked load law."""
    coordinates = {}
    coordinate_rows = []
    for prime, heights, centre in ((3, (3, 4), 5), (5, (1, 2), 2), (7, (1, 2), 2)):
        for height in heights:
            period = prime**height
            excluded = ([(3, 0), (9, 4)] + [
                (3**a, 3**(a-1)-8) for a in range(3, height+1)] if prime == 3 else
                [(prime**a, prime**(a-1)-1) for a in range(1, height+1)])
            survivors = [value for value in range(period)
                         if all(value % modulus != residue for modulus, residue in excluded)]
            density = F(len(survivors), period)
            require(density == 1-sum((F(1, prime**a) for a in range(1, height+1)), F(0)),
                    'sharp-head pure classes have exact disjoint exclusion mass')
            counts = Counter(sum(value % prime**a == centre % prime**a
                                 for a in range(1, height+1)) for value in survivors)
            tails = [F(1)]
            for a in range(1, height+1):
                tail = F(sum(number for count, number in counts.items() if count >= a),
                         len(survivors))
                require(tail == 1/(density*prime**a),
                        'every selected nested cylinder attains its exact pure-survivor cap')
                tails.append(tail)
            tails.append(F(0))
            atoms = {count+1: tails[count]-tails[count+1] for count in range(height+1)}
            require({count+1: F(number, len(survivors)) for count, number in counts.items()} == atoms,
                    'entire finite auxiliary count law, including its terminal atom')
            coordinates[prime, height] = (counts, atoms, len(survivors), density)
            coordinate_rows.append({'prime': prime, 'height': height, 'centre': centre,
                                    'pure_survivors': len(survivors),
                                    'count_histogram': [counts[count] for count in range(height+1)],
                                    'tail_probabilities': list(map(str, tails[1:-1]))})
    source_rows = actual_sharpness['full_head_cases']
    by_height = {(row['ternary_height'], row['quinary_height'], row['septenary_height']): row
                 for row in source_rows}
    expected_heights = set(cartesian_product((3, 4), (1, 2), (1, 2)))
    require(len(source_rows) == len(by_height) == 8 and set(by_height) == expected_heights,
            'exactly the eight existing CM7 full-head cases')
    rows = []
    for heights in sorted(expected_heights):
        observed, canonical = {1: 1}, {1: F(1)}
        total = 1
        for prime, height in zip((3, 5, 7), heights):
            counts, atoms, size, density = coordinates[prime, height]
            next_observed, next_canonical = Counter(), {}
            for load, number in observed.items():
                for count, frequency in counts.items():
                    next_observed[load*(count+1)] += number*frequency
            for load, probability in canonical.items():
                for factor, atom in atoms.items():
                    key = load*factor
                    next_canonical[key] = next_canonical.get(key, F(0))+probability*atom
            observed, canonical = next_observed, next_canonical
            total *= size
        require(sum(observed.values()) == total and sum(canonical.values()) == 1
                and {load: F(number, total) for load, number in observed.items()} == canonical,
                'entire complete-head product distribution equals the canonical law')
        mean = sum((F(load*number, total) for load, number in observed.items()), F(0))
        second = sum((F(load*load*number, total) for load, number in observed.items()), F(0))
        densities = [coordinates[p, h][3] for p, h in zip((3, 5, 7), heights)]
        require(mean == prod(1/density for density in densities), 'exact complete-head mean')
        require(second == prod(1+sum((F(2*a+1, p**a) for a in range(1, h+1)), F(0))/density
                               for p, h, density in zip((3, 5, 7), heights, densities)),
                'exact complete-layout second moment')
        source = by_height[heights]
        require(source['period'] == prod(p**h for p, h in zip((3, 5, 7), heights))
                and F(source['survivors'], total) == F(source['pure_product_survival'])
                and 1-F(source['survivors'], total) == F(source['pure_product_mixed_mass']),
                'same actual family as the existing CM7 survivor identity')
        rows.append({'heights': list(heights), 'pure_survivors': total,
                     'load_states': len(observed), 'mean': str(mean), 'second_moment': str(second),
                     'CM7_survival': source['pure_product_survival'],
                     'CM7_mixed_mass': source['pure_product_mixed_mass']})
    uniform_divisor_sum = prod(F(p, p-1) for p in (3, 5, 7))
    uniform_pair_sum = prod(1+F(3*p-1, (p-1)**2) for p in (3, 5, 7))
    require((uniform_divisor_sum, uniform_pair_sum) == (F(35, 16), F(35, 4)),
            'complete uniform divisor and ordered-pair sums for finite truncation errors')
    limiting_densities = (F(1, 2), F(3, 4), F(5, 6))
    limiting_mean = prod(1/density for density in limiting_densities)
    limiting_second = prod(1+F(3*p-1, (p-1)**2)/density
                           for p, density in zip((3, 5, 7), limiting_densities))
    require(limiting_mean == F(16, 5) and limiting_second == F(325, 18)
            and actual_sharpness['limit_pure_product_mixed_mass'] == '82/135',
            'simultaneous sharp limiting head mass, mean and second moment')
    return {'coordinate_cases': coordinate_rows, 'full_head_cases': rows,
            'limit_mixed_mass': '82/135', 'limit_mean': str(limiting_mean),
            'limit_second_moment': str(limiting_second),
            'uniform_divisor_sum': str(uniform_divisor_sum), 'uniform_pair_sum': str(uniform_pair_sum),
            'scope': 'Exact coordinate enumeration and product-law comparison for eight existing CM7 families. Their mixed mass and unmarked convex-comparison law are simultaneously sharp in the limit; the all-height argument is an ordinary proof.'}


def comb_stoploss_dual_transport():
    """Exact primal/dual witnesses for complete cylinder-cap tail sums."""
    rows = []
    for prime in (3, 5, 7):
        for height in range(2, 9):
            # Aggregate the p-2 escape groups at each depth; the final
            # group also includes the single surviving spine leaf.
            sizes = {d: (prime-2)*prime**(height-d)+(d == height)
                     for d in range(1, height+1)}
            total = ((prime-2)*prime**height+1)//(prime-1)
            require(sum(sizes.values()) == total, 'complete comb survivor groups')
            for threshold in range(2, height+1):
                optimum = F(prime**(height-threshold+1)-1,
                            (prime-2)*prime**height+1)
                demands = {d: optimum*size for d, size in sizes.items()}
                original = demands.copy()
                plan = {}
                for e in range(height, threshold-1, -1):
                    supply = F(prime**(height-e))
                    for d in range(e, 0, -1):
                        mass = min(supply, demands[d])
                        if mass:
                            plan[e, d] = mass
                        supply -= mass
                        demands[d] -= mass
                    require(supply == 0, 'nested transport uses every depth budget')
                require(all(mass == 0 for mass in demands.values()),
                        'nested transport gives every leaf the constant dual weight')
                for d in sizes:
                    require(sum(mass for (e, group), mass in plan.items() if group == d)
                            == original[d], 'group demand equality')
                    require(sum(mass/F(sizes[d]) for (e, group), mass in plan.items() if group == d)
                            == optimum, 'constant per-leaf dual coverage')
                for e in range(threshold, height+1):
                    # A full depth-e cylinder has p^(H-e) leaves. Dividing
                    # transported mass by this size gives its total dual budget.
                    budget = sum(mass/F(prime**(height-e))
                                 for (depth, d), mass in plan.items() if depth == e)
                    require(budget == 1, 'unit dual budget at each selected depth')
                uniform = sum((F(prime**(height-e), total)
                               for e in range(threshold, height+1)), F(0))
                require(uniform == optimum, 'uniform actual law attains the dual lower bound')
                rows.append({'branching': prime, 'height': height,
                             'first_charged_depth': threshold,
                             'survivor_count': total, 'minimum_cap_tail_sum': str(optimum),
                             'transport_nonzero_entries': len(plan)})
    require(len(rows) == 84, 'finite dual-transport regression count')
    return {'rows': rows, 'scope': 'Exact feasible primal and dual regressions; the all-height nested-transport proof is stated separately. Each tail objective has its own dual.'}


def homogeneous_comb_capacity():
    """Actual leaf-flow regressions and exact finite comb cap-sum witnesses."""
    def actual_flow(forbidden, beta):
        b1, b2, b3 = beta
        f1, f2, f3 = forbidden
        level2 = [0 if n//3 == f1 or n == f2 else min(b2, (3-int(f3//3 == n))*b3)
                  for n in range(9)]
        level1 = [min(b1, sum(level2[3*n:3*n+3])) for n in range(3)]
        return min(81, sum(level1))

    def comb_flow(beta):
        full = critical = beta[-1]
        for depth in (2, 1, 0):
            bound = 81 if depth == 0 else beta[depth-1]
            full, critical = min(bound, 3*full), min(bound, full+critical)
        return critical

    # All forbidden configurations, with profiles spanning degeneracy,
    # saturation equalities, both sides of them, and nonmonotone capacities.
    profiles = [(0, 0, 0), (54, 18, 6), (40, 20, 10), (81, 27, 9),
                (81, 28, 9), (80, 26, 8), (9, 40, 2), (1, 162, 81)]
    comparisons = strict = 0
    for beta in profiles:
        bound = comb_flow(beta)
        require(bound == actual_flow((0, 6, 24), beta), 'explicit comb matches recursion')
        for forbidden in cartesian_product(range(3), range(9), range(27)):
            value = actual_flow(forbidden, beta)
            require(value >= bound, 'comb minimizes root flow')
            comparisons += 1
            strict += value > bound
    laws = []
    for height in range(1, 7):
        law = {}
        for value in range(3**height):
            digits, weight = value, F(1)
            for depth in range(1, height+1):
                digit, digits = digits % 3, digits//3
                if digit == 0:
                    weight = F(0)
                    break
                weight /= 2
                if digit == 1:
                    weight /= 3**(height-depth)
                    break
            if weight:
                law[value] = weight
        require(sum(law.values(), F(0)) == 1, 'actual binary-split comb law')
        caps = []
        for depth in range(1, height+1):
            masses = [F(0)]*3**depth
            for value, weight in law.items():
                masses[value % 3**depth] += weight
            cap = max(masses)
            require(cap == F(1, 2**depth), 'all actual cylinder caps')
            caps.append(cap)
        mean = 1+sum(caps)
        second = 1+sum((2*e+1)*caps[e-1] for e in range(1, height+1))
        require(mean == 2-F(1, 2**height) and second == 6-F(2*height+5, 2**height),
                'full comparison moments')
        stops = []
        for j in range(1, height+1):
            stop = sum(caps[j-1:], F(0))
            require(stop == F(1, 2**(j-1))-F(1, 2**height), 'integer positive-part profile')
            stops.append(str(stop))
        laws.append({'height': height, 'support_size': len(law), 'caps': list(map(str, caps)),
                     'minimum_cap_sum': str(sum(caps)), 'comparison_mean': str(mean),
                     'comparison_second_moment': str(second),
                     'stoploss_at_integer_thresholds_1_to_height': stops})
    return {'branching': 3, 'regression_depth': 3, 'capacity_scale': 81,
            'capacity_profiles_scaled': [list(row) for row in profiles], 'forbidden_assignments': 729,
            'flow_comparisons': comparisons, 'strict_comparisons': strict,
            'binary_split_laws': laws,
            'scope': 'Finite actual-cylinder and flow regressions. General comb extremality and all-height cap-sum optimality are separate ordinary proofs; no optimal convex-profile claim.'}
