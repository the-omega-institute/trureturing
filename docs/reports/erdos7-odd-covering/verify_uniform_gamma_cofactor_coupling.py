#!/usr/bin/env python3
"""Exact uniform Gamma35 and Gamma357 bounds from shared actual parameters.

Python3.9+ standard library only. The accompanying proof gives the layout
inequality and the continuous linear-fractional vertex reduction. This checks
all72 old branches,103680 shared branches and12960 signed layout-vertices,
plus missing-class cases,
with no solver.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
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
            'signed_two_level_three_prime_parameters':signed_two_level_three_prime_bound()}


def main():
    data=json.loads(Path(__file__).with_name('uniform_gamma_cofactor_certificate.json').read_text())
    expected=compute_certificate()
    require(data==expected,'fixed certificate differs from exact recomputation')
    print('Verified all72 continuous-envelope branches: uniform Gamma35 <=55/4.')
    print('Positive denominators and absent-modulus-3 bound215/24 verified; '
          'the old57/4 extremal budget now has coupled bound55/4.')
    print('Verified103680 shared-parameter branches: uniform Gamma357<=937/24; '
          'all denominator and missing-pure-class checks passed.')
    print('Verified12960 signed two-level layout-vertices: uniform Gamma357<=3849/106; '
          'both missing-pure-class bounds are smaller on the same law.')


if __name__=='__main__':
    main()
