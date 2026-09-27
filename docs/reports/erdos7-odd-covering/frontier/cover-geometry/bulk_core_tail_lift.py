#!/usr/bin/env python3
"""Exact controls for bounded-density core support and weighted tail completion.

The small-prime control uses its measured survival, not the large-cutoff
estimate. All checks remain active under -O. Importing performs no work.
"""
import argparse
import json
from fractions import Fraction as F
from math import lcm, prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def crt(pairs):
    modulus = prod(m for m, _ in pairs)
    residue = sum(r*(modulus//m)*pow(modulus//m, -1, m) for m,r in pairs) % modulus
    require(all(residue % m == r % m for m,r in pairs), 'literal CRT')
    return modulus, residue


def scalar_controls():
    primes = (5,7,11,13)
    M1 = prod(F(p,p-1) for p in primes)
    M2 = prod(F(p*(p+1),(p-1)**2) for p in primes)
    density_old = F(192,79)
    kappa = F(1,1050)
    good_mass_strip = kappa/(6-kappa)
    good_density_strip = density_old/good_mass_strip
    good_mass_short = (F(1,1000)-F(1,2000))/(2-F(1,2000))
    good_density_short = density_old/good_mass_short
    require(good_mass_strip == F(1,6299) and good_density_strip < 16000,
            'strip support has a height-independent Haar density cap')
    require(good_mass_short == F(1,3999) and good_density_short < 16000,
            'short-depth support has a height-independent Haar density cap')
    require(M2 < 5 and 16000*M2 < 80000 and M1 < M2, 'head harmonic moments')
    require(108*513**2 < 3**16 and 324 < 3**6, 'exact cutoff constants')
    return dict(core_primes=primes, all_height_J1_upper=M1, all_height_J2_upper=M2,
                original_survivor_density_lower=F(79,192), old_Haar_density_cap=density_old,
                strip_gap=kappa, strip_good_mass_lower=good_mass_strip,
                strip_good_Haar_density_upper=good_density_strip, strip_pointwise_margin=F(1,4200),
                short_depth_good_mass_lower=good_mass_short,
                short_depth_good_Haar_density_upper=good_density_short,
                short_depth_pointwise_margin=F(1,2000), shared_Haar_density_cap=16000,
                shared_integer_moment_cap=80000, height_independent_prime_cutoff='3^256 * 80000^3',
                short_depth_scope='The whole original family has ternary height at most five',
                strip_scope='At least one of h5<=3,h7<=2,h11<=1,h13<=1; any finite ternary height')


def actual_control():
    """One original family with a dead core fibre and a surviving global law.

    The core valuation partition is exact: every original core residue is 0
    modulo a power of 5, and each kernel depends only on those memberships.
    """
    p = 7
    height, Q, H = p-1, 5**(p-1), 2
    head_divisors = [5**j for j in range(p)]
    labels = []
    for j,a in enumerate(head_divisors):
        for e,leaf in ((0,j),(2,(j+1)%p)):
            pairs = [(a,0),(p,leaf)] + ([(3**e,0)] if e else [])
            modulus, residue = crt(pairs)
            labels.append(dict(modulus=modulus,residue=residue,e=e,a=a))
    require(len({v['modulus'] for v in labels}) == 2*p and
            all(v['modulus'] > 1 and v['modulus'] % 2 for v in labels),
            'distinct original nonunit odd numerical moduli')
    cells = []
    for valuation in range(p):
        count = 1 if valuation == height else 4*5**(height-valuation-1)
        representative = 0 if valuation == height else 5**valuation
        mass = F(count,Q)
        forbidden = set(range(valuation+1))
        alpha = F(len(forbidden),p)
        row = []
        for leaf in range(p):
            if alpha <= F(1,2):
                density = F(0) if leaf in forbidden else 1/(1-alpha)
            else:
                density = (2*alpha-1)/alpha if leaf in forbidden else F(2)
            require(0 <= density <= 2, 'capped full-history density')
            row.append(density/p)
        require(sum(row) == 1, 'every conditional row is normalized, including dead fibres')
        cells.append(dict(valuation=valuation,cardinality=count,representative=representative,
                          core_mass=mass,alpha=alpha,kernel=row,good_leaves=tuple(range(valuation+1,p))))
    require(sum(c['cardinality'] for c in cells) == Q, 'exact core partition')
    survival = sum(c['core_mass']*sum(c['kernel'][y] for y in c['good_leaves']) for c in cells)
    require(0 < survival < 1, 'nontrivial measured global survival')
    for cell in cells:
        cell['joint_conditioned'] = [cell['core_mass']*v/survival if y in cell['good_leaves'] else F()
                                     for y,v in enumerate(cell['kernel'])]
        cell['conditioned_core_mass'] = sum(cell['joint_conditioned'])
    require(sum(c['conditioned_core_mass'] for c in cells) == 1, 'one normalized global law')
    require(cells[-1]['representative'] == 0 and cells[-1]['core_mass'] > 0 and
            cells[-1]['conditioned_core_mass'] == 0, 'a fully deleted core fibre is allowed')
    tv = sum(abs(c['conditioned_core_mass']-c['core_mass']) for c in cells)/2
    require(0 < tv <= 1-survival, 'core marginal changes with controlled total variation')
    J1 = sum((F(1,a) for a in head_divisors),F())
    J2 = sum((F(1,lcm(a,b)) for a in head_divisors for b in head_divisors),F())
    second = sum(c['core_mass']*c['alpha']**2 for c in cells)
    require(second == J2/p**2, 'exact weighted head-pair second moment')
    require(1-survival <= second, 'global first-moment failure is paid by one second moment')
    query_count = 0
    for a in head_divisors:
        for leaf in range(p):
            before = sum(c['core_mass']*c['kernel'][leaf] for c in cells if c['representative']%a == 0)
            after = sum(c['joint_conditioned'][leaf] for c in cells if c['representative']%a == 0)
            require(before <= F(2,a*p) and after <= F(2,a*p)/survival,
                    'joint core-cylinder and outside-cylinder bounds')
            query_count += 1
    completion = F()
    literal_checks = 0
    for cell in cells:
        x = cell['representative']
        for leaf,mass in enumerate(cell['joint_conditioned']):
            old_hits = sum(x%v['a'] == v['residue']%v['a'] and leaf == v['residue']%p
                           for v in labels if v['e'] == 0)
            require(mass == 0 or old_hits == 0, 'support avoids every original 3-free class')
            cofactor_hits = sum(x%v['a'] == v['residue']%v['a'] and leaf == v['residue']%p
                                for v in labels if v['e'] == 2)
            literal_hits = 0
            for ternary in range(3**H):
                _,word = crt([(Q,x),(p,leaf),(3**H,ternary)])
                literal_hits += sum(word%v['modulus'] == v['residue'] for v in labels if v['e'] == 2)
                literal_checks += 1
            require(F(3*literal_hits,3**H) == F(cofactor_hits,3),
                    'literal original phases give the weighted cofactor load')
            completion += mass*F(cofactor_hits,3)
    finite_cap = F(2,3*p)*J1/survival
    require(0 < completion <= finite_cap, 'late load on the same global law')
    return dict(scope='Exact small-prime control, using measured survival rather than the asymptotic cutoff',
                core_period=Q,outside_prime=p,core_height=height,ternary_height=H,
                original_labels=labels,old_core_classes=[],core_Haar_density_cap=1,
                early_original_depths=[0],late_original_depths=[2],core_completion_load=0,
                J1=J1,J2=J2,second_moment=second,global_survival=survival,
                core_total_variation=tv,core_cells=cells,
                killed_core_point=0,point_mass_preservation_impossible=True,
                actual_late_completion=completion,finite_joint_cap_completion=finite_cap,
                joint_query_count=query_count,literal_original_CRT_checks=literal_checks)


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=dict(parameters=scalar_controls(),actual_original_control=actual_control())
    rendered=json.dumps(encode(result),indent=2)+'\n'
    if args.output:
        args.output.write_text(rendered)
        actual=result['actual_original_control']
        print(json.dumps(encode({k:v for k,v in actual.items() if k not in ('original_labels','core_cells')}),indent=2))
    else:
        print(rendered,end='')


if __name__ == '__main__':
    main()
