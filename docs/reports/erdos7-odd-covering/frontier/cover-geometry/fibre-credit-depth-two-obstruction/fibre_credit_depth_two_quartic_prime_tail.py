#!/usr/bin/env python3
"""Exact controls for a same-source higher-moment prime tail.

The inherited head geometry/density and Rosser--Schoenfeld estimates are
ordinary mathematical source premises, not proved by this consumer.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, factorial, lcm, prod
from pathlib import Path
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def moment4(p):
    # Geometric-series derivative formula for the all-height Haar fourth moment.
    return F(p**4+11*p**3+11*p**2+p, (p-1)**4)


def growth_coefficients(k):
    if k == 4:
        return (F(1), F(15), F(50), F(60), F(24))
    raise ValueError('This exact consumer instantiates only order 4.')


def evaluate(primes, mass, density, k, delta, r, B, ell, lower):
    need(B >= 286 and ell >= 4 and 3**ell <= B and k*ell >= r,
         'prime-product premise and decreasing tail-integrand hypotheses')
    coeff = growth_coefficients(k)
    slacks = [F(comb(r,j)) - (F(1) if j == 0 else
               (coeff[j]/(1-delta) if j < len(coeff) else F(0)))
              for j in range(r+1)]
    need(all(x >= 0 for x in slacks), 'full coefficientwise growth envelope')
    local = [sum((coeff[j]*F(1,p-1)**j for j in range(k+1)),F(0))
             for p in primes]
    if k == 4:
        need(local == [moment4(p) for p in primes],
             'reciprocal-gap polynomial equals independently expressed Haar fourth moment')
    K = density*prod(local,start=F(1))
    C = F((k-1)**(k-1),k**k)/(delta**(k-1)*(1-delta))
    c = F(2*ell**2+1,2*ell**2-1)
    polynomial = sum((F(factorial(r),factorial(r-j)*((k-1)*ell)**j)
                      for j in range(r+1)),F(0))
    tau = C/F(k-1)*c**r*F(B,(B-1)**k)*polynomial
    loss = K*tau
    remaining = mass-loss
    need(remaining > lower > 0, 'strict same-source remaining absolute mass')
    return dict(head_primes=primes,head_mass_lower=str(mass),
                head_joint_Haar_density_upper=str(density),moment_order=k,
                delta=str(delta),growth_degree=r,cutoff_exclusive=B,ell=ell,
                local_all_height_Haar_moments=list(map(str,local)),
                absolute_moment_potential=str(K),scalar_loss_constant=str(C),
                coefficient_slacks=list(map(str,slacks)),prime_product_constant=str(c),
                integral_polynomial=str(polynomial),tail_coefficient=str(tau),
                tail_debit=str(loss),tail_debit_decimal=float(loss),
                remaining_absolute_mass_lower=str(remaining),
                remaining_decimal=float(remaining),strict_simple_lower=str(lower),
                Haar_lower_prefactor=str(lower/density),
                Haar_tail_factor_per_actual_prime=str(1-delta))


def toy_stage(delta):
    old_period, new_period = 5, 45
    old_mass = F(3,4)
    point_mass = old_mass/old_period
    originals = ((3,0),(9,3),(15,7),(45,14))
    # Every complete old query is 1 + 1_{a mod 5}; no query is omitted.
    Kold = old_mass*F(16+4,5)
    nu, alpha = {}, {}
    for x in range(old_period):
        fibre = tuple(z for z in range(new_period) if z%old_period == x)
        bad = {z for z in fibre if any(z%d == a for d,a in originals)}
        beta = F(len(bad),9)
        load = F(0)
        for d,a in originals:
            old_cofactor,current_factor = d,1
            while old_cofactor%3 == 0:
                old_cofactor //= 3
                current_factor *= 3
            if x%old_cofactor == a%old_cofactor:
                load += F(1,current_factor)
        alpha[x] = load
        need(beta <= load, 'actual union bounded by actual partial-query load')
        for z in fibre:
            nu[z] = F(0) if z in bad else point_mass/9/(1-min(beta,delta))
    new_mass = sum(nu.values(),F(0))
    alpha_moment = sum((point_mass*alpha[x]**4 for x in range(old_period)),F(0))
    theta = F(1,3)+F(1,9)
    A4H = sum((F((e+1)**4-e**4,3**e) for e in (1,2)),F(0))
    Knew = Kold*(1+A4H/(1-delta))
    loss_cap = F(27,256)*Kold*theta**4/(delta**3*(1-delta))
    need(alpha_moment <= Kold*theta**4 and old_mass-new_mass <= loss_cap,
         'same actual measure satisfies the complete fourth-moment loss chain')
    support = tuple(z for z in range(new_period) if nu[z])
    denominator = lcm(*(v.denominator for v in nu.values()))
    weights = tuple(int(nu[z]*denominator) for z in support)
    moduli = (1,3,5,9,15,45)
    columns = tuple(tuple(tuple(int(z%d == a) for z in support)
                          for a in range(d)) for d in moduli)
    maximum,count = -1,0
    for chosen in product(*columns):
        numerator = sum(w*sum(bits)**4 for w,bits in zip(weights,zip(*chosen)))
        maximum = max(maximum,numerator)
        count += 1
    actual_max = F(maximum,denominator)
    need(count == 91125 and actual_max <= Knew,
         'all complete actual 45-query fourth moments satisfy propagated bound')
    return dict(delta=str(delta),originals=originals,old_mass=str(old_mass),
                new_mass=str(new_mass),actual_loss=str(old_mass-new_mass),
                actual_union_load_fourth_moment=str(alpha_moment),
                absolute_old_fourth_moment=str(Kold),absolute_loss_upper=str(loss_cap),
                propagated_fourth_moment_upper=str(Knew),complete_queries_checked=count,
                actual_maximum_fourth_moment=str(actual_max))


def calculate(head_certificate=None):
    if head_certificate is None:
        head_certificate = (Path(__file__).resolve().parent.parent /
                            "seven-block-certificate/seven_block_certificate.json")
    raw = head_certificate.read_bytes()
    head_sha = sha256(raw).hexdigest()
    need(head_sha == 'b6c47c2e710cdb27e599b92ccfe7d1b5c4e55b4b4082ad8058d196c1e964b9b2',
         'inherited seven-prime certificate identity')
    head = json.loads(raw)
    primes7 = (3,5,7,11,13,17,19)
    rows = [row for row in head['core_results'] if row['children_lower_bounds'] == list(primes7[1:])]
    need(len(rows) == 1, 'unique inherited head certificate row')
    row = rows[0]
    need(row['thresholds'] == [2,4,4,8,8], 'inherited seven-prime source thresholds')
    m7,D7 = F(row['mass_lower_bound']),F(row['global_density_cap'])
    need(m7 == F(7235955529,450000000000) and D7 == F(27,2),
         'same inherited measure mass and joint density')
    caps = tuple(map(F,row['coordinate_marginal_caps']))
    need(caps == (F(1),F(1),F(3,2),F(5,3),F(3,2),F(2),F(9,5)) and prod(caps) == D7,
         'source kernel density factors match inherited joint-density construction')

    # Exhaustive arbitrary bad subsets on a height-two ternary coordinate.
    kernel_rows,prefix_caps,scalar_controls = 0,0,0
    for mask in range(512):
        beta = F(mask.bit_count(),9)
        for delta in (F(1,4),F(2,5)):
            R = tuple(F(0) if (mask>>y)&1 else F(1,9)/(1-min(beta,delta)) for y in range(9))
            mass = sum(R,F(0))
            need(mass == 1-max(beta-delta,F(0))/(1-delta) and 0 <= mass <= 1,
                 'actual clipped row is a subprobability with exact loss')
            need(1-mass <= F(27,256)*beta**4/(delta**3*(1-delta)),
                 'quartic actual-union clipping bound')
            for e in range(3):
                for a in range(3**e):
                    value = sum((R[y] for y in range(9) if y%3**e == a),F(0))
                    need(value <= (F(1) if e == 0 else F(1,3**e)/(1-delta)),
                         'every true current-prime prefix has required mass cap')
                    prefix_caps += 1
            kernel_rows += 1
    for delta in (F(1,4),F(2,5)):
        for a in (F(0),delta/2,delta,F(4,3)*delta,2*delta,4*delta):
            lhs = 27*a**4-256*delta**3*(a-delta)
            rhs = (3*a-4*delta)**2*(3*a*a+8*a*delta+16*delta*delta)
            need(lhs == rhs, 'exact quartic nonnegative remainder identity')
            scalar_controls += 1

    exponent_checks = 0
    for p in (3,5,29,41):
        for H in range(1,5):
            raw_sum = sum((F(1,p**max(exps)) for exps in product(range(H+1),repeat=4)),F(0))
            grouped = 1+sum((F((j+1)**4-j**4,p**j) for j in range(1,H+1)),F(0))
            need(raw_sum == grouped < moment4(p), 'all exponent quadruples grouped by their true maximum')
            exponent_checks += 1

    seven = evaluate(primes7,m7,D7,4,F(1,4),20,1500,6,F(3,500))
    eight = evaluate(primes7+(23,),F(1,1002375),F(1),4,F(2,5),25,10000,8,F(1,20000000))
    need(F(seven['absolute_moment_potential']) == F(82461631627375,127401984), 'seven-prime quartic initialization')
    need(F(eight['absolute_moment_potential']) == F(16379878645983125,190768545792), 'eight-prime quartic initialization')
    toys = [toy_stage(delta) for delta in (F(1,4),F(2,5))]
    out = dict(scope='Same-source complete-query higher-moment tail; all original heights unrestricted. '
                     'Ordinary proof with exact controls, not new Lean verification or a complete odd-cover resolution.',
               source_certificate_sha256=head_sha,inherited_head_geometry_reexecuted=False,
               analytic_prime_product_theorem_reproved=False,
               eight_prime_density=dict(attribution='Michael Schroeder, Nine Prime Divisors in Odd Distinct Covering Systems, '
                                                   'edition1.0.1, cor:uncovered-density',
                                        archive_sha256='9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c',
                                        attributed_ordinary_source_premise=True,
                                        whole_arbitrary_height_theorem_locally_kernel_replayed=False),
               kernel_rows_checked=kernel_rows,prefix_caps_checked=prefix_caps,
               scalar_identity_controls=scalar_controls,quadruple_exponent_checks=exponent_checks,
               actual_CRT_stages=toys,quartic_seven=seven,quartic_eight=eight,
               exact_checks_passed=True)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head-certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(args.head_certificate)))
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix(".json").read_text()) == result,
             "retained result agrees with quartic tail and source arithmetic")
        print(rendered, end="")
    else:
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
