#!/usr/bin/env python3
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from math import gcd
import argparse
import json


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def crt(a, q, b, m):
    return (a + q * (((b-a) * pow(q, -1, m)) % m)) % (q*m)


def fixtures(p, height, old_period):
    ds = [d for d in range(1, old_period+1) if old_period % d == 0]
    nonunit = ds[1:]
    old_forbidden = [(d, 0) for d in nonunit]
    survivors = [x for x in range(old_period)
                 if all(x % d != a for d,a in old_forbidden)]
    require(survivors == [x for x in range(old_period) if gcd(x, old_period) == 1],
            'uniform complete actual357 survivor set')
    origin, changed = 1, 1+old_period//3
    require(origin in survivors and changed in survivors, 'both old rows are actual survivors')
    modulus = p**height
    pure_atoms = modulus-1
    delta = F(7,p-2)
    count = delta*pure_atoms
    require(count.denominator == 1, 'exact threshold belongs to actual pure-base grid')
    remaining = count.numerator
    digits = []
    for e in range(1,height+1):
        digit, remaining = divmod(remaining,p**(height-e))
        digits.append(digit)
    require(remaining == 0 and digits[0] == 7, 'exact base-p decomposition')
    require(max(digits) <= len(nonunit), 'distinct old-label budget at every current depth')
    # Rows are (old modulus, old residue, current exponent, current prefix).
    mixed = []
    first_ds = [3,5,7,9,15,21,35]
    require(all(old_period//3 % d == 0 for d in first_ds), 'first-depth labels survive the old-row change')
    for root,d in enumerate(first_ds,1):
        mixed.append((d,origin%d,1,root))
    prefix = 8
    for e in range(2,height+1):
        for j,d in enumerate(nonunit[:digits[e-1]]):
            mixed.append((d,origin%d,e,prefix+j*p**(e-1)))
        prefix += digits[e-1]*p**(e-1)
    mixed.append((old_period,changed,1,9))
    require(len({(d,e) for d,a,e,r in mixed}) == len(mixed), 'one actual class per original mixed modulus')
    for i,(_,_,e,r) in enumerate(mixed):
        require(1 <= r % p <= 9, 'all mixed masks avoid the clean root and pure leaf')
        for _,_,f,s in mixed[:i]:
            require((r-s) % p**min(e,f) != 0, 'current forbidden cylinders are globally disjoint')
    current_count = sum(p**(height-e) for d,a,e,r in mixed[:-1])
    require(current_count == count, 'literal disjoint-prefix atom count equals threshold')
    forbidden = old_forbidden + [(modulus,0)] + [
        (d*p**e, crt(a,d,r,p**e)) for d,a,e,r in mixed]
    for (d,a,e,r),(literal_modulus,literal_residue) in zip(mixed,forbidden[len(old_forbidden)+1:]):
        require(literal_modulus == d*p**e and 0 <= literal_residue < literal_modulus
                and literal_residue%d == a and literal_residue%p**e == r,
                'literal original mixed CRT classes')
    require(len({d for d,a in forbidden}) == len(forbidden), 'distinct complete original forbidden moduli')
    tests = []
    old_test_blocks = []
    for e in range(height+1):
        old_layout = [(d, origin if e == 0 and d == old_period else
                        3*e if e > 0 and d == old_period else 0) for d in ds]
        old_test_blocks.append(old_layout)
        for d,a in old_layout:
            tests.append((d*p**e, a if e == 0 else crt(a,d,p-1,p**e)))
    require(len({tuple(layout) for layout in old_test_blocks}) == height+1,
            'all old test layouts are distinct rather than identified')
    require({d for d,a in tests} == {d*p**e for d in ds for e in range(height+1)},
            'complete original test exponent rectangle')
    require(len(tests) == len(ds)*(height+1), 'every original test label retained')
    for e,layout in enumerate(old_test_blocks):
        for (d,a),(literal_modulus,literal_residue) in zip(layout,tests[e*len(ds):(e+1)*len(ds)]):
            require(literal_modulus == d*p**e and literal_residue%d == a
                    and (e == 0 or literal_residue%p**e == p-1),
                    'literal original complete-test CRT classes')
    clip = 1/(1-delta)
    generic_pure_lower = F(p-2,p-1)
    cap = clip/generic_pure_lower
    wfirst = sum(p**(height-e) for e in range(1,height+1))
    wsecond = sum((2*e-1)*p**(height-e) for e in range(1,height+1))
    hist = Counter()
    charge = killed_excess = covariance = physical = killed = zero_excess = F(0)
    rows = {}
    for x in survivors:
        active_count = sum(p**(height-e) for d,a,e,r in mixed if x%d == a)
        alpha = F(active_count,pure_atoms)
        require(alpha < 1, 'genuine mixed union leaves a current good point in every row')
        a = 1/(1-min(alpha,delta))
        beta = max(alpha-delta,F(0))/(1-delta)
        bad_density = beta/alpha if alpha else F(0)
        require((1-alpha)*a+alpha*bad_density == 1, 'actual BB kernel normalization')
        require(0 <= bad_density <= 1 and 1 <= a <= clip, 'actual clipped density bounds')
        loads = [sum(x%d == residue for d,residue in layout) for layout in old_test_blocks]
        require(loads[0] == 1+int(x == origin), 'nonconstant zero-current block')
        require(loads[1:] == [1]*height, 'all independent positive blocks have their exact original loads')
        row_covariance = F(0)
        envelope = a/generic_pure_lower
        for e in range(height+1):
            for f in range(height+1):
                if e == 0 and f == 0:
                    continue
                row_covariance += F(1,p**max(e,f))*(cap-envelope)*(loads[e]*loads[f]-1)
        # Every bad cylinder has first root <=9, whereas every positive test prefix
        # has first root p-1. Thus every bad point has exactly load A0.
        row_excess = beta*(loads[0]**2-1)
        row_square = loads[0]**2 + F(a,pure_atoms)*(2*loads[0]*wfirst+wsecond)
        row_killed = row_square-beta*loads[0]**2
        hist[active_count] += 1
        factor = F(1,len(survivors))
        charge += factor*beta
        killed_excess += factor*row_excess
        covariance += factor*row_covariance
        physical += factor*row_square
        killed += factor*row_killed
        zero_excess += factor*(loads[0]-1)
        if x in (origin,changed):
            rows[str(x)] = dict(alpha=str(alpha),beta=str(beta),pure_bad_atom_count=active_count,
                                old_test_block_loads=loads,SH26_cap_deficit=str(cap-envelope))
    require(F(rows[str(origin)]['alpha']) == delta, 'origin has exact clipping-threshold union fraction')
    require(F(rows[str(changed)]['alpha']) > delta, 'changed old row has positive actual assigned charge')
    require(charge > 0 and zero_excess == F(1,len(survivors)) > 0, 'positive bad mass and nonconstant zero layer')
    require(F(sum(x%3 == 1 for x in survivors),len(survivors)) == F(1,2),
            'zero-layer mod3 edit strictly improves the displayed nonmaximizing test')
    require(covariance == killed_excess == 0, 'both complete SH26 covariance and actual killed excess vanish')
    require(physical-killed == charge, 'exact whole complete-test square loss remains the unit floor')
    actual_pure_mass = F(pure_atoms,modulus)
    true_cap = clip/actual_pure_mass
    require(true_cap < cap, 'actual pure-density refinement remains strictly available')
    return dict(prime=p,current_height=height,old_period=old_period,full_original_period=old_period*modulus,
                old_survivor_count=len(survivors),pure_base_atom_count=pure_atoms,
                actual_pure_Haar_mass=str(actual_pure_mass),delta=str(delta),
                threshold_base_p_digits=digits,original_forbidden_classes=forbidden,
                original_test_classes=tests,forbidden_count=len(forbidden),test_count=len(tests),
                critical_old_rows=rows,actual_bad_count_histogram=[dict(count=n,old_rows=k) for n,k in sorted(hist.items())],
                assigned_bad_mass=str(charge),zero_block_mean_excess=str(zero_excess),
                complete_SH26_cap_covariance=str(covariance),actual_killed_excess=str(killed_excess),
                physical_complete_test_square=str(physical),killed_complete_test_square=str(killed),
                SH26_generic_cap=str(cap),actual_pure_density_cap=str(true_cap),
                separate_actual_pure_density_cap_saving=str(cap-true_cap),
                zero_layer_mod3_edit_strict_square_gain_lower='3/2',
                current_maximizing_test_claim=False)


def unique(pairs):
    out = {}
    for key,value in pairs:
        require(key not in out,'duplicate JSON key')
        out[key] = value
    return out


parser = argparse.ArgumentParser(description="Exact full-height SH26 joint-zero counterexamples with all original labels.")
parser.add_argument('certificate',nargs='?',type=Path,default=Path(__file__).with_name('current_joint_zero_certificate.json'))
parser.add_argument('--write',action='store_true')
args = parser.parse_args()
data = dict(schema='full-height-SH26-joint-zero-v1',
            scope='Actual uniform full357 law and genuine BB kernels at T8; all original tests through actual current heights. SH26 generic-cap covariance and killed excess both vanish. Actual pure-density saving remains positive; no maximizing-current-test claim.',
            fixtures=[fixtures(17,4,945),fixtures(19,8,2835)])
output = args.certificate
if args.write:
    output.write_text(json.dumps(data,indent=2)+'\n')
else:
    saved = json.loads(output.read_text(),object_pairs_hook=unique)
    require(json.dumps(saved,sort_keys=True) == json.dumps(data,sort_keys=True),'certificate mismatch')
print('PASS: full original 17/19 heights, distinct independent old test blocks, actual uniform357 source, genuine BB kernels, positive charge and zero-layer excess, both joint savings zero')
