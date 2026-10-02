"""Initial depth-two coloured profile with the actual 2 mod55 group retained.

Explicit libraries are loaded as definitions only. No producer main, old
finite control, or prime continuation is run. Complete moments retain all
run heights; low atoms are exact through256.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
from math import prod
from pathlib import Path
import runpy


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--arithmetic-library', type=Path, required=True)
    parser.add_argument('--coloured-library', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    lib = runpy.run_path(str(args.arithmetic_library), run_name='profile_arithmetic_library')
    coloured = runpy.run_path(str(args.coloured_library), run_name='coloured_profile_library')
    require, factor_moments, snapshot, trim = (
        lib[name] for name in ('require','factor_moments','snapshot','trim'))
    primes, limit, orders = lib['PRIMES'][1:],lib['LIMIT'],lib['ORDERS']
    require(primes == (5,7,11,13,17,19,23,29,31,37,41), 'fixed old nonternary support')
    require(limit == 256 and orders == (0,1,2,4), 'fixed exact inventory and complete moments')
    h = 1/lib['D0']
    require(h == F(36518862868606981,1816999451688960000), 'same source and h')
    base_atoms, base_moments, allowed, base_patterns, base_cells = coloured['build_coloured_profile'](
        lib, {p:F(1,p)+F(1,p*p) for p in primes}, h)
    zero = {r:{p:allowed[r][p]-F(1,p) for p in primes} for r in (1,2)}
    delta = F(1,55)
    pair = (5,11)
    pair_mask = sum(1 << primes.index(p) for p in pair)
    for r in (1,2):
        require(F(1,11) <= zero[r][11], 'conditional q zero coefficient nonnegative')
        require(delta < zero[r][5]*zero[r][11], 'corrected pair zero coefficient positive')
    positive_moments = {
        p:[m-F(p-1,p) for m in factor_moments(p,F(1),F(1))] for p in primes}
    ternary_long = [m-F(2,3) for m in factor_moments(3,F(1),F(1))]
    corrected_patterns, debit_patterns = {}, {}
    debit_moments = [F(0) for _ in orders]
    affected = 0
    for mask,(lo,hi,z1,z2) in base_patterns.items():
        new_roots = {1:z1,2:z2}
        if mask & pair_mask == pair_mask:
            affected += 1
            for r in (1,2):
                other_zero_product = prod(zero[r][p] for i,p in enumerate(primes)
                                          if p not in pair and mask & (1 << i))
                new_roots[r] -= delta*other_zero_product
        nl,nh = min(new_roots.values()),max(new_roots.values())
        require(0 < nl <= nh, 'corrected common-root pattern positive')
        require(nl <= lo and nh <= hi, 'both min and max decrease before scalar pushforward')
        dl,dh = lo-nl,hi-nh
        corrected_patterns[mask] = (nl,nh,new_roots[1],new_roots[2])
        debit_patterns[mask] = (dl,dh)
        if mask & pair_mask != pair_mask:
            require(dl == dh == 0, 'only joint pair-zero patterns change')
        for ki in range(len(orders)):
            positive = prod(positive_moments[p][ki] for i,p in enumerate(primes)
                            if not mask & (1 << i))
            debit_moments[ki] += (dl/3+dh*ternary_long[ki])*positive
    require(len(corrected_patterns) == 2048 and affected == 512,
            'all2048 patterns and exactly512 pair-zero corrections')
    expected_debit_mass = delta/3*sum(
        (prod(allowed[r][p] for p in primes if p not in pair) for r in (1,2)),F(0))
    require(debit_moments[0] == expected_debit_mass, 'exact actual rectangle reference mass debit')

    # Only pair-zero cells can contribute to the debit; preserve their full
    # zero masks until taking the two corrected root products' min and max.
    cells = {(pair_mask,1):F(1)}
    for i,p in enumerate(primes):
        if p in pair:
            continue
        nxt = defaultdict(F)
        for (mask,z),weight in cells.items():
            nxt[(mask | (1 << i),z)] += weight
            for v in range(2,limit//z+1):
                nxt[(mask,z*v)] += weight*F(p-1,p**v)
        cells = dict(nxt)
    debit_atoms = [F(0) for _ in range(limit+1)]
    for (mask,z),weight in cells.items():
        dl,dh = debit_patterns[mask]
        debit_atoms[z] += weight*dl/3
        for v in range(2,limit//z+1):
            debit_atoms[z*v] += weight*dh*F(2,3**v)
    atoms = [a-d for a,d in zip(base_atoms,debit_atoms)]
    moments = [m-d for m,d in zip(base_moments,debit_moments)]
    require(all(0 <= d <= a for d,a in zip(debit_atoms,base_atoms)),
            'scalar low-atom debit is a positive submeasure')
    require(all(d > 0 for d in debit_moments), 'complete moment debits positive')
    require(moments[0] >= h, 'same actual source mass fits corrected positive profile')
    base_raw = snapshot(base_atoms,base_moments)
    debit = snapshot(debit_atoms,debit_moments)
    raw = snapshot(atoms,moments)
    atoms,moments,initial_trim = trim(atoms,moments,h)
    initial = snapshot(atoms,moments)
    data = {
        'scope':'same FC159 eta0/h; actual N>=max(2,N_plus); retained n2; original2mod55; initialization only',
        'evidence':'ordinary mathematical comparison and exact arithmetic; no Lean claim',
        'source_mass':str(h), 'retained_depth':2, 'atom_limit':limit, 'orders':orders,
        'old_nonternary_primes':primes,
        'actual_group':{'modulus':55,'residue':2,'pair':pair,'root_pair_zero_debit':str(delta)},
        'canonical_dependency_basenames':['depth_two_profile.py','coloured_star_profile.py'],
        'dependency_hashes':{
            args.arithmetic_library.name:hashlib.sha256(args.arithmetic_library.read_bytes()).hexdigest(),
            args.coloured_library.name:hashlib.sha256(args.coloured_library.read_bytes()).hexdigest()},
        'allowed_factor_masses':{str(r):{str(p):str(a) for p,a in allowed[r].items()} for r in (1,2)},
        'zero_patterns':{str(mask):{'min_product':str(lo),'max_product':str(hi),
                                  'root1_product':str(z1),'root2_product':str(z2),
                                  'min_debit':str(debit_patterns[mask][0]),
                                  'max_debit':str(debit_patterns[mask][1])}
                         for mask,(lo,hi,z1,z2) in corrected_patterns.items()},
        'affected_zero_patterns':affected,'base_pattern_low_atom_cells':base_cells,
        'debit_pattern_low_atom_cells':len(cells),
        'actual_reference_mass_debit':str(expected_debit_mass),
        'raw_coloured_before_group':base_raw, 'group_debit':debit, 'raw_grouped':raw,
        'initial_trim':initial_trim,'initial':initial,
        'prime_updates_executed':0,'checks':require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'checks':data['checks'],'patterns':len(corrected_patterns),
        'affected_patterns':affected,'debit_low_cells':len(cells),
        'raw_mass':float(F(raw['moments']['0'])),'raw_mean':float(F(raw['mean'])),
        'initial_cutoff':initial_trim['cutoff'],
        'initial_moments':{k:float(F(v)) for k,v in initial['moments'].items()},
        'initial_mean':float(F(initial['mean'])), 'prime_updates_executed':0,
        'output':str(args.output)}))


if __name__ == '__main__':
    main()
