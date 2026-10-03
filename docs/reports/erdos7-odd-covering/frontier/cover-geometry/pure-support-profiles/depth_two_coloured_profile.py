"""Actual depth-two pure-plus-star profile on the fixed 43-through-73 schedule.

Load only definitions from the named depth_two_profile.py and
coloured_star_profile.py dependencies; neither producer main nor its finite
control suite is run. All moments are complete; only exact low atoms stop256.
"""
import argparse
from fractions import Fraction as F
import hashlib
from itertools import combinations
import json
from math import comb, factorial
from pathlib import Path
import runpy


def actual_depth_two_controls(require):
    records = []
    for p, residues in ((5, (4, 3, 0, 1)), (7, (6, 5, 0, 1)),
                        (11, (0, 6, 1, 17))):
        pure1, pure2, star1, star2 = residues
        period = p*p
        cylinders = [{x for x in range(period) if x % p == pure1},
                     {pure2},
                     {x for x in range(period) if x % p == star1},
                     {star2}]
        for i, j in combinations(range(4), 2):
            require(not cylinders[i] & cylinders[j],
                    'four literal pure/star depth-two cylinders disjoint')
        require([len(c) for c in cylinders] == [p, 1, p, 1],
                'literal four-cylinder sizes')
        pure = cylinders[0] | cylinders[1]
        both = set().union(*cylinders)
        u = F(1, p)+F(1, p*p)
        require(F(len(pure), period) == u, 'literal pure union Haar mass')
        require(F(len(both), period) == 2*u, 'literal pure-plus-star union Haar mass')
        require(F(period-len(both), period)-F(1, p) > 0,
                'literal active-star anchor zero atom positive')
        records.append({'prime': p, 'period': period,
                        'pure': [[1, pure1], [2, pure2]],
                        'star': [[1, star1], [2, star2]],
                        'pure_union_mass': str(u),
                        'pure_star_union_mass': str(2*u)})
    return records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--arithmetic-library', type=Path, required=True)
    parser.add_argument('--coloured-library', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    lib = runpy.run_path(str(args.arithmetic_library), run_name='profile_arithmetic_library')
    coloured = runpy.run_path(str(args.coloured_library), run_name='coloured_profile_library')
    require, snapshot, stoploss, append, trim = (
        lib[name] for name in ('require', 'snapshot', 'stoploss', 'append', 'trim'))
    require(lib['PRIMES'] == (3,5,7,11,13,17,19,23,29,31,37,41),
            'fixed old twelve-prime support')
    require(lib['LIMIT'] == 256 and lib['ORDERS'] == (0,1,2,4),
            'fixed complete moments and exact low-atom limit')
    h = 1/lib['D0']
    require(h == F(36518862868606981,1816999451688960000),
            'same fixed FC159 source mass')
    controls = actual_depth_two_controls(require)
    primes = lib['PRIMES'][1:]
    retained_u = {p: F(1,p)+F(1,p*p) for p in primes}
    atoms, moments, allowed_mass, patterns, cells = coloured['build_coloured_profile'](
        lib, retained_u, h)
    raw = snapshot(atoms, moments)
    atoms, moments, initial_trim = trim(atoms, moments, h)
    initial = snapshot(atoms, moments)
    stages = []
    for q in (43,47,53,59,61,67,71,73):
        threshold = F(q-1,2)
        before = snapshot(atoms, moments)
        loss = stoploss(atoms, moments, threshold)
        require(loss >= 0, 'complete stop-loss nonnegative')
        charge = loss/threshold
        target = moments[0]-charge
        entry = {'prime':q, 'delta':'1/2', 'cap':'2', 'before':before,
                 'threshold':str(threshold), 'stop_loss':str(loss),
                 'deletion_charge':str(charge), 'candidate_mass':str(target),
                 'positive':target > 0,
                 'mean_gate':str((q-1)*moments[0]-moments[1])}
        if target <= 0:
            entry['decision'] = 'stop before appending first nonpositive stage'
            stages.append(entry)
            break
        atoms, moments = append(atoms, moments, q, F(1), F(2))
        entry['appended'] = snapshot(atoms, moments)
        atoms, moments, certificate = trim(atoms, moments, target)
        entry['trim'] = certificate
        entry['after'] = snapshot(atoms, moments)
        stages.append(entry)
    completed = sum(s['positive'] for s in stages)
    density_cap = 2**completed
    reached73 = len(stages) == 8 and completed == 8
    if reached73:
        b, ell = 10000, 8
        require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25,
                'fixed inherited quartic tail parameter domain')
        for k, coefficient in {1:F(25),2:F(250,3),3:F(100),4:F(40)}.items():
            require(coefficient <= comb(25,k), 'inherited quartic growth domination')
        tau = (F(5625,6144)*F(2*ell*ell+1,2*ell*ell-1)**25
               *F(b,(b-1)**4)*sum(
                   (F(factorial(25),factorial(25-j)*(3*ell)**j) for j in range(26)),F(0)))
        reserve = moments[0]-moments[3]*tau
        require(reserve > 0, 'fixed quartic tail retains positive distorted mass')
        # Short outward rational bounds, checked after the one declared run.
        coarse_mass, coarse_fourth = F(93,100000), F(11310000)
        coarse_reserve = coarse_mass-coarse_fourth*tau
        require(moments[0] > coarse_mass, 'head mass above93/100000')
        require(moments[3] < coarse_fourth, 'head fourth moment below11310000')
        require(coarse_reserve > F(1,1250), 'short fixed-tail reserve above1/1250')
        require(reserve > coarse_reserve, 'exact reserve above short certificate')
        tail = {'B':b, 'ell':ell, 'tau4':str(tau),
                'exact_reserve':str(reserve), 'positive':True,
                'coarse_mass_lower':str(coarse_mass),
                'coarse_M4_upper':str(coarse_fourth),
                'coarse_reserve':str(coarse_reserve),
                'certified_reserve_lower':'1/1250'}
    else:
        tail = None
    data = {
        'scope':'FC159 actual finite N>=max(2,N_plus); same h; actual first two pure/star layers',
        'evidence':'ordinary mathematical premises and exact rational arithmetic; no Lean claim',
        'source_mass':str(h), 'retained_depth':2, 'atom_limit':lib['LIMIT'],
        'orders':lib['ORDERS'], 'old_nonternary_primes':primes,
        'active_stars':{'1':[5], '2':[p for p in primes if p != 5]},
        'canonical_dependency_basenames':['depth_two_profile.py','coloured_star_profile.py'],
        'dependency_hashes':{
            args.arithmetic_library.name:hashlib.sha256(args.arithmetic_library.read_bytes()).hexdigest(),
            args.coloured_library.name:hashlib.sha256(args.coloured_library.read_bytes()).hexdigest()},
        'actual_four_cylinder_controls':controls,
        'retained_pure_masses':{str(p):str(u) for p,u in retained_u.items()},
        'allowed_factor_masses':{str(r):{str(p):str(a) for p,a in allowed_mass[r].items()}
                                 for r in (1,2)},
        'zero_patterns':{str(mask):{'min_product':str(lo),'max_product':str(hi),
                                  'root1_product':str(z1),'root2_product':str(z2)}
                         for mask,(lo,hi,z1,z2) in patterns.items()},
        'pattern_low_atom_cells':cells, 'raw_coloured':raw,
        'initial_trim':initial_trim, 'initial':initial,
        'declared_schedule':[43,47,53,59,61,67,71,73],
        'first_nonpositive_stops':True, 'stages':stages,
        'reached73':reached73, 'final':snapshot(atoms,moments),
        'final_density_cap':str(density_cap),
        'actual_head_Haar_lower':str(moments[0]/density_cap),
        'quartic_tail_conditional_on_734_analytic_premise':tail,
        'checks':require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'checks':data['checks'], 'patterns':len(patterns),
        'low_pattern_cells':cells, 'initial_cutoff':initial_trim['cutoff'],
        'stages':[{'q':s['prime'], 'positive':s['positive'],
                   'candidate_mass':float(F(s['candidate_mass'])),
                   'mean_gate':float(F(s['mean_gate'])),
                   **({'cutoff':s['trim']['cutoff'], 'mean':float(F(s['after']['mean'])),
                       'M2':float(F(s['after']['moments']['2'])),
                       'M4':float(F(s['after']['moments']['4']))} if s['positive'] else {})}
                  for s in stages], 'reached73':reached73,
        'quartic_reserve':float(F(tail['exact_reserve'])) if tail else None,
        'output':str(args.output)}))


if __name__ == '__main__':
    main()
