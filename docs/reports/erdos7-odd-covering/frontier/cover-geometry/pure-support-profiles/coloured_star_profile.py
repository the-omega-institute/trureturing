"""One actual first-pure/first-star coloured profile and fixed half schedule.

The explicit arithmetic library is loaded as definitions only. Complete
moments include every auxiliary height; low atoms stop at declared load256.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from math import comb, factorial, prod
from pathlib import Path
import runpy


def finite_colour_controls(require):
    # Exhaust all complete first-digit layouts on the literal 3*5 carrier.
    allowed = [x for x in range(15) if x % 3 != 0 and x % 5 != 4
               and not (x % 3 == 1 and x % 5 == 0)]
    finite_profile = {1:F(2,15), 2:F(4,15), 4:F(1,15)}
    require(F(len(allowed),15) == sum(finite_profile.values(),F(0)), 'finite coloured mass')
    layout_count = 0
    for a3,a5,a15 in product(range(3),range(5),range(15)):
        loads = [1+(x % 3 == a3)+(x % 5 == a5)+(x == a15) for x in allowed]
        for t in range(5):
            actual = sum(max(z-t,0) for z in loads)/F(15)
            bound = sum((max(z-t,0)*w for z,w in finite_profile.items()),F(0))
            require(actual <= bound, 'literal joint-colour complete-layout hinge')
        layout_count += 1
    sharp_loads = Counter(1+(x % 3 == 2)+(x % 5 == 1)+(x == 11) for x in allowed)
    require({z:F(n,15) for z,n in sharp_loads.items()} == finite_profile,
            'one explicit finite layout attains the entire finite coloured profile')
    require(layout_count == 225, 'declared new complete-layout control count')
    return layout_count, finite_profile


def build_coloured_profile(lib, retained_u, source_mass):
    """Return complete moments and low atoms, preserving the joint zero pattern."""
    require, factor_moments = lib['require'], lib['factor_moments']
    primes, limit, orders = lib['PRIMES'][1:], lib['LIMIT'], lib['ORDERS']
    h = source_mass
    # The caller supplies its declared finite pure/star mass at each coordinate.
    allowed_mass = {r:{} for r in (1,2)}
    zero_atom = {r:{} for r in (1,2)}
    positive_moments = {}
    for p in primes:
        for r in (1,2):
            active = (r == 1 and p == 5) or (r == 2 and p != 5)
            allowed_mass[r][p] = 1-(1+int(active))*retained_u[p]
            zero_atom[r][p] = allowed_mass[r][p]-F(1,p)
            require(zero_atom[r][p] > 0, 'finite actual pure/star anchor domain')
        positive_moments[p] = [m-F(p-1,p) for m in factor_moments(p,F(1),F(1))]
        require(all(m > 0 for m in positive_moments[p]), 'positive full nonzero-run moments')
    ternary_long = [m-F(2,3) for m in factor_moments(3,F(1),F(1))]
    require(ternary_long[0] == F(1,3), 'long ternary component mass is one third')

    patterns = {}
    moments = [F(0) for _ in orders]
    for mask in range(1 << len(primes)):
        z1 = prod(zero_atom[1][p] for i,p in enumerate(primes) if mask & (1 << i))
        z2 = prod(zero_atom[2][p] for i,p in enumerate(primes) if mask & (1 << i))
        z1, z2 = F(z1), F(z2)
        lo,hi = min(z1,z2),max(z1,z2)
        patterns[mask] = (lo,hi,z1,z2)
        require(lo > 0 and hi >= lo, 'joint products compared after multiplying each zero set')
        for ki in range(len(orders)):
            positive = prod(positive_moments[p][ki] for i,p in enumerate(primes)
                            if not mask & (1 << i))
            moments[ki] += (lo/3 + hi*ternary_long[ki])*positive
    reference_mass = sum((prod(allowed_mass[r].values()) for r in (1,2)),F(0))/3
    require(moments[0] == reference_mass, 'joint coloured raw mass equals actual reference mass')
    require(moments[0] >= h, 'one fixed source mass fits coloured comparison')

    # Nonzero-run low atoms, carrying the exact zero pattern until its joint min/max.
    cells = {(0,1):F(1)}
    for i,p in enumerate(primes):
        nxt = defaultdict(F)
        for (mask,z),weight in cells.items():
            nxt[(mask | (1 << i),z)] += weight
            for v in range(2,limit//z+1):
                nxt[(mask,z*v)] += weight*F(p-1,p**v)
        cells = dict(nxt)
    atoms = [F(0) for _ in range(limit+1)]
    for (mask,z),weight in cells.items():
        lo,hi,_,_ = patterns[mask]
        atoms[z] += weight*lo/3
        for v in range(2,limit//z+1):
            atoms[z*v] += weight*hi*F(2,3**v)
    require(all(a >= 0 for a in atoms), 'coloured low atoms nonnegative')
    return atoms, moments, allowed_mass, patterns, len(cells)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--library', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    lib = runpy.run_path(str(args.library), run_name='profile_arithmetic_library')
    require, snapshot, stoploss, append, trim, factor_moments = (
        lib[name] for name in ('require','snapshot','stoploss','append','trim','factor_moments'))
    require(lib['LIMIT'] == 256, 'declared low-load inventory256')
    require(lib['PRIMES'] == (3,5,7,11,13,17,19,23,29,31,37,41), 'declared old support')
    require(lib['ORDERS'] == (0,1,2,4), 'declared complete moment orders')
    limit, orders = lib['LIMIT'], lib['ORDERS']
    primes = lib['PRIMES'][1:]
    h = 1/lib['D0']
    require(h == F(36518862868606981,1816999451688960000), 'unchanged initial source mass')
    layout_count, finite_profile = finite_colour_controls(require)
    atoms, moments, allowed_mass, patterns, pattern_cells = build_coloured_profile(
        lib, {p:F(1,p) for p in primes}, h)
    raw = snapshot(atoms,moments)
    atoms,moments,initial_trim = trim(atoms,moments,h)
    initial = snapshot(atoms,moments)
    stages = []
    for q in (43,47,53,59,61,67,71,73):
        threshold = F(q-1,2)
        before = snapshot(atoms,moments)
        loss = stoploss(atoms,moments,threshold)
        charge = loss/threshold
        target = moments[0]-charge
        require(loss >= 0, 'nonnegative complete stop-loss')
        entry = {'prime':q,'delta':'1/2','cap':'2','before':before,
                 'threshold':str(threshold),'stop_loss':str(loss),'deletion_charge':str(charge),
                 'candidate_mass':str(target),'positive':target > 0,
                 'mean_gate':str((q-1)*moments[0]-moments[1])}
        if target <= 0:
            entry['decision'] = 'stop before appending first nonpositive fixed stage'
            stages.append(entry)
            break
        atoms,moments = append(atoms,moments,q,F(1),F(2))
        entry['appended'] = snapshot(atoms,moments)
        atoms,moments,certificate = trim(atoms,moments,target)
        entry['trim'] = certificate
        entry['after'] = snapshot(atoms,moments)
        stages.append(entry)
    completed = sum(s['positive'] for s in stages)
    density_cap = 2**completed

    # Existing Report734/779 quartic continuation at the fixed endpoint10000.
    b,ell = 10000,8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25, 'quartic parameter domain')
    for k,coefficient in {1:F(25),2:F(250,3),3:F(100),4:F(40)}.items():
        require(coefficient <= comb(25,k), 'inherited quartic growth domination')
    tau = (F(5625,6144)*F(2*ell*ell+1,2*ell*ell-1)**25*F(b,(b-1)**4)
           *sum((F(factorial(25),factorial(25-j)*(3*ell)**j) for j in range(26)),F(0)))
    reserve = moments[0]-moments[3]*tau
    require(len(stages) == 8 and completed == 7 and stages[-1]['prime'] == 73
            and not stages[-1]['positive'], 'fixed coloured prefix reaches71 and first fails73')
    require(moments[0] > F(1,500), 'coloured71 mass above1/500')
    require(moments[2] < F(157,10), 'coloured71 second moment below157/10')
    require(moments[3] < 8040000, 'coloured71 fourth moment below8040000')
    require(density_cap == 128, 'seven cap-two actual source updates')
    require(moments[0]/density_cap > F(1,64000), 'coloured71 actual head Haar lower bound')
    require(moments[1] > 73*moments[0], 'coloured71 normalized mean exceeds73')
    require(F(stages[-1]['mean_gate']) < 0, 'all legal constant73 clipping parameters fail this comparator')
    coarse_reserve = F(1,500)-8040000*tau
    require(coarse_reserve > F(19,10000), 'fixed quartic coarse reserve above19/10000')
    require(reserve > coarse_reserve, 'exact quartic reserve dominates short certificate')
    data = {
        'scope':'same FC159 eta0; actual retained first pure/star roots; N>=max(1,N_plus)',
        'source_mass':str(h),'retained_depth':1,'atom_limit':limit,'orders':orders,
        'dependency_hashes':{args.library.name:hashlib.sha256(args.library.read_bytes()).hexdigest()},
        'old_nonternary_primes':primes,'active_stars':{'1':[5],'2':[p for p in primes if p != 5]},
        'allowed_factor_masses':{str(r):{str(p):str(a) for p,a in allowed_mass[r].items()} for r in (1,2)},
        'zero_patterns':{str(mask):{'min_product':str(lo),'max_product':str(hi),
                                  'root1_product':str(z1),'root2_product':str(z2)}
                         for mask,(lo,hi,z1,z2) in patterns.items()},
        'pattern_low_atom_cells':pattern_cells,
        'finite_control':{'period':15,'complete_layouts':layout_count,
                          'profile':{str(z):str(w) for z,w in finite_profile.items()},
                          'attaining_layout':{'3':2,'5':1,'15':11}},
        'raw_coloured':raw,'initial_trim':initial_trim,'initial':initial,
        'declared_schedule':[43,47,53,59,61,67,71,73],'first_nonpositive_stops':True,
        'stages':stages,'final':snapshot(atoms,moments),'final_density_cap':str(density_cap),
        'actual_head_Haar_lower':str(moments[0]/density_cap),
        'quartic_tail_conditional_on_734_analytic_premise':{
            'B':b,'ell':ell,'tau4':str(tau),'exact_reserve':str(reserve),'positive':reserve > 0,
            'coarse_mass_lower':'1/500','coarse_M4_upper':'8040000',
            'coarse_reserve':str(coarse_reserve),'certified_reserve_lower':'19/10000'},
        'checks':require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'checks':data['checks'],'patterns':len(patterns),'low_pattern_cells':pattern_cells,
        'initial_cutoff':initial_trim['cutoff'],'stages':[
            {'q':s['prime'],'positive':s['positive'],'candidate_mass':float(F(s['candidate_mass'])),
             'mean_gate':float(F(s['mean_gate'])),
             **({'cutoff':s['trim']['cutoff'],'mean':float(F(s['after']['mean'])),
                 'M2':float(F(s['after']['moments']['2'])),
                 'M4':float(F(s['after']['moments']['4']))} if s['positive'] else {})} for s in stages],
        'quartic_reserve':float(reserve),'output':str(args.output)}))


if __name__ == '__main__':
    main()
