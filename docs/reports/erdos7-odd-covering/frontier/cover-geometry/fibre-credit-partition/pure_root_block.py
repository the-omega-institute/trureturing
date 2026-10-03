"""Consume the pinned 59 result; test only the declared 61/67/71 block.

Uses the preceding exact arithmetic library without reexecuting its main
or finite controls. Both explicit input files are SHA256-bound. No search.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import runpy

parser = argparse.ArgumentParser()
parser.add_argument('--seed-library', type=Path, required=True)
parser.add_argument('--seed', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
LIBRARY, SEED, OUTPUT = args.seed_library, args.seed, args.output
HASHES = {
    LIBRARY: '46a0282f006d410accf911a592d6dd09c85b8480e86df4d23e73fd8242bdfdb9',
    SEED: '6ab8d3935834724bc2b158a0806859ff41326c311ea234cd5e3549fff2efc568',
}
for path, expected in HASHES.items():
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ArithmeticError('explicit seed dependency digest mismatch')
lib = runpy.run_path(str(LIBRARY), run_name='profile_seed_library')
require, snapshot, stoploss, append, trim = (
    lib[name] for name in ('require', 'snapshot', 'stoploss', 'append', 'trim'))
data = json.loads(SEED.read_text())
state = data['stages'][-1]['after']
require(data['stages'][-1]['prime'] == 59, 'seed is exact completed 59 source')
atoms = [F(0) for _ in range(lib['LIMIT']+1)]
for z, v in state['low_atoms'].items():
    atoms[int(z)] = F(v)
moments = [F(state['moments'][str(k)]) for k in lib['ORDERS']]
require(snapshot(atoms, moments) == state, 'seed exact moments and tail replay')
records = []
density_cap = F(data['final_density_cap'])
for q in (61, 67, 71):
    threshold = F(q-1, 2)
    before = snapshot(atoms, moments)
    loss = stoploss(atoms, moments, threshold)
    charge = loss/threshold
    target = moments[0]-charge
    require(loss >= 0, 'nonnegative fixed block stop-loss')
    entry = {'prime': q, 'delta': '1/2', 'cap': '2', 'before': before,
             'threshold': str(threshold), 'stop_loss': str(loss),
             'deletion_charge': str(charge), 'candidate_mass': str(target),
             'mean_gate': str((q-1)*moments[0]-moments[1]),
             'positive': target > 0}
    if target <= 0:
        entry['decision'] = 'stop: declared half-clipping ledger is nonpositive'
        records.append(entry)
        break
    atoms, moments = append(atoms, moments, q, F(1), F(2))
    entry['appended'] = snapshot(atoms, moments)
    atoms, moments, certificate = trim(atoms, moments, target)
    entry['trim'] = certificate
    entry['after'] = snapshot(atoms, moments)
    density_cap *= 2
    records.append(entry)

b, ell = 10000, 8
tau = (F(5625,6144)*F(2*ell*ell+1,2*ell*ell-1)**25*F(b,(b-1)**4)
       *sum((F(factorial(25),factorial(25-j)*(3*ell)**j) for j in range(26)),F(0)))
require(tau == F(data['quartic_tail_conditional_on_734_analytic_premise']['tau4']),
        'same inherited quartic allowance')
reserve = moments[0]-moments[3]*tau
require(reserve > 0, 'last positive prefix still admits fixed quartic tail')
require(all(s['positive'] for s in records) and records[-1]['prime'] == 71,
        'whole declared block gives one positive source through71')
require(moments[0] > F(1,2800), 'final71 mass above1/2800')
require(moments[2] < F(51,5), 'final71 second moment below51/5')
require(moments[3] < 8150000, 'final71 fourth moment below8150000')
require(density_cap == 128, 'seven cap-two source operations')
require(moments[0]/density_cap > F(1,358400), 'final71 actual head Haar bound')
coarse_reserve = F(1,2800)-8150000*tau
require(coarse_reserve > F(1,4000), 'short71 quartic reserve above1/4000')
require(reserve > coarse_reserve, 'exact71 reserve dominates short reserve')
next_mean_gate = 72*moments[0]-moments[1]
require(next_mean_gate < 0, 'current71 comparator excludes all constant clipping at73')
result = {
    'dependency_hashes': {p.name: h for p,h in HASHES.items()},
    'declared_block': [61,67,71], 'first_nonpositive_stops': True,
    'stages': records, 'final': snapshot(atoms,moments),
    'final_density_cap': str(density_cap), 'actual_head_Haar_lower': str(moments[0]/density_cap),
    'conditional_quartic_tail': {'B': b, 'ell': ell, 'tau4': str(tau),
                                'exact_reserve': str(reserve),
                                'coarse_mass_lower': '1/2800', 'coarse_M4_upper': '8150000',
                                'coarse_reserve': str(coarse_reserve),
                                'certified_reserve_lower': '1/4000'},
    'next73_mean_gate': str(next_mean_gate),
    'checks': require.__globals__['CHECKS'],
}
OUTPUT.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'checks': result['checks'], 'stages': [
    {'q': s['prime'], 'positive': s['positive'], 'candidate_mass': float(F(s['candidate_mass'])),
     'mean_gate': float(F(s['mean_gate'])),
     **({'cutoff': s['trim']['cutoff'], 'mean': float(F(s['after']['mean'])),
         'M2': float(F(s['after']['moments']['2'])), 'M4': float(F(s['after']['moments']['4']))}
        if s['positive'] else {})} for s in records],
    'quartic_reserve': float(reserve), 'output': str(OUTPUT)}))
