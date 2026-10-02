"""Optimistic pure-depth envelope; never a finite physical source bound.

One declared half-clipping schedule only. Load explicit arithmetic definitions,
record their source digest, and do not invoke their main or finite controls.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import runpy

parser = argparse.ArgumentParser()
parser.add_argument('--library', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
library_hash = hashlib.sha256(args.library.read_bytes()).hexdigest()
lib = runpy.run_path(str(args.library), run_name='depth2_arithmetic_library')
require, snapshot, stoploss, append, trim = (
    lib[name] for name in ('require', 'snapshot', 'stoploss', 'append', 'trim'))
require(lib['LIMIT'] == 256, 'declared low-load inventory256')
require(lib['PRIMES'] == (3,5,7,11,13,17,19,23,29,31,37,41), 'declared old prime support')
require(lib['ORDERS'] == (0,1,2,4), 'declared complete moment orders')
primes = lib['PRIMES']
moments = [F(1) for _ in lib['ORDERS']]
atoms = [F(0) for _ in range(lib['LIMIT']+1)]
atoms[1] = F(1)
factors = {}
for p in primes:
    mass = F(2,3) if p == 3 else F(p-2,p-1)
    factors[str(p)] = str(mass)
    atoms, moments = append(atoms,moments,p,mass,F(1))
raw = snapshot(atoms,moments)
h = 1/lib['D0']
source_mstar = F(36518862868606981,466438558966380000)
source_cv = F(1048576,403767)
require(moments[0] == F(2)/(3*source_cv), 'exact optimistic raw comparison mass')
require(0 < source_mstar < 1, 'fixed source constant lies strictly between zero and one')
require(h == source_mstar*moments[0], 'initial mass below optimistic raw mass')
atoms, moments, initial_trim = trim(atoms,moments,h)
initial = snapshot(atoms,moments)
stages = []
for q in (43,47,53,59,61,67,71,73):
    threshold = F(q-1,2)
    before = snapshot(atoms,moments)
    loss = stoploss(atoms,moments,threshold)
    charge = loss/threshold
    target = moments[0]-charge
    require(loss >= 0, 'nonnegative complete stop-loss')
    entry = {'prime': q, 'delta': '1/2', 'cap': '2', 'before': before,
             'threshold': str(threshold), 'stop_loss': str(loss),
             'deletion_charge': str(charge), 'candidate_ledger_mass': str(target),
             'positive': target > 0,
             'mean_gate': str((q-1)*moments[0]-moments[1])}
    if target <= 0:
        entry['decision'] = 'stop at first nonpositive optimistic fixed ledger'
        stages.append(entry)
        break
    atoms, moments = append(atoms,moments,q,F(1),F(2))
    entry['appended'] = snapshot(atoms,moments)
    atoms, moments, certificate = trim(atoms,moments,target)
    entry['trim'] = certificate
    entry['after'] = snapshot(atoms,moments)
    stages.append(entry)
require(len(stages) == 8 and all(s['positive'] for s in stages[:-1])
        and stages[-1]['prime'] == 73 and not stages[-1]['positive'],
        'optimistic fixed prefix ends71 and first fails73')
require(moments[1] > 87*moments[0], 'optimistic71 normalized mean exceeds87')
require(F(stages[-1]['mean_gate']) < -F(1,50), 'strict optimistic73 mean deficit')
require(F(stages[-1]['candidate_ledger_mass']) < -F(1,2000),
        'strict negative optimistic73 half-clipping ledger')
data = {
    'interpretation': 'optimistic ideal comparison envelope only; not a finite physical source',
    'dependency_hashes': {args.library.name: library_hash},
    'primes': primes, 'factor_masses': factors, 'initial_mass': str(h),
    'raw_mass_identity': {'C_V':str(source_cv), 'm_star':str(source_mstar),
                         'raw_mass':str(F(2)/(3*source_cv)),
                         'h_equals_mstar_times_raw_mass':True},
    'atom_limit': 256, 'orders': lib['ORDERS'],
    'declared_schedule': [43,47,53,59,61,67,71,73], 'first_nonpositive_stops': True,
    'raw_ideal': raw, 'initial_trim': initial_trim, 'initial': initial,
    'stages': stages, 'last_positive_prefix': snapshot(atoms,moments),
    'short_witness': {'last_prefix_mean_lower': '87', 'next_prime':73,
                      'mean_deficit_lower':'1/50', 'negative_ledger_magnitude_lower':'1/2000'},
    'checks': require.__globals__['CHECKS'],
}
args.output.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'checks':data['checks'], 'initial_cutoff':initial_trim['cutoff'],
    'stages':[{'q':s['prime'],'positive':s['positive'],
        'candidate_ledger_mass':float(F(s['candidate_ledger_mass'])),
        'mean_gate':float(F(s['mean_gate'])),
        **({'cutoff':s['trim']['cutoff'],'mean':float(F(s['after']['mean'])),
            'M2':float(F(s['after']['moments']['2'])),
            'M4':float(F(s['after']['moments']['4']))} if s['positive'] else {})}
        for s in stages], 'output':str(args.output)}))
