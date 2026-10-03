"""One fixed continuation from the saved grouped initialization.

No initialization producer or finite control is rerun. The eight half steps
are fixed. At79 only the necessary mean comparison is read unless it passes;
then and only then one half step is evaluated. No parameter search.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import runpy


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed', type=Path, required=True)
    parser.add_argument('--arithmetic-library', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data0 = json.loads(args.seed.read_text())
    lib = runpy.run_path(str(args.arithmetic_library), run_name='profile_arithmetic_library')
    require, snapshot, stoploss, append, trim = (
        lib[name] for name in ('require','snapshot','stoploss','append','trim'))
    require(lib['LIMIT'] == data0['atom_limit'] == 256, 'exact low-atom limit256')
    require(tuple(data0['orders']) == lib['ORDERS'] == (0,1,2,4), 'complete moment orders')
    require(data0['retained_depth'] == 2 and data0['prime_updates_executed'] == 0,
            'saved depth-two initialization only')
    require(data0['actual_group'] == {'modulus':55,'residue':2,'pair':[5,11],
                                      'root_pair_zero_debit':'1/55'}, 'same actual group')
    h = F(data0['source_mass'])
    require(h == 1/lib['D0'], 'same source mass')
    initial = data0['initial']
    atoms = [F(initial['low_atoms'].get(str(z),'0')) for z in range(257)]
    moments = [F(initial['moments'][str(k)]) for k in lib['ORDERS']]
    require(snapshot(atoms,moments) == initial, 'saved complete initial state reconstructed exactly')
    stages = []

    def half_step(q, a, m):
        threshold = F(q-1,2)
        before = snapshot(a,m)
        loss = stoploss(a,m,threshold)
        require(loss >= 0, 'complete hinge nonnegative')
        charge = loss/threshold
        target = m[0]-charge
        entry = {'prime':q,'delta':'1/2','cap':'2','before':before,
                 'threshold':str(threshold),'stop_loss':str(loss),
                 'deletion_charge':str(charge),'candidate_mass':str(target),
                 'positive':target > 0, 'mean_gate':str((q-1)*m[0]-m[1])}
        if target <= 0:
            entry['decision'] = 'stop before appending first nonpositive half stage'
            return a,m,entry
        a,m = append(a,m,q,F(1),F(2))
        entry['appended'] = snapshot(a,m)
        a,m,certificate = trim(a,m,target)
        entry['trim'] = certificate
        entry['after'] = snapshot(a,m)
        return a,m,entry

    for q in (43,47,53,59,61,67,71,73):
        atoms,moments,entry = half_step(q,atoms,moments)
        stages.append(entry)
        if not entry['positive']:
            break
    through73 = len(stages) == 8 and all(s['positive'] for s in stages)
    next79 = {'considered':False,'hinge_evaluated':False,'update_executed':False}
    if through73:
        gate = 78*moments[0]-moments[1]
        next79.update({'considered':True,'existing_source':snapshot(atoms,moments),
                       'necessary_mean_gate':str(gate),
                       'necessary_condition_passes':gate > 0})
        if gate <= 0:
            next79['decision'] = 'all legal constant79 clipping ledgers nonpositive by the existing mean'
        else:
            next79['hinge_evaluated'] = True
            atoms,moments,entry = half_step(79,atoms,moments)
            stages.append(entry)
            next79['update_executed'] = entry['positive']
            next79['decision'] = 'one half79 evaluation after the necessary mean condition passed'

    positives = [s for s in stages if s['positive']]
    density_cap = 2**len(positives)
    last_prime = positives[-1]['prime'] if positives else 41
    b,ell = 10000,8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25,
            'fixed inherited quartic domain')
    for k, coefficient in {1:F(25),2:F(250,3),3:F(100),4:F(40)}.items():
        require(coefficient <= comb(25,k), 'inherited quartic growth domination')
    tau = (F(5625,6144)*F(2*ell*ell+1,2*ell*ell-1)**25
           *F(b,(b-1)**4)*sum(
               (F(factorial(25),factorial(25-j)*(3*ell)**j) for j in range(26)),F(0)))
    reserve = moments[0]-moments[3]*tau
    data = {
        'scope':'same FC159 eta0/h; N>=max(2,N_plus); depth-two pure/star and actual2mod55 group',
        'evidence':'ordinary mathematical comparison and exact rational arithmetic; no Lean claim',
        'seed_file':args.seed.name,'seed_hash':hashlib.sha256(args.seed.read_bytes()).hexdigest(),
        'dependency_hashes':{args.arithmetic_library.name:
                             hashlib.sha256(args.arithmetic_library.read_bytes()).hexdigest()},
        'source_mass':str(h),'atom_limit':256,'orders':lib['ORDERS'],
        'declared_schedule':[43,47,53,59,61,67,71,73],
        'initial':initial,'first_nonpositive_stops':True,'stages':stages,
        'through73':through73,'next79':next79,'last_positive_prime':last_prime,
        'final':snapshot(atoms,moments),'final_density_cap':str(density_cap),
        'actual_head_Haar_lower':str(moments[0]/density_cap),
        'quartic_tail_conditional_on_734_analytic_premise':{
            'B':b,'ell':ell,'tau4':str(tau),'exact_reserve':str(reserve),'positive':reserve > 0},
        'checks':require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'checks':data['checks'],'stages':[
        {'q':s['prime'],'positive':s['positive'],'mass':float(F(s['candidate_mass'])),
         **({'cutoff':s['trim']['cutoff'],'mean':float(F(s['after']['mean'])),
             'M2':float(F(s['after']['moments']['2'])),
             'M4':float(F(s['after']['moments']['4']))} if s['positive'] else {})}
        for s in stages], 'next79':{k:v for k,v in next79.items() if k != 'existing_source'},
        'last_positive_prime':last_prime,'density_cap':density_cap,
        'quartic_reserve':float(reserve),'output':str(args.output)}))


if __name__ == '__main__':
    main()
