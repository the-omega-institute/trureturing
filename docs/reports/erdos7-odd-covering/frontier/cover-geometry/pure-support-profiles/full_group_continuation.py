"""Two separate fixed continuations from the saved full-group profiles.

Definitions-only canonical arithmetic; no initialization or source producer.
Each case stops first failure. At79 only the necessary mean test is allowed,
even when it passes. The fixed quartic tail is read at the last positive stage.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import comb,factorial
from pathlib import Path
import runpy


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed',type=Path,required=True)
    parser.add_argument('--arithmetic-library',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    seed = json.loads(args.seed.read_text())
    lib = runpy.run_path(str(args.arithmetic_library),run_name='profile_arithmetic_library')
    require,snapshot,stoploss,append,trim = (
        lib[name] for name in ('require','snapshot','stoploss','append','trim'))
    require(seed['atom_limit'] == lib['LIMIT'] == 256, 'same exact low inventory')
    require(tuple(seed['orders']) == lib['ORDERS'] == (0,1,2,4), 'same complete moments')
    require(seed['retained_depth'] == 2 and seed['retained_group_depth'] == 1,
            'fixed retained pure/star and group depth')
    require(seed['prime_updates_executed'] == 0, 'saved seed is initialization only')
    require(set(seed['cases']) == {'FC110','FC131'}, 'two whole actual source cases')
    h = F(seed['source_mass'])
    require(h == 1/lib['D0'], 'unchanged actual source mass')
    b,ell = 10000,8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25,
            'fixed inherited quartic domain')
    for k,c in {1:F(25),2:F(250,3),3:F(100),4:F(40)}.items():
        require(c <= comb(25,k), 'inherited quartic growth domination')
    tau = (F(5625,6144)*F(2*ell*ell+1,2*ell*ell-1)**25
           *F(b,(b-1)**4)*sum(
               (F(factorial(25),factorial(25-j)*(3*ell)**j) for j in range(26)),F(0)))
    cases = {}
    for name in ('FC110','FC131'):
        source = seed['cases'][name]
        initial = source['initial']
        atoms = [F(initial['low_atoms'].get(str(z),'0')) for z in range(257)]
        moments = [F(initial['moments'][str(k)]) for k in lib['ORDERS']]
        require(snapshot(atoms,moments) == initial, 'this source initial state reconstructed exactly')
        require(moments[0] == h, 'this physical source has unchanged h')
        stages = []
        for q in (43,47,53,59,61,67,71,73):
            threshold = F(q-1,2)
            before = snapshot(atoms,moments)
            loss = stoploss(atoms,moments,threshold)
            require(loss >= 0, 'complete stop-loss nonnegative')
            charge = loss/threshold
            target = moments[0]-charge
            entry = {'prime':q,'delta':'1/2','cap':'2','before':before,
                     'threshold':str(threshold),'stop_loss':str(loss),
                     'deletion_charge':str(charge),'candidate_mass':str(target),
                     'positive':target > 0,'mean_gate':str((q-1)*moments[0]-moments[1])}
            if target <= 0:
                entry['decision'] = 'stop this case before appending first nonpositive stage'
                stages.append(entry)
                break
            atoms,moments = append(atoms,moments,q,F(1),F(2))
            entry['appended'] = snapshot(atoms,moments)
            atoms,moments,certificate = trim(atoms,moments,target)
            entry['trim'] = certificate
            entry['after'] = snapshot(atoms,moments)
            stages.append(entry)
        positive = [s for s in stages if s['positive']]
        through73 = len(positive) == 8
        next79 = {'considered':through73,'hinge_evaluated':False,'update_executed':False}
        if through73:
            gap = 78*moments[0]-moments[1]
            next79.update({'necessary_mean_gate':str(gap),
                           'necessary_condition_passes':gap > 0,
                           'decision':('necessary condition passes; await authorization before any79 hinge or update'
                                       if gap > 0 else
                                       'all legal constant79 clipping ledgers nonpositive for this comparator')})
        density = 2**len(positive)
        reserve = moments[0]-moments[3]*tau
        cases[name] = {
            'source_file':source['source_file'],'source_hash':source['source_hash'],
            'initial':initial,'declared_schedule':[43,47,53,59,61,67,71,73],
            'first_nonpositive_stops':True,'stages':stages,'through73':through73,
            'next79':next79,'last_positive_prime':positive[-1]['prime'] if positive else 41,
            'final':snapshot(atoms,moments),'final_density_cap':str(density),
            'actual_head_Haar_lower':str(moments[0]/density),
            'quartic_tail_conditional_on_734_analytic_premise':{
                'B':b,'ell':ell,'tau4':str(tau),'exact_reserve':str(reserve),'positive':reserve > 0},
        }
    data = {
        'scope':'separate FC110/FC131 FC159 sources; same h; N>=max(2,N_plus); n2 pure/star; all36 first-depth groups',
        'evidence':'ordinary conditional theorem and exact arithmetic; no Lean claim',
        'seed_file':args.seed.name,'seed_hash':hashlib.sha256(args.seed.read_bytes()).hexdigest(),
        'dependency_hashes':{args.arithmetic_library.name:
                             hashlib.sha256(args.arithmetic_library.read_bytes()).hexdigest()},
        'source_mass':str(h),'atom_limit':256,'orders':lib['ORDERS'],
        'cases':cases,'no79hinge_or_update':True,'checks':require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'checks':data['checks'],'no79hinge_or_update':True,
        'cases':{name:{'last_positive_prime':c['last_positive_prime'],
                       'mass':float(F(c['final']['moments']['0'])),
                       'mean':float(F(c['final']['mean'])),
                       'M2':float(F(c['final']['moments']['2'])),
                       'M4':float(F(c['final']['moments']['4'])),
                       'density_cap':c['final_density_cap'],
                       '79necessary_passes':c['next79'].get('necessary_condition_passes'),
                       'quartic_reserve':float(F(c['quartic_tail_conditional_on_734_analytic_premise']['exact_reserve']))}
                 for name,c in cases.items()},'output':str(args.output)}))


if __name__ == '__main__':
    main()
