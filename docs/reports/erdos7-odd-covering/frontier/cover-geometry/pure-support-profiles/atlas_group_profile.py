"""Uniform atlas grouped profile, followed by one fixed half-clipping schedule.

Use callable library definitions only. The private deletion is max(n5,n7)/q;
its direct row mass is an outer comparison mass, not an actual group survivor.
No source, prime, depth, order, or clipping search; no prior producer main.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
from math import comb, factorial, prod
from pathlib import Path
import runpy


def provenance(path):
    return {'file': path.name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'hash_role': 'provenance only; no hash admission condition'}


def private_positive_cells(private, limit):
    cells = {(3, 1): F(1)}
    for offset, q in enumerate(private, start=2):
        nxt = defaultdict(F)
        for (mask, load), weight in cells.items():
            nxt[(mask | (1 << offset), load)] += weight
            for v in range(2, limit // load + 1):
                nxt[(mask, load*v)] += weight * F(q-1, q**v)
        cells = dict(nxt)
    return cells


def continue_case(case, lib, tau):
    require = lib['require']
    snapshot, stoploss, append, trim = (lib[n] for n in ('snapshot', 'stoploss', 'append', 'trim'))
    atoms = [F(case['initial']['low_atoms'].get(str(z), '0')) for z in range(257)]
    moments = [F(case['initial']['moments'][str(k)]) for k in lib['ORDERS']]
    require(snapshot(atoms, moments) == case['initial'], 'same saved atlas initial state')
    stages = []
    for q in (43, 47, 53, 59, 61, 67, 71, 73):
        threshold = F(q-1, 2)
        loss = stoploss(atoms, moments, threshold)
        require(loss >= 0, 'nonnegative complete stop-loss')
        charge, target = loss/threshold, moments[0]-loss/threshold
        entry = {'prime': q, 'delta': '1/2', 'cap': '2',
                 'before_moments': {str(k): str(m) for k, m in zip(lib['ORDERS'], moments)},
                 'threshold': str(threshold), 'stop_loss': str(loss),
                 'deletion_charge': str(charge), 'candidate_mass': str(target),
                 'positive': target > 0, 'mean_gate': str((q-1)*moments[0]-moments[1])}
        if target <= 0:
            entry['decision'] = 'stop before appending first nonpositive fixed stage'
            stages.append(entry)
            break
        atoms, moments = append(atoms, moments, q, F(1), F(2))
        entry['appended_moments'] = {str(k): str(m) for k, m in zip(lib['ORDERS'], moments)}
        atoms, moments, entry['trim'] = trim(atoms, moments, target)
        entry['after'] = snapshot(atoms, moments)
        stages.append(entry)
    successful = [s for s in stages if s['positive']]
    through73 = len(successful) == 8
    density = 2**len(successful)
    next79 = {'considered': through73, 'hinge_evaluated': False, 'update_executed': False}
    if through73:
        gap = 78*moments[0]-moments[1]
        next79.update({'necessary_mean_gate': str(gap), 'necessary_condition_passes': gap > 0,
                       'decision': ('necessary condition passes; no79 hinge or update authorized'
                                    if gap > 0 else
                                    'all legal constant79 ledgers nonpositive for this comparator')})
    reserve = moments[0]-moments[3]*tau
    return {'initial': case['initial'], 'declared_schedule': [43,47,53,59,61,67,71,73],
            'first_nonpositive_stops': True, 'stages': stages, 'through73': through73,
            'last_positive_prime': successful[-1]['prime'] if successful else 41,
            'next79': next79, 'final': snapshot(atoms, moments),
            'final_density_cap': str(density), 'actual_head_Haar_lower': str(moments[0]/density),
            'quartic_tail_conditional_on_734_analytic_premise': {
                'B': 10000, 'ell': 8, 'tau4': str(tau), 'exact_reserve': str(reserve),
                'positive': reserve > 0}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('first-source', 'second-source', 'arithmetic-library', 'coloured-library',
                 'group-library', 'canonical-profile', 'profile-output', 'continuation-output'):
        parser.add_argument('--'+name, type=Path, required=True)
    args = parser.parse_args()
    lib = runpy.run_path(str(args.arithmetic_library), run_name='atlas_arithmetic_library')
    coloured = runpy.run_path(str(args.coloured_library), run_name='atlas_coloured_library')
    grouped = runpy.run_path(str(args.group_library), run_name='atlas_group_library')
    require, snapshot, trim, factor_moments = (lib[n] for n in ('require', 'snapshot', 'trim', 'factor_moments'))
    source_roles, head_rows = grouped['source_roles'], grouped['head_rows']
    primes, orders, limit = lib['PRIMES'][1:], lib['ORDERS'], lib['LIMIT']
    private, h = primes[2:], 1/lib['D0']
    require(primes == (5,7,11,13,17,19,23,29,31,37,41), 'declared old coordinates')
    require(orders == (0,1,2,4) and limit == 256, 'complete moments and exact low inventory')
    canonical = json.loads(args.canonical_profile.read_text())
    require(F(canonical['source_mass']) == h and canonical['retained_depth'] == 2
            and canonical['retained_group_depth'] == 1, 'canonical comparison contract')
    base_atoms, base_moments, allowed, base_patterns, base_cells = coloured['build_coloured_profile'](
        lib, {p: F(1,p)+F(1,p*p) for p in primes}, h)
    base_trim_atoms, base_trim_moments, base_trim_certificate = trim(base_atoms, base_moments, h)
    require(base_trim_certificate['cutoff'] == 8, 'pure/star reference split8')
    zero = {r: {p: allowed[r][p]-F(1,p) for p in primes} for r in (1,2)}
    heads = {r: {p: head_rows(p,r) for p in (5,7)} for r in (1,2)}
    for r in (1,2):
        for p in (5,7):
            require(sum(heads[r][p],F()) == allowed[r][p], 'literal finite head row masses')
    positive_moments = {p: [m-F(p-1,p) for m in factor_moments(p,F(1),F(1))] for p in primes}
    ternary_long = [m-F(2,3) for m in factor_moments(3,F(1),F(1))]
    cells = private_positive_cells(private, limit)
    cases = {}
    for name, path in (('FC110',args.first_source), ('FC131',args.second_source)):
        source = json.loads(path.read_text())
        roles, rows, masks = source_roles(source, name, require)
        old = canonical['cases'][name]
        require(rows == old['actual_rows'] and masks == old['selected_root_masks'], 'same fixed head assignment')
        root_data, deltas = {}, {}
        outer_mass = F()
        for r in (1,2):
            b5, b7 = heads[r][5], heads[r][7]
            weights = [b5[i]*b7[j] for i in range(5) for j in range(7)]
            w, conditional, counts = {}, {}, {}
            for q in private:
                role5, role7 = roles[q][5], roles[q][7]
                counts[q] = [(int(i == role5['free_row']) + int(r == role5['selected_root'] and i == role5['selected_row']),
                              int(j == role7['free_row']) + int(r == role7['selected_root'] and j == role7['selected_row']))
                             for i in range(5) for j in range(7)]
                w[q] = [F(max(n5,n7),q) for n5,n7 in counts[q]]
                require(all(0 <= debit <= F(n5+n7,q) < zero[r][q]
                            for debit,(n5,n7) in zip(w[q],counts[q])), 'uniform deletion and canonical positive bound')
                conditional[q] = [1-debit/zero[r][q] for debit in w[q]]
            root_outer = sum((weights[k]*prod(allowed[r][q]-w[q][k] for q in private) for k in range(35)),F())
            outer_mass += root_outer/3
            threshold = allowed[r][5]*allowed[r][7]-zero[r][5]*zero[r][7]
            full_h = [prod(conditional[q][k] for q in private) for k in range(35)]
            h_cells, K, root_delta, records = {0:[F(1)]*35}, {0:F(1)}, {}, {}
            for mask in range(512):
                if mask:
                    bit = mask & -mask
                    q = private[bit.bit_length()-1]
                    prev = mask ^ bit
                    h_cells[mask] = [x*y for x,y in zip(h_cells[prev],conditional[q])]
                    K[mask] = K[prev]*zero[r][q]
                H = [sum((b5[i]*h_cells[mask][7*i+j] for i in range(5)),F()) for j in range(7)]
                M = sum((b7[j]*H[j] for j in range(7)),F())
                old_pattern = old['root_conditions'][str(r)]['private_zero_patterns'][str(mask)]
                require(all(x >= y for x,y in zip(h_cells[mask],full_h)), 'subset dominates fullQ')
                require(all(H[j] >= F(1,5) for j in range(7) if b7[j]), 'all live head7 row conditions')
                require(threshold <= M <= allowed[r][5]*allowed[r][7], 'all total head conditions')
                require(all(x >= F(y) for x,y in zip(H,old_pattern['H_rows']))
                        and M >= F(old_pattern['M']), 'uniform head masses dominate canonical conditions')
                delta = K[mask]*(allowed[r][5]*allowed[r][7]-M)
                capacity = K[mask]*zero[r][5]*zero[r][7]
                require(0 <= delta <= F(old_pattern['delta']) <= capacity, 'safe zero debit between canonical and pure/star')
                root_delta[mask] = delta
                records[str(mask)] = {'K':str(K[mask]), 'H_rows':[str(x) for x in H],
                                      'M':str(M), 'delta':str(delta), 'headzero_capacity':str(capacity)}
            require(root_delta[0] == 0, 'empty private zero set unchanged')
            deltas[r] = root_delta
            full = records['511']
            root_data[str(r)] = {
                'head5_rows':[str(x) for x in b5], 'head7_rows':[str(x) for x in b7],
                'private_active_counts':{str(q):counts[q] for q in private},
                'uniform_private_deletion':{str(q):[str(x) for x in w[q]] for q in private},
                'fullQ_H_rows':full['H_rows'], 'fullQ_M':full['M'], 'total_threshold':str(threshold),
                'fullQ_live_row_min_margin':str(min(F(full['H_rows'][j])-F(1,5) for j in range(7) if b7[j])),
                'fullQ_total_margin':str(F(full['M'])-threshold),
                'direct_outer_mass':str(root_outer), 'private_zero_patterns':records}
        corrected, debit_patterns, debit_moments = {}, {}, [F() for _ in orders]
        for mask, (lo,hi,z1,z2) in base_patterns.items():
            root = {1:z1,2:z2}
            if mask & 3 == 3:
                for r in (1,2):
                    root[r] -= deltas[r][mask >> 2]
            old_pattern = old['full_zero_patterns'][str(mask)]
            require(F(old_pattern['root1_product']) <= root[1] <= z1
                    and F(old_pattern['root2_product']) <= root[2] <= z2, 'every root coefficient sandwiched')
            nl, nh = min(root.values()), max(root.values())
            require(0 <= nl <= nh and nl <= lo and nh <= hi, 'joint-colour positive correction')
            dl, dh = lo-nl, hi-nh
            corrected[str(mask)] = {'min_product':str(nl), 'max_product':str(nh),
                                    'root1_product':str(root[1]), 'root2_product':str(root[2])}
            debit_patterns[mask] = (dl,dh)
            for ki in range(len(orders)):
                positive = prod(positive_moments[p][ki] for i,p in enumerate(primes) if not mask & (1 << i))
                debit_moments[ki] += (dl/3+dh*ternary_long[ki])*positive
        debit_atoms = [F() for _ in range(limit+1)]
        for (mask,load), weight in cells.items():
            dl,dh = debit_patterns[mask]
            debit_atoms[load] += weight*dl/3
            for v in range(2,limit//load+1):
                debit_atoms[load*v] += weight*dh*F(2,3**v)
        atoms = [a-d for a,d in zip(base_atoms,debit_atoms)]
        moments = [m-d for m,d in zip(base_moments,debit_moments)]
        require(all(F(old['raw_grouped']['low_atoms'].get(str(z),'0')) <= atoms[z] <= base_atoms[z]
                    for z in range(limit+1)), 'low scalar atoms between canonical and pure/star')
        require(all(F(old['raw_grouped']['moments'][str(k)]) <= m <= b
                    for k,m,b in zip(orders,moments,base_moments)), 'complete raw moments sandwiched')
        require(moments[0] == outer_mass, 'artificial outer row-mass identity, not actual-source equality')
        require(moments[0] >= h, 'same actual mass fits outer profile')
        raw, debit = snapshot(atoms,moments), snapshot(debit_atoms,debit_moments)
        atoms, moments, certificate = trim(atoms,moments,h)
        require(certificate['cutoff'] == 8, 'inherited split8 bracket')
        require(all(F(old['initial']['moments'][str(k)]) <= m <= b
                    for k,m,b in zip(orders,moments,base_trim_moments)), 'same-h initial moments sandwiched')
        cases[name] = {'source':provenance(path), 'actual_rows':rows, 'selected_root_masks':masks,
                       'root_conditions':root_data, 'full_zero_patterns':corrected,
                       'direct_outer_mass':str(outer_mass), 'outer_mass_is_actual':False,
                       'raw_uniform':raw, 'group_debit':debit,
                       'initial_trim':certificate, 'initial':snapshot(atoms,moments)}
    profile = {
        'scope':'uniform over122 private-prefix atlas, separately per fixed FC110/FC131 head assignment; N>=max(2,N_plus)',
        'evidence':'ordinary all-query comparison and exact arithmetic; no new Lean certification',
        'comparison_deletion_rule':'max(n5,n7)/q; outer profile may lack a jointly realizing matching',
        'source_mass':str(h), 'retained_depth':2, 'retained_group_depth':1, 'atom_limit':limit, 'orders':orders,
        'old_nonternary_primes':primes, 'dependencies':[provenance(p) for p in
            (args.arithmetic_library,args.coloured_library,args.group_library,args.canonical_profile)],
        'base_pattern_low_atom_cells':base_cells, 'debit_pattern_low_atom_cells':len(cells),
        'cases':cases, 'prime_updates_executed':0, 'checks':require.__globals__['CHECKS']}
    args.profile_output.write_text(json.dumps(profile,indent=2)+'\n')
    print(json.dumps({'event':'profile_complete', 'checks':profile['checks'], 'output':str(args.profile_output),
                      'cases':{name:{'raw_mass':float(F(c['raw_uniform']['moments']['0'])),
                                      'cutoff':c['initial_trim']['cutoff'],
                                      'moments':{k:float(F(v)) for k,v in c['initial']['moments'].items()}}
                               for name,c in cases.items()}}), flush=True)
    b, ell = 10000, 8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25, 'fixed quartic domain')
    for k,c in {1:F(25),2:F(250,3),3:F(100),4:F(40)}.items():
        require(c <= comb(25,k), 'inherited quartic growth coefficients')
    tau = (F(5625,6144)*F(2*ell*ell+1,2*ell*ell-1)**25*F(b,(b-1)**4)
           *sum((F(factorial(25),factorial(25-j)*(3*ell)**j) for j in range(26)),F()))
    final_cases = {name:continue_case(case,lib,tau) for name,case in cases.items()}
    continuation = {'scope':profile['scope'], 'evidence':profile['evidence'],
                    'seed':provenance(args.profile_output), 'source_mass':str(h),
                    'atom_limit':limit, 'orders':orders, 'cases':final_cases,
                    'no79hinge_or_update':True,
                    'checks':require.__globals__['CHECKS']-profile['checks']}
    args.continuation_output.write_text(json.dumps(continuation,indent=2)+'\n')
    print(json.dumps({'event':'continuation_complete', 'checks':continuation['checks'],
                      'output':str(args.continuation_output), 'cases':{
                          name:{'last_positive_prime':c['last_positive_prime'],
                                'mass':float(F(c['final']['moments']['0'])),
                                'mean':float(F(c['final']['mean'])), 'M4':float(F(c['final']['moments']['4'])),
                                '79_mean_gate':c['next79'].get('necessary_mean_gate'),
                                'tail_reserve':float(F(c['quartic_tail_conditional_on_734_analytic_premise']['exact_reserve']))}
                          for name,c in final_cases.items()}}), flush=True)


if __name__ == '__main__':
    main()
