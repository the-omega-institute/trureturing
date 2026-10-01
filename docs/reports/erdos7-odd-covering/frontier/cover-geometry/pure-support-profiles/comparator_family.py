"""Fixed same-source two-comparator continuations, never a minimum measure.

Read saved initial laws only. Keep FC110 and FC131 wholly separate. For each
source, charge the least complete stop-loss and update every comparator to the
same mass. Compare with saved117; never invoke any initialization producer.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import runpy


NAMES = ('one_pair', 'full_group')
SCHEDULE = (43, 47, 53, 59, 61, 67, 71, 73)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pair-seed', type=Path, required=True)
    parser.add_argument('--full-seed', type=Path, required=True)
    parser.add_argument('--reference117', type=Path, required=True)
    parser.add_argument('--arithmetic-library', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pair, full, reference = (json.loads(p.read_text()) for p in
                            (args.pair_seed, args.full_seed, args.reference117))
    lib = runpy.run_path(str(args.arithmetic_library),
                        run_name='profile_arithmetic_library')
    require, snapshot, stoploss, append, trim = (
        lib[k] for k in ('require', 'snapshot', 'stoploss', 'append', 'trim'))
    orders = lib['ORDERS']
    require(lib['LIMIT'] == 256 and orders == (0, 1, 2, 4), 'arithmetic scope')
    h = F(pair['source_mass'])
    require(h == F(full['source_mass']) == F(reference['source_mass']) == 1/lib['D0'],
            'one unchanged initial source mass')
    for seed in (pair, full):
        require(seed['retained_depth'] == 2, 'saved depth-two pure/star bounds')
        require(seed['atom_limit'] == 256 and tuple(seed['orders']) == orders,
                'complete saved inventories agree')
        require(seed['prime_updates_executed'] == 0, 'seed is initialization only')
    require(full['retained_group_depth'] == 1, 'fixed full-group retained depth')
    require(pair['actual_group'] == {'modulus': 55, 'residue': 2, 'pair': [5, 11],
                                    'root_pair_zero_debit': '1/55'},
            'fixed actual pair shared by these two sources')
    require(set(full['cases']) == set(reference['cases']) == {'FC110', 'FC131'},
            'separate complete physical source cases')
    require(reference['seed_hash'] == sha(args.full_seed), '117 binds this full seed')
    require(reference['dependency_hashes'][args.arithmetic_library.name] ==
            sha(args.arithmetic_library), '117 shares canonical arithmetic')
    require(reference['no79hinge_or_update'], '117 reference has no79 update')

    b, ell = 10000, 8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25,
            'fixed inherited quartic domain')
    for k, c in {1: F(25), 2: F(250, 3), 3: F(100), 4: F(40)}.items():
        require(c <= comb(25, k), 'inherited quartic growth domination')
    tau = (F(5625, 6144)*F(2*ell*ell+1, 2*ell*ell-1)**25
           *F(b, (b-1)**4)*sum(
               (F(factorial(25), factorial(25-j)*(3*ell)**j)
                for j in range(26)), F(0)))
    cases = {}
    for source_name in ('FC110', 'FC131'):
        source, ref = full['cases'][source_name], reference['cases'][source_name]
        require(source['source_hash'] == ref['source_hash'] and
                source['source_file'] == ref['source_file'], 'same actual source as117')
        require(source['initial'] == ref['initial'], 'same full-group initialization')
        initial = {'one_pair': pair['initial'], 'full_group': source['initial']}
        bank = {}
        for name in NAMES:
            atoms = [F(initial[name]['low_atoms'].get(str(z), '0')) for z in range(257)]
            moments = [F(initial[name]['moments'][str(k)]) for k in orders]
            require(snapshot(atoms, moments) == initial[name], 'exact saved initial law')
            require(moments[0] == h, 'same initial physical mass in entire bank')
            bank[name] = (atoms, moments)
        current = h
        stages = []
        for q in SCHEDULE:
            threshold = F(q-1, 2)
            before, charges, losses = {}, {}, {}
            for name in NAMES:
                atoms, moments = bank[name]
                require(moments[0] == current, 'common source mass before charge')
                before[name] = snapshot(atoms, moments)
                losses[name] = stoploss(atoms, moments, threshold)
                require(losses[name] >= 0, 'complete hinge nonnegative')
                charges[name] = losses[name]/threshold
            charge = min(charges.values())
            minimizers = [name for name in NAMES if charges[name] == charge]
            chosen = minimizers[0]
            target = current-charge
            entry = {
                'prime': q, 'delta': '1/2', 'cap': '2', 'threshold': str(threshold),
                'common_before_mass': str(current), 'before': before,
                'stop_losses': {name: str(losses[name]) for name in NAMES},
                'deletion_charges': {name: str(charges[name]) for name in NAMES},
                'minimizers': minimizers, 'selected_comparator': chosen,
                'selected_charge': str(charge), 'candidate_mass': str(target),
                'positive': target > 0,
                'mean_gate': str((q-1)*current-min(bank[n][1][1] for n in NAMES)),
            }
            if target <= 0:
                entry['decision'] = 'stop this source before first nonpositive target'
                stages.append(entry)
                break
            entry.update({'appended': {}, 'trim': {}, 'after': {}})
            for name in NAMES:
                atoms, moments = bank[name]
                atoms, moments = append(atoms, moments, q, F(1), F(2))
                require(moments[0] == current, 'append is mass preserving for every comparator')
                entry['appended'][name] = snapshot(atoms, moments)
                atoms, moments, certificate = trim(atoms, moments, target)
                require(moments[0] == target, 'every comparator trimmed to same target')
                entry['trim'][name] = certificate
                entry['after'][name] = snapshot(atoms, moments)
                bank[name] = (atoms, moments)
            current = target
            stages.append(entry)

        positive = [s for s in stages if s['positive']]
        through73 = len(positive) == len(SCHEDULE)
        next79 = {'considered': through73, 'hinge_evaluated': False, 'update_executed': False}
        if through73:
            wmin = min(bank[n][1][1] for n in NAMES)
            next79.update({
                'first_moments': {n: str(bank[n][1][1]) for n in NAMES},
                'minimizers': [n for n in NAMES if bank[n][1][1] == wmin],
                'necessary_mean_gate': str(78*current-wmin),
                'necessary_condition_passes': 78*current > wmin,
                'decision': 'necessary mean test only; no79 hinge or physical update',
            })
        density = 2**len(positive)
        fourth = {n: bank[n][1][3] for n in NAMES}
        kmin = min(fourth.values())
        reserve = current-kmin*tau
        final = {n: snapshot(*bank[n]) for n in NAMES}

        # Compare saved trajectories without assuming an improvement or equality.
        require(tuple(ref['declared_schedule']) == SCHEDULE, 'same declared117 schedule')
        comparisons = []
        ref_by_q = {s['prime']: s for s in ref['stages']}
        for stage in stages:
            q = stage['prime']
            rstage = ref_by_q.get(q)
            comparison = {'prime': q, 'reference_stage_present': rstage is not None}
            if rstage is not None:
                difference = F(stage['candidate_mass'])-F(rstage['candidate_mass'])
                comparison.update({
                    'candidate_mass_difference': str(difference),
                    'candidate_mass_equal': difference == 0,
                    'positivity_equal': stage['positive'] == rstage['positive'],
                    'full_group_before_equal': stage['before']['full_group'] == rstage['before'],
                })
                if stage['positive'] and rstage['positive']:
                    after_diff = (F(stage['after']['full_group']['moments']['0'])-
                                  F(rstage['after']['moments']['0']))
                    comparison.update({
                        'after_mass_difference': str(after_diff),
                        'after_mass_equal': after_diff == 0,
                        'full_group_appended_equal': stage['appended']['full_group'] == rstage['appended'],
                        'full_group_trim_equal': stage['trim']['full_group'] == rstage['trim'],
                        'full_group_after_equal': stage['after']['full_group'] == rstage['after'],
                    })
            comparisons.append(comparison)
        tail_ref = ref['quartic_tail_conditional_on_734_analytic_premise']
        require(tau == F(tail_ref['tau4']) and b == tail_ref['B'] and ell == tail_ref['ell'],
                'same fixed complete fourth-moment tail envelope as117')
        mass_equal = current == F(ref['final']['moments']['0'])
        tail_equal = reserve == F(tail_ref['exact_reserve'])
        same_trajectory = (len(stages) == len(ref['stages']) and all(
            c['reference_stage_present'] and c['candidate_mass_equal'] and c['positivity_equal']
            and c['full_group_before_equal'] and c.get('after_mass_equal', True)
            and c.get('full_group_after_equal', True) for c in comparisons))
        full_selected_every_stage = all(s['selected_comparator'] == 'full_group' for s in stages)
        endpoint_equal = (mass_equal and final['full_group'] == ref['final'] and
                          F(density) == F(ref['final_density_cap']) and tail_equal and
                          current/density == F(ref['actual_head_Haar_lower']))
        no_improvement = full_selected_every_stage and same_trajectory and endpoint_equal
        cases[source_name] = {
            'source_file': source['source_file'], 'source_hash': source['source_hash'],
            'initial': initial, 'declared_schedule': SCHEDULE, 'first_nonpositive_stops': True,
            'stages': stages, 'through73': through73, 'next79': next79,
            'last_positive_prime': positive[-1]['prime'] if positive else 41,
            'final_common_mass': str(current), 'final': final,
            'final_density_cap': str(density), 'actual_head_Haar_lower': str(current/density),
            'quartic_tail_conditional_on_734_analytic_premise': {
                'B': b, 'ell': ell, 'tau4': str(tau),
                'fourth_moments': {n: str(fourth[n]) for n in NAMES},
                'minimizers': [n for n in NAMES if fourth[n] == kmin],
                'selected_M4': str(kmin), 'exact_reserve': str(reserve), 'positive': reserve > 0,
            },
            'comparison117': {
                'stages': comparisons, 'same_mass_and_full_group_trajectory': same_trajectory,
                'full_group_selected_every_stage': full_selected_every_stage,
                'full_group_final_snapshot_equal': final['full_group'] == ref['final'],
                'final_mass_difference': str(current-F(ref['final']['moments']['0'])),
                'final_mass_equal': mass_equal,
                'density_cap_difference': str(F(density)-F(ref['final_density_cap'])),
                'Haar_lower_difference': str(current/density-F(ref['actual_head_Haar_lower'])),
                'quartic_reserve_difference': str(reserve-F(tail_ref['exact_reserve'])),
                'endpoint_equal': endpoint_equal, 'no_improvement_stop_route': no_improvement,
            },
        }
    data = {
        'scope': 'two separately fixed FC159 sources; same-source bank only; no mixing',
        'evidence': 'same-source simultaneous comparison and exact rational arithmetic; no Lean claim',
        'input_hashes': {p.name: sha(p) for p in
                        (args.pair_seed, args.full_seed, args.reference117, args.arithmetic_library)},
        'source_mass': str(h), 'atom_limit': 256, 'orders': orders, 'comparator_order': NAMES,
        'cases': cases, 'no79hinge_or_update': True,
        'checks': require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({'execution': 'complete', 'checks': data['checks'],
                      'output': str(args.output), 'sha256': sha(args.output)}))


if __name__ == '__main__':
    main()
