"""One stronger-source initialization and one fixed half-clipping schedule.

Read only saved raw_uniform comparisons and callable arithmetic definitions.
No source/profile producer or old controls; no phase, prime or policy search.
The source and all-query premise is Report528 FC487–FC497.
"""
import argparse
import ast
from fractions import Fraction as F
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import runpy

H84 = F(2826369, 131072000)
MU84 = F(21, 250)
CV = F(1048576, 403767)
SCHEDULE = (43, 47, 53, 59, 61, 67, 71, 73, 79)
DEFINITION_NAMES = ('require', 'factor_moments', 'append', 'snapshot', 'trim', 'stoploss')


def provenance(path):
    return {'file': path.name,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'hash_role': 'input provenance; not a mathematical premise'}


def load_arithmetic(path):
    # A custom run name leaves the guarded main and finite_controls unexecuted.
    source = path.read_text()
    tree = ast.parse(source, filename=str(path))
    functions = {node.name: node for node in tree.body
                 if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))}
    needed, pending = set(), list(DEFINITION_NAMES)
    while pending:
        name = pending.pop()
        if name in needed:
            continue
        if name not in functions:
            raise ArithmeticError('missing arithmetic definition: ' + name)
        node = functions[name]
        needed.add(name)
        if any(isinstance(x, ast.Name) and x.id == 'D0' for x in ast.walk(node)):
            raise ArithmeticError('old D0 enters required arithmetic definition: ' + name)
        for x in ast.walk(node):
            if isinstance(x, ast.Call) and isinstance(x.func, ast.Name):
                if x.func.id in functions and x.func.id not in needed:
                    pending.append(x.func.id)
    if {'main', 'finite_controls'} & needed:
        raise ArithmeticError('producer or controls reached by required arithmetic')
    lib = runpy.run_path(str(path), run_name='stronger_source_arithmetic_definitions')
    return lib, sorted(needed)


def reconstruct(raw, lib):
    require = lib['require']
    limit, orders = lib['LIMIT'], lib['ORDERS']
    require(set(raw['moments']) == {str(k) for k in orders}, 'complete raw moment orders')
    require(all(str(int(z)) == z and 1 <= int(z) <= limit
                for z in raw['low_atoms']), 'exact raw atom labels within retained limit')
    atoms = [F(raw['low_atoms'].get(str(z), '0')) for z in range(limit + 1)]
    moments = [F(raw['moments'][str(k)]) for k in orders]
    require(all(a >= 0 for a in atoms), 'nonnegative raw low atoms')
    require(lib['snapshot'](atoms, moments) == raw, 'saved raw_uniform reconstructed exactly')
    require(moments[0] >= H84, 'stronger source mass fits the raw comparison')
    return atoms, moments


def moment_record(moments, orders):
    return {str(k): str(value) for k, value in zip(orders, moments)}


def continue_case(raw, lib, tau4):
    require = lib['require']
    snapshot, trim, append, stoploss = (
        lib[name] for name in ('snapshot', 'trim', 'append', 'stoploss'))
    orders = lib['ORDERS']
    atoms, moments = reconstruct(raw, lib)
    raw_moments = moment_record(moments, orders)
    # This is a fresh Top_h84. Neither old initial nor old cutoff is consumed.
    atoms, moments, initial_trim = trim(atoms, moments, H84)
    require(moments[0] == H84, 'new initial source has exact h84')
    initial = snapshot(atoms, moments)
    stages, successful = [], []
    for q in SCHEDULE:
        threshold = F(q - 1, 2)
        gate = (q - 1) * moments[0] - moments[1]
        entry = {
            'prime': q, 'delta': '1/2', 'cap': '2', 'threshold': str(threshold),
            'before_moments': moment_record(moments, orders),
            'necessary_mean_gate': str(gate), 'necessary_condition_passes': gate > 0,
            'hinge_evaluated': False, 'update_executed': False,
            'successful': False,
        }
        if gate <= 0:
            entry['fixed_target_upper_bound_from_mean'] = str(gate / threshold)
            entry['decision'] = 'stop at nonpositive necessary mean gate; no hinge or update'
            stages.append(entry)
            break
        loss = stoploss(atoms, moments, threshold)
        require(loss >= 0, 'nonnegative exact complete hinge')
        charge = loss / threshold
        target = moments[0] - charge
        entry.update({'hinge_evaluated': True, 'stop_loss': str(loss),
                      'deletion_charge': str(charge), 'candidate_mass': str(target),
                      'fixed_target_positive': target > 0})
        require(target <= gate / threshold, 'fixed target obeys necessary mean upper bound')
        if target <= 0:
            entry['decision'] = 'stop at nonpositive fixed hinge target before append or trim'
            stages.append(entry)
            break
        old_mass = moments[0]
        atoms, moments = append(atoms, moments, q, F(1), F(2))
        require(moments[0] == old_mass, 'normalized cap-two factor preserves comparison mass')
        entry['appended_moments'] = moment_record(moments, orders)
        atoms, moments, certificate = trim(atoms, moments, target)
        require(moments[0] == target, 'stage trim reaches the newly certified source mass')
        entry.update({'trim': certificate, 'after': snapshot(atoms, moments),
                      'update_executed': True, 'successful': True,
                      'decision': 'positive fixed target; append cap two and trim'})
        stages.append(entry)
        successful.append(q)
    through79 = successful == list(SCHEDULE)
    next83 = {'considered': through79, 'hinge_evaluated': False, 'update_executed': False}
    if through79:
        gate83 = 82 * moments[0] - moments[1]
        next83.update({'necessary_mean_gate': str(gate83),
                       'necessary_condition_passes': gate83 > 0,
                       'decision': '83 necessary mean gate only; no hinge or update'})
    last = successful[-1] if successful else 41
    density = 2 ** len(successful)
    reserve = moments[0] - moments[3] * tau4
    return {
        'raw_uniform_moments': raw_moments,
        'raw_uniform_sha256': hashlib.sha256(
            json.dumps(raw, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
        'initial_trim': initial_trim, 'initial': initial,
        'declared_schedule': list(SCHEDULE),
        'gate_order': 'necessary mean, then hinge, then positive target, then append and trim',
        'stages': stages, 'successful_primes': successful,
        'last_positive_prime': last, 'through79': through79, 'next83': next83,
        'final': snapshot(atoms, moments), 'final_density_cap': str(density),
        'actual_head_Haar_lower': str(moments[0] / density),
        'excluded_additional_prime_interval': {
            'lower_exclusive': last, 'upper_inclusive': 10000},
        'quartic_tail_conditional_on_734_779_analytic_premise': {
            'B': 10000, 'ell': 8, 'delta': '2/5', 'growth_exponent': 25,
            'tau4': str(tau4), 'exact_reserve': str(reserve), 'positive': reserve > 0,
            'meaning': 'distorted-source mass reserve, not a final Haar-density bound',
            'additional_support_primes_strictly_greater_than': 10000,
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, required=True)
    parser.add_argument('--arithmetic-library', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    profile = json.loads(args.profile.read_text())
    lib, definitions = load_arithmetic(args.arithmetic_library)
    require = lib['require']
    require(profile['atom_limit'] == lib['LIMIT'] == 256, 'same exact retained low inventory')
    require(tuple(profile['orders']) == lib['ORDERS'] == (0, 1, 2, 4), 'complete moment orders')
    require(profile['retained_depth'] == 2 and profile['retained_group_depth'] == 1,
            'unchanged two pure/star layers and one shallow group layer')
    require(profile['prime_updates_executed'] == 0, 'profile input contains raw comparisons')
    require(set(profile['cases']) == {'FC110', 'FC131'}, 'separate two fixed assignments')
    require(tuple(profile['old_nonternary_primes']) == lib['PRIMES'][1:],
            'unchanged old prime support')
    require(H84 == F(2, 3) * MU84 / CV, 'proved new source mass normalization')
    b, ell = 10000, 8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25,
            'inherited fixed quartic parameter domain')
    for k, coefficient in {1: F(25), 2: F(250, 3), 3: F(100), 4: F(40)}.items():
        require(coefficient <= comb(25, k), 'inherited quartic growth domination')
    tau4 = (F(5625, 6144) * F(2*ell*ell + 1, 2*ell*ell - 1)**25
            * F(b, (b - 1)**4)
            * sum((F(factorial(25), factorial(25-j) * (3*ell)**j)
                   for j in range(26)), F()))
    cases = {}
    for name in ('FC110', 'FC131'):
        # No old initial, old source mass, source producer or controls are used.
        cases[name] = continue_case(profile['cases'][name]['raw_uniform'], lib, tau4)
        print(json.dumps({'event': 'case_complete', 'case': name,
                          'initial_cutoff': cases[name]['initial_trim']['cutoff'],
                          'last_positive_prime': cases[name]['last_positive_prime']}), flush=True)
    result = {
        'scope': 'Report528 FC487–FC497 finite auxiliary source for the FC417–FC478 normalized phase class, separately per fixed FC110/FC131 head assignment',
        'evidence': 'ordinary source/all-query premise plus exact rational arithmetic; no Lean claim',
        'input_profile': provenance(args.profile),
        'arithmetic_library': provenance(args.arithmetic_library),
        'arithmetic_definitions_used': definitions,
        'old_D0_used_by_arithmetic': False,
        'source_mass': str(H84), 'source_density_cap': str(1 / H84),
        'source_premise': {'pure_conditioned_survivor_lower': str(MU84),
                           'C_V': str(CV),
                           'completion': 'finite N_prime >= max(original_N,2,N84); N84 exists, not computed'},
        'orders': lib['ORDERS'], 'atom_limit': lib['LIMIT'],
        'declared_schedule': list(SCHEDULE),
        'no_parameter_search': True, 'no83hinge_or_update': True,
        'old_initial_consumed': False, 'old_producer_or_controls_executed': False,
        'cases': cases, 'checks': require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'output': str(args.output), 'checks': result['checks'],
        'cases': {name: {
            'initial_cutoff': case['initial_trim']['cutoff'],
            'last_positive_prime': case['last_positive_prime'],
            'mass': float(F(case['final']['moments']['0'])),
            'mean': float(F(case['final']['mean'])),
            'fourth_moment': float(F(case['final']['moments']['4'])),
            'quartic_reserve': float(F(case['quartic_tail_conditional_on_734_779_analytic_premise']['exact_reserve'])),
            'next83_considered': case['next83']['considered'],
            'next83_mean_passes': case['next83'].get('necessary_condition_passes'),
        } for name, case in cases.items()}}, indent=2))


if __name__ == '__main__':
    main()
