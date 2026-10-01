"""One fixed two-case continuation from FC645's smaller all-height source.

Read explicit saved Xi_can raw data; execute only six extracted arithmetic
functions. No producer, dependency top level, controls, or parameter search.
Design: e7_batch142_continuation_design.md, SHA256
fd7d151d3c963267bd6a96a5f6776a9354106046e642a622e46291eb77223ed6.
"""
import argparse
import ast
from fractions import Fraction as F
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import sys

H_ALL = F(403767, 52428800)
MU_ALL = F(3, 100)
C_V = F(1048576, 403767)
SCHEDULE = (43, 47, 53, 59, 61, 67, 71, 73, 79)
ORDERS = (0, 1, 2, 4)
LIMIT = 256
PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
FUNCTION_NAMES = ('require', 'factor_moments', 'append', 'snapshot', 'trim', 'stoploss')
PROFILE_SHA256 = 'c40c5cb289b3d370bddb0c0c85c29a0904bf8f656c67352543c95dc8d82ca34d'
ARITHMETIC_SHA256 = '83712618f2c1cc2754c955b6a87aaa9d6294cfc79b216d8c09ce195da077b666'
DESIGN_SHA256 = 'fd7d151d3c963267bd6a96a5f6776a9354106046e642a622e46291eb77223ed6'


def read_pinned(path, expected):
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != expected:
        raise ArithmeticError('input fingerprint mismatch: ' + str(path))
    return data, {'file': str(path), 'sha256': digest,
                  'hash_role': 'input identity; not a mathematical premise'}


def load_arithmetic(path):
    data, provenance = read_pinned(path, ARITHMETIC_SHA256)
    tree = ast.parse(data.decode(), filename=str(path))
    functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    pending, needed = list(FUNCTION_NAMES), set()
    while pending:
        name = pending.pop()
        if name in needed:
            continue
        if name not in functions:
            raise ArithmeticError('missing arithmetic definition: ' + name)
        needed.add(name)
        node = functions[name]
        if any(isinstance(child, ast.Name) and child.id == 'D0' for child in ast.walk(node)):
            raise ArithmeticError('historical source mass enters arithmetic: ' + name)
        for child in ast.walk(node):
            if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
                if child.func.id in functions and child.func.id not in needed:
                    pending.append(child.func.id)
    if needed != set(FUNCTION_NAMES):
        raise ArithmeticError('unexpected transitive arithmetic closure')
    if {'main', 'finite_controls'} & needed:
        raise ArithmeticError('producer or controls reached')
    wanted = {'LIMIT': LIMIT, 'ORDERS': ORDERS, 'PRIMES': PRIMES, 'CHECKS': 0}
    constants = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
            if isinstance(target, ast.Name) and target.id in wanted:
                constants[target.id] = ast.literal_eval(node.value)
    if constants != wanted:
        raise ArithmeticError('arithmetic constants do not match the fixed design')
    namespace = {'F': F, **constants}
    definitions = ast.Module(body=[functions[name] for name in FUNCTION_NAMES], type_ignores=[])
    # Compile definitions only. No imports, global initializer, guarded main,
    # finite control, runpy, or profile producer from the source is executed.
    exec(compile(ast.fix_missing_locations(definitions), str(path), 'exec'), namespace)
    namespace['require'](H_ALL == F(2, 3) * MU_ALL / C_V,
                         'all-height source normalization')
    return namespace, provenance


def moment_record(moments):
    return {str(k): str(v) for k, v in zip(ORDERS, moments)}


def reconstruct(raw, lib):
    require = lib['require']
    require(set(raw) == {'moments', 'tail_moments_above_limit', 'low_atoms', 'mean'},
            'exact raw snapshot schema')
    require(set(raw['moments']) == {str(k) for k in ORDERS}, 'complete raw moment orders')
    require(set(raw['tail_moments_above_limit']) == {str(k) for k in ORDERS},
            'complete tail moment orders')
    require(set(raw['low_atoms']) == {str(z) for z in range(1, LIMIT + 1)},
            'saved canonical low inventory is exactly1 through256')
    atoms = [F(raw['low_atoms'].get(str(z), '0')) for z in range(LIMIT + 1)]
    moments = [F(raw['moments'][str(k)]) for k in ORDERS]
    require(all(a >= 0 for a in atoms), 'nonnegative exact raw atoms')
    require(lib['snapshot'](atoms, moments) == raw, 'saved raw_grouped reconstructed exactly')
    require(moments[0] >= H_ALL, 'smaller actual source fits the canonical raw comparison')
    return atoms, moments


def exact_trim(atoms, moments, target, lib):
    try:
        return lib['trim'](atoms, moments, target), None
    except ArithmeticError as error:
        if str(error) == 'upper-mass cutoff resolved in low atoms':
            return None, 'upper-mass cutoff unresolved within saved exact atoms1..256'
        raise


def tail_coefficient(lib):
    require = lib['require']
    b, ell = 10000, 8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4 * ell >= 25,
            'unchanged inherited quartic parameter domain')
    for k, coefficient in {1: F(25), 2: F(250, 3), 3: F(100), 4: F(40)}.items():
        require(coefficient <= comb(25, k), 'unchanged quartic growth domination')
    return (F(5625, 6144) * F(129, 127)**25 * F(b, (b - 1)**4)
            * sum((F(factorial(25), factorial(25 - j) * 24**j)
                   for j in range(26)), F()))


def continue_case(name, raw, lib, tau4):
    require, snapshot = lib['require'], lib['snapshot']
    atoms, moments = reconstruct(raw, lib)
    result = {
        'raw_key': 'cases.' + name + '.raw_grouped',
        'comparison': 'Xi_can',
        'raw_moments': moment_record(moments),
        'raw_sha256': hashlib.sha256(
            json.dumps(raw, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
        'declared_schedule': list(SCHEDULE),
        'gate_order': 'necessary mean, hinge, positive target, append, exact trim',
        'initialization_completed': False,
        'stages': [], 'successful_primes': [],
    }
    initialized, issue = exact_trim(atoms, moments, H_ALL, lib)
    if issue:
        result.update({'status': 'unresolved_initial_cutoff', 'reason': issue,
                       'next83': {'considered': False, 'hinge_evaluated': False,
                                  'update_executed': False}})
        return result
    atoms, moments, initial_trim = initialized
    require(moments[0] == H_ALL, 'fresh Top_h_all has exact prescribed mass')
    result.update({'initialization_completed': True, 'initial_trim': initial_trim,
                   'initial': snapshot(atoms, moments)})
    status = 'schedule_completed'
    for q in SCHEDULE:
        threshold = F(q - 1, 2)
        gate = (q - 1) * moments[0] - moments[1]
        entry = {
            'prime': q, 'delta': '1/2', 'cap': '2', 'threshold': str(threshold),
            'before_moments': moment_record(moments),
            'necessary_mean_gate': str(gate), 'necessary_condition_passes': gate > 0,
            'hinge_evaluated': False, 'append_executed': False,
            'trim_completed': False, 'update_executed': False, 'successful': False,
        }
        if gate <= 0:
            entry.update({'fixed_target_upper_bound_from_mean': str(gate / threshold),
                          'decision': 'stop at nonpositive necessary mean; no hinge or update'})
            result['stages'].append(entry)
            status = 'stopped_nonpositive_mean_gate'
            break
        loss = lib['stoploss'](atoms, moments, threshold)
        require(loss >= 0, 'nonnegative exact complete hinge')
        charge = loss / threshold
        target = moments[0] - charge
        require(target <= gate / threshold, 'half-clipping target obeys necessary mean upper bound')
        entry.update({'hinge_evaluated': True, 'stop_loss': str(loss),
                      'deletion_charge': str(charge), 'candidate_mass': str(target),
                      'fixed_target_positive': target > 0})
        if target <= 0:
            entry['decision'] = 'stop at nonpositive fixed hinge target before append or trim'
            result['stages'].append(entry)
            status = 'stopped_nonpositive_hinge_target'
            break
        appended_atoms, appended_moments = lib['append'](atoms, moments, q, F(1), F(2))
        require(appended_moments[0] == moments[0], 'normalized cap-two factor preserves mass')
        entry.update({'append_executed': True,
                      'appended': snapshot(appended_atoms, appended_moments)})
        trimmed, issue = exact_trim(appended_atoms, appended_moments, target, lib)
        if issue:
            entry.update({'decision': issue,
                          'reason': 'positive physical target, next numeric profile unresolved'})
            result['stages'].append(entry)
            status = 'stopped_unresolved_stage_cutoff'
            break
        atoms, moments, certificate = trimmed
        require(moments[0] == target, 'stage trim has the newly certified target mass')
        entry.update({'trim': certificate, 'after': snapshot(atoms, moments),
                      'trim_completed': True, 'update_executed': True, 'successful': True,
                      'decision': 'positive exact target; normalized cap-two append then trim'})
        result['stages'].append(entry)
        result['successful_primes'].append(q)
        print(json.dumps({'event': 'stage_complete', 'case': name, 'prime': q,
                          'cutoff': certificate['cutoff']}), flush=True)
    successful = result['successful_primes']
    through79 = successful == list(SCHEDULE)
    next83 = {'considered': through79, 'hinge_evaluated': False, 'update_executed': False}
    if through79:
        gate83 = 82 * moments[0] - moments[1]
        next83.update({'necessary_mean_gate': str(gate83),
                       'necessary_condition_passes': gate83 > 0,
                       'decision': '83 necessary mean diagnostic only; never hinge or update'})
    last = successful[-1] if successful else 41
    density = 2 ** len(successful)
    reserve = moments[0] - moments[3] * tau4
    result.update({
        'status': status, 'last_positive_prime': last, 'through79': through79,
        'next83': next83, 'final': snapshot(atoms, moments),
        'final_density_cap': str(density),
        'actual_head_Haar_lower': str(moments[0] / density),
        'excluded_additional_prime_interval': {'lower_exclusive': last, 'upper_inclusive': 10000},
        'quartic_tail_conditional_on_734_779_analytic_premise': {
            'B': 10000, 'ell': 8, 'delta': '2/5', 'growth_exponent': 25,
            'tau4': str(tau4), 'exact_reserve': str(reserve), 'positive': reserve > 0,
            'meaning': 'distorted-source mass reserve, not a final Haar-density lower bound',
            'additional_support_primes_strictly_greater_than': 10000,
        },
    })
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, required=True)
    parser.add_argument('--arithmetic-library', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    # Exact rational outputs can have long integer components; this changes
    # only the local formatting limit, with no global environment mutation.
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    if args.output.exists():
        raise RuntimeError('refusing to overwrite a prior result; one designated run only')
    data, input_provenance = read_pinned(args.profile, PROFILE_SHA256)
    profile = json.loads(data)
    lib, arithmetic_provenance = load_arithmetic(args.arithmetic_library)
    require = lib['require']
    require(profile['atom_limit'] == LIMIT, 'fixed exact low-atom limit')
    require(tuple(profile['orders']) == ORDERS, 'complete moment orders')
    require(profile['retained_depth'] == 2 and profile['retained_group_depth'] == 1,
            'unchanged two pure-star layers and canonical grouped coefficients')
    require(profile['prime_updates_executed'] == 0, 'saved input is pre-continuation')
    require(set(profile['cases']) == {'FC110', 'FC131'}, 'two separate fixed head tables')
    require(tuple(profile['old_nonternary_primes']) == PRIMES[1:], 'fixed old prime support')
    tau4 = tail_coefficient(lib)
    cases = {}
    for name in ('FC110', 'FC131'):
        cases[name] = continue_case(name, profile['cases'][name]['raw_grouped'], lib, tau4)
        case = cases[name]
        print(json.dumps({'event': 'case_complete', 'case': name,
                          'status': case['status'],
                          'initial_cutoff': case.get('initial_trim', {}).get('cutoff'),
                          'last_positive_prime': case.get('last_positive_prime')}), flush=True)
    result = {
        'scope': 'FC634-FC646 finite all-ternary-height nongroup inventory, direct full-target source or FC604-FC618 capacity extension; separately for FC110 and FC131',
        'evidence': 'ordinary source/query theorem plus exact saved-data rational arithmetic; no Lean claim',
        'design_sha256': DESIGN_SHA256,
        'consumer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_profile': input_provenance, 'arithmetic_library': arithmetic_provenance,
        'profile_selected_before_run': 'Xi_can only; cases[name].raw_grouped',
        'source_mass': str(H_ALL), 'orders': list(ORDERS), 'atom_limit': LIMIT,
        'source_premise': {
            'canonical_margin': str(MU_ALL), 'C_V': str(C_V),
            'completion': 'complete capacity source extended to N_prime>=max(N,2,N_all); no numerical N_all required',
            'excluded_old_cofactors': ['1', 'p^e', 'h*q^e with h in{5,7},q private'],
        },
        'arithmetic_definitions_used': list(FUNCTION_NAMES),
        'dependency_top_level_executed': False,
        'old_D0_used_by_arithmetic': False,
        'producer_or_controls_executed': False,
        'old_initial_or_continuation_consumed': False,
        'declared_schedule': list(SCHEDULE), 'no_parameter_search': True,
        'no83hinge_or_update': True,
        'execution': {'python': sys.version.split()[0], 'isolated': bool(sys.flags.isolated),
                      'site_disabled': bool(sys.flags.no_site),
                      'bytecode_disabled': bool(sys.flags.dont_write_bytecode)},
        'cases': cases, 'checks': lib['require'].__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'event': 'output_written', 'output': str(args.output),
                      'checks': result['checks'],
                      'cases': {name: {'status': c['status'],
                                        'last_positive_prime': c.get('last_positive_prime'),
                                        'next83_considered': c['next83']['considered']}
                                for name, c in cases.items()}}), flush=True)


if __name__ == '__main__':
    main()
