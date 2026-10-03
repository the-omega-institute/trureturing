"""Two fixed all-six shallow assignments; exact complete limiting min-cap fees.

Read the two declared source tables. Do not execute old evaluation mains,
finite controls, searches, initializations or continuations.
"""
import argparse
import ast
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import runpy

HEADS = (5, 7)
Q = (11, 13, 17, 19, 23, 29, 31, 37, 41)
ROOTS = (1, 2)
CHECKS = 0


def require(ok, message):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ArithmeticError(message)


def mul(xs):
    return prod(xs, start=F(1))


def load_definitions(path):
    source = path.read_text()
    tree = ast.parse(source, filename=str(path))
    functions = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}
    pending = ['read_witness', 'supported_head_sum']
    needed = set()
    while pending:
        name = pending.pop()
        if name in needed:
            continue
        require(name in functions, 'Required pure callable definition exists')
        needed.add(name)
        for n in ast.walk(functions[name]):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
                if n.func.id in functions and n.func.id not in needed:
                    pending.append(n.func.id)
    require(not needed.intersection({'evaluate', 'main'}),
            'Old producer or evaluator not in the arithmetic call closure')
    library = runpy.run_path(str(path), run_name='batch132_arithmetic_definitions')
    require(library['HEADS'] == HEADS and library['PRIVATE'] == Q and
            library['ROOTS'] == ROOTS, 'Exactly the declared source coordinates')
    return library, sorted(needed)


def extract_roles(data, b):
    result = {}
    for q in Q:
        by_head = {}
        for h in HEADS:
            record = data['private_sources'][str(q)][str(h)]
            free = [F(v) for v in record['free']]
            selected = {r: [F(v) for v in record['selected_increment'][str(r)]]
                        for r in ROOTS}
            free_rows = [i for i, v in enumerate(free) if v != 0]
            selected_rows = [(r, i) for r in ROOTS
                             for i, v in enumerate(selected[r]) if v != 0]
            require(len(free_rows) == 1 and free[free_rows[0]] == b[q],
                    'One complete free role at a unique actual head row')
            require(len(selected_rows) == 1 and
                    selected[selected_rows[0][0]][selected_rows[0][1]] == b[q],
                    'One complete selected role at one actual root and row')
            by_head[h] = {'free_row': free_rows[0],
                          'selected_root': selected_rows[0][0],
                          'selected_row': selected_rows[0][1],
                          'free_shallow_digit': 6, 'selected_shallow_digit': 6}
        result[q] = by_head
    return result


def evaluate_fixed(name, path, lib):
    source_checks = lib['Checks']()
    data, schema, c, b, w, old_arrays, g, digest = lib['read_witness'](path, source_checks)
    # Saved original arrays were validated by read_witness. They do not enter
    # any new group projection, group residual, remainder fee or score.
    del old_arrays
    roles = extract_roles(data, b)
    factors_p = {r: [] for r in ROOTS}
    factors_k = {r: [] for r in ROOTS}
    local = {r: [] for r in ROOTS}
    for r in ROOTS:
        epsilon = int(r == 2)
        for q in Q:
            u, tail = c[q] / q, c[q] / (q * (q - 1))
            f = u - (1 + epsilon) * tail
            require(f == g[r][q] / q and f > 0,
                    'Exact limiting all-six mass identity, not a finite-N substitute')
            p_matrix, k_matrix = [], []
            for i in range(5):
                p_row, k_row = [], []
                role5 = roles[q][5]
                alpha = int(i == role5['free_row'] or
                            (r == role5['selected_root'] and i == role5['selected_row']))
                for j in range(7):
                    role7 = roles[q][7]
                    beta = int(j == role7['free_row'] or
                               (r == role7['selected_root'] and j == role7['selected_row']))
                    x, y, z = alpha*f, beta*f, alpha*beta*f
                    h = g[r][q] - max(alpha, beta)*f
                    p = max(F(0), g[r][q] - x - y)
                    k = g[r][q] - max(x, y)
                    require(0 <= x <= g[r][q] and 0 <= y <= g[r][q] and
                            0 <= z <= min(x, y), 'Same-carrier raw subset guards')
                    require(h == g[r][q] - x - y + z == k,
                            'Literal all-six common union and H=K')
                    require(p == g[r][q] - x - y and 0 < p <= h <= g[r][q],
                            'Native lower factor stays on its positive branch')
                    require(x / g[r][q] == F(alpha, q) and
                            y / g[r][q] == F(beta, q), 'Boolean active-role saturation')
                    p_row.append(p)
                    k_row.append(k)
                    local[r].append({'q': q, 'i5': i, 'i7': j, 'alpha': alpha,
                                     'beta': beta, 'g': g[r][q], 'f': f,
                                     'X': x, 'Y': y, 'Z': z, 'H': h, 'P': p, 'K': k})
                p_matrix.append(p_row)
                k_matrix.append(k_row)
            factors_p[r].append(p_matrix)
            factors_k[r].append(k_matrix)

    full = (1 << len(Q)) - 1
    matrices = {}
    raw_residual, true_residual = {}, {}
    for r in ROOTS:
        matrices[r] = [[[F(1) for _ in range(7)] for _ in range(5)]]
        for mask in range(1, full + 1):
            bit = mask & -mask
            index = bit.bit_length() - 1
            previous = mask ^ bit
            matrices[r].append([[matrices[r][previous][i][j] * factors_k[r][index][i][j]
                                for j in range(7)] for i in range(5)])
        raw_residual[r] = sum((w[r][5][i]*w[r][7][j]*mul(
            factors_p[r][index][i][j] for index in range(len(Q)))
            for i, j in product(range(5), range(7))), F(0))
        true_residual[r] = sum((w[r][5][i]*w[r][7][j]*matrices[r][full][i][j]
                               for i, j in product(range(5), range(7))), F(0))
        require(0 <= raw_residual[r] <= true_residual[r] <= 1,
                'True skeleton residual dominates its native group lower bound')

    free_total, selected_total = F(0), F(0)
    support_records, buckets = [], {}
    primes = HEADS + Q
    for size in range(2, len(primes) + 1):
        for support in combinations(primes, size):
            fixed = tuple(h for h in HEADS if h in support)
            inside = sum(1 << index for index, q in enumerate(Q) if q in support)
            outside = full ^ inside
            lower = {h: 2 if size == 2 and len(fixed) == 1 else 1 for h in fixed}
            private_factor = mul(b[q] for q in Q if q in support)
            table = {}
            for address in product(*(range(h) for h in fixed)):
                row = dict(zip(fixed, address))
                values = {}
                for r in ROOTS:
                    values[r] = sum(((F(1) if 5 in fixed else w[r][5][i]) *
                                     (F(1) if 7 in fixed else w[r][7][j]) *
                                     matrices[r][outside][i][j]
                                     for i in ([row[5]] if 5 in fixed else range(5))
                                     for j in ([row[7]] if 7 in fixed else range(7))), F(0))
                    old_marginal = mul(g[r][q] for q in Q if q not in support) * mul(
                        sum(w[r][h]) for h in HEADS if h not in fixed)
                    require(0 <= values[r] <= old_marginal,
                            'Same-source unsupported-coordinate kernel has its actual cap')
                table[address] = values
            free, selected = lib['supported_head_sum'](fixed, table, lower, c, w)
            free, selected = private_factor*free, private_factor*selected
            require(free >= 0 and selected >= 0, 'Complete per-depth cap fees are nonnegative')
            free_total += free
            selected_total += selected
            support_records.append({'support': support, 'head_depth_lower': lower,
                                    'private_factor': private_factor,
                                    'free': free, 'selected': selected})
            key = ','.join(map(str, fixed)) or 'none'
            bucket = buckets.setdefault(key, {'supports': 0, 'free': F(0), 'selected': F(0)})
            bucket['supports'] += 1
            bucket['free'] += free
            bucket['selected'] += selected
    require(len(support_records) == 2036, 'Exactly the full FC159 support inventory')
    thresholds = {h: lib['threshold'](h, 1, c, w) for h in HEADS}
    require(all(value == 2 for value in thresholds.values()),
            'Unchanged head weights retain the exact existing depth-two geometric split')
    ap, ah = sum(raw_residual.values())/2, sum(true_residual.values())/2
    fee = free_total + selected_total
    jp, jh = ap - fee, ah - fee
    require(jh - jp == ah - ap >= 0, 'Two scores share exactly the same complete K fee')
    if jp > 0:
        settlement = 'native and true-group certificates both have strict positive margins'
    elif jh > 0:
        settlement = 'native nonpositive; true-group certificate has strict positive margin'
    elif jh == 0:
        settlement = 'true-group certificate zero; continuity supplies no strict margin'
    else:
        settlement = 'both declared certificates fail; no conclusion of actual covering'
    answer = {
        'case': name, 'source_schema': schema, 'source_filename': path.name,
        'source_sha256': digest, 'source_schema_checks': source_checks.count,
        'gamma': F(1, 2), 'pure_caps': c, 'head_weights': w, 'roles': roles,
        'all_shallow_digits': 6, 'local_raw_cells': local,
        'native_group_residual_roots': raw_residual,
        'true_group_residual_roots': true_residual,
        'A_P': ap, 'A_H': ah, 'free_fee': free_total,
        'selected_fee': selected_total, 'common_K_fee': fee,
        'J_P': jp, 'J_H': jh, 'J_P_positive': jp > 0, 'J_H_positive': jh > 0,
        'exact_group_gain': ah - ap, 'settlement': settlement,
        'support_count': len(support_records), 'head_tail_thresholds': thresholds,
        'support_fees': support_records, 'by_supported_heads': buckets,
        'finite_source': {
            'strict_margin_supplied': jh > 0,
            'explicit_N_computed': False,
            'scope': 'Finite existence by complete-depth continuity; no old query-profile or continuation claim',
        },
    }
    if jh > 0:
        mu = jh / 2
        answer['finite_source'].update({'mu_half_J_H': mu,
                                       'Haar_dominated_mass': F(2, 3)*mu/F(1048576, 403767)})
    return answer


def serialize(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): serialize(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [serialize(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--arithmetic-library', type=Path, required=True)
    parser.add_argument('--first-source', type=Path, required=True)
    parser.add_argument('--second-source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    lib, used = load_definitions(args.arithmetic_library)
    cases = {}
    for name, path in (('FC110', args.first_source), ('FC131', args.second_source)):
        cases[name] = evaluate_fixed(name, path, lib)
        print(json.dumps({'case_complete': name, 'J_P': float(cases[name]['J_P']),
                          'J_H': float(cases[name]['J_H']),
                          'settlement': cases[name]['settlement']}), flush=True)
    result = {
        'contract': 'Exactly two fixed all-six shallow families, fixed limiting caps, gamma=1/2, complete FC159 min-cap fee',
        'evidence': 'Ordinary common-source and continuity proofs plus exact rational arithmetic; no Lean claim',
        'private_primes': Q, 'head_primes': HEADS, 'all_shallow_digits': 6,
        'arithmetic_library_sha256': sha256(args.arithmetic_library.read_bytes()).hexdigest(),
        'arithmetic_definitions_used': used, 'cases': cases, 'checks': CHECKS,
        'old_evaluator_or_producer_executed': False,
        'old_finite_controls_executed': False, 'new_finite_controls_executed': False,
        'source_phase_parameter_search': False, 'continuation_executed': False,
    }
    args.output.write_text(json.dumps(serialize(result), indent=2) + '\n')
    print(json.dumps({'output': str(args.output), 'checks': CHECKS,
                      'source_schema_checks': {name: case['source_schema_checks']
                                               for name, case in cases.items()}}, indent=2))


if __name__ == '__main__':
    main()
