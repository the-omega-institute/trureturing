#!/usr/bin/env python3
"""Complete twenty-source certificate with arbitrary seven-star first roots.

The first stage computes exact RICE boundary tables and selects every shared
state whose bound is at most 1/1000. The second stage uses conditional root-cell
boxes and enumerates every remaining leaf pair. All twenty central sources,
32 induced-support responses, and 512 inherited query costs are retained.
Each edge still shares one pair of first roots across its twelve retained
originals. This is ordinary exact arithmetic, not Lean verification or a
solution of unrestricted Erdos #7.
"""
import argparse
import hashlib
import importlib.util
import json
import struct
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
    'arbitrary_pure_source_certificate.py': '48c5266bcd91f681ee5b5f5b44130e6af2f4671a4a79b2877757279bbccb4eb7',
    'matching_endpoint_certificate.py': '69153d040ad621ac0ffb671bbf218d1d527a323a3284e79db852fcba16016324',
    'pure_source_template_pair_orbits.py': '3d2e86d09654f936a18d0e488fcb99abeb20114737df454bb396350fc960d1ca',
    'actual_pair_activation_certificate.json': '2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f',
}
QS = (7, 11, 13, 17, 19)
EDGES = tuple(combinations(range(5), 2))
HS, CS = 1 << 23, 1 << 27
THRESHOLD = F(1, 1000)
ALPHA = F(2673, 110656)
EXPECTED_GATE = F(190452499219361, 189995609279692800)
CHECKS = []


def check(name, condition, evaluations=1):
    if not condition:
        raise ArithmeticError(name)
    CHECKS.append(dict(name=name, evaluations=evaluations))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def floor(x, scale):
    return x.numerator * scale // x.denominator


def ceil(x, scale):
    return -((-x.numerator * scale) // x.denominator)


def load_dependencies(directory):
    global source624, algebra, orb, gain, coefficients, clo, chi, r, a, mean, hbar
    for name, pin in PINS.items():
        check('dependency_pin_' + name, sha(directory / name) == pin)
    source624 = module('unanchored_source624', directory / 'arbitrary_pure_source_certificate.py')
    algebra = module('unanchored_matching_algebra', directory / 'matching_endpoint_certificate.py')
    orb = source624.orb
    data = json.loads((directory / 'actual_pair_activation_certificate.json').read_text())
    c = F(data['constants']['continuation_c'])
    check('continuation_constant', c == F(1084133, 201247200))
    gain = 1 - c
    loss = list(map(F, data['complete_coefficients']['loss']))
    query = list(map(F, data['complete_coefficients']['weighted_nonunit_query']))
    check('complete_512_cost_arrays', len(loss) == len(query) == 512 and loss[0] == query[0] == 0)
    coefficients = [gain * l + c * w for l, w in zip(loss, query)]
    clo = [floor(x, CS) for x in coefficients]
    chi = [ceil(x, CS) for x in coefficients]
    check('nonnegative_directed_coefficients', all(0 <= F(lo, CS) <= x <= F(hi, CS)
          for x, lo, hi in zip(coefficients, clo, chi)), 512)
    screen = 675 * 2 * HS
    budget = screen * (ceil(gain, CS) + sum(chi))
    check('signed_integer_ranges', screen < 2**63 and 1000 * 10 * budget < 2**120)
    r = [F(1, q - 1) for q in QS]
    a = [F(1, q * (q - 2)) for q in QS]
    mean = [1 - F(3047, 2660) * x - F(3, 4) * y for x, y in zip(r, a)]
    hbar = [algebra.matching(31 ^ t, mean, r) for t in range(32)]
    return dict(dependencies=PINS, local_scale=HS, coefficient_scale=CS,
                central_denominator=675, integer_arithmetic_ranges=dict(
                    screen_abs_bound=str(screen), pair_budget_abs_bound=str(budget),
                    threshold_crossproduct_abs_bound=str(1000 * 10 * budget)))


def coarse_intervals():
    lower = [1 - 5*x - 2*y for x, y in zip(r, a)]
    upper = [F(1)] * 5
    umax = [r[q] * r[s] / (lower[q] * lower[s]) for q, s in EDGES]
    polynomials = []
    for mask in range(1024):
        selected = [e for e in range(10) if mask >> e & 1]
        value = 1 - sum((umax[e] for e in selected), F())
        value += sum((umax[e] * umax[f] for e, f in combinations(selected, 2)
                      if set(EDGES[e]).isdisjoint(EDGES[f])), F())
        polynomials.append(value)
    disjoint = max(sum((umax[j] for j in range(10)
                       if set(EDGES[i]).isdisjoint(EDGES[j])), F()) for i in range(10))
    check('strict_shearer_all_induced_subsets', min(polynomials) > 0 and
          min(polynomials) == polynomials[-1] and disjoint < 1, 1024)
    local = []
    for q in range(5):
        values = [1-r[q]-a[q]-(r[q]+a[q])*col-r[q]*n+(r[q]+a[q])*different
                  for col, n, different in product(range(2), range(4), range(2))]
        check(f'local_box_{q}', min(values) == lower[q] and max(values) == upper[q], 16)
        average = 1-r[q]-a[q]-(r[q]+a[q])/4-r[q]*(F(1,7)+F(1,5)+F(1,19))+(r[q]+a[q])/2
        check(f'template_mean_{q}', average == mean[q])
        local.append([v - mean[q] for v in values])
    alignment_count = 0
    for q in range(5):
        lam = r[q] / (r[q] + a[q])
        weights = (lam, 1-lam)
        for R1, R2, C1, C2, i, j, n in product(range(2), range(2), range(4), range(4), range(2), range(4), range(4)):
            actual = 1-r[q]*((i == R1)+(j == C1)+n)-a[q]*((i == R2)+(j == C2))
            corner = sum((weights[u]*weights[v]*(1-(r[q]+a[q])*((i == (R1,R2)[u])+(j == (C1,C2)[v]))-r[q]*n)
                          for u, v in product(range(2), repeat=2)), F())
            if actual != corner:
                raise ArithmeticError('seven-role whole-vector convex alignment')
            alignment_count += 1
    check('seven_role_convex_alignment', True, alignment_count)
    integrated = []
    for mask in range(32):
        lo = algebra.integrated_matching(mask, mean, lower, r)
        hi = algebra.integrated_matching(mask, mean, upper, r)
        check(f'integrated_box_{mask}', 0 < lo <= hi)
        integrated.append((lo, hi))
    suffix = bytearray(struct.pack('<512q', *clo) + struct.pack('<512q', *chi))
    for q, s in EDGES:
        em = (1 << q) | (1 << s)
        mass, query = [None]*256, [None]*8192
        for cq, cs in product(range(16), repeat=2):
            d, e = local[q][cq], local[s][cs]
            U, code = d*e, 16*cq+cs
            for T in range(32):
                base = hbar[T]/10
                if not T >> q & 1:
                    base += hbar[T | (1 << q)]*d/4
                if not T >> s & 1:
                    base += hbar[T | (1 << s)]*e/4
                lo, hi = (F(), F()) if T & em else integrated[31 ^ (T | em)]
                high = base+(hi if U >= 0 else lo)*U
                query[256*T+code] = ceil(high, HS)
                if T == 0:
                    mass[code] = floor(base+(lo if U >= 0 else hi)*U, HS)
        check(f'coarse_local_ranges_{q}_{s}', None not in mass+query and
              max(abs(v) for v in mass+query) <= 2*HS, 8448)
        suffix.extend(struct.pack('<256q', *mass))
        suffix.extend(struct.pack('<8192q', *query))
    return bytes(suffix), dict(strict_shearer_min=str(min(polynomials)),
                               disjoint_edge_sum=str(disjoint), mean_Z=list(map(str, mean)),
                               min_Z=list(map(str, lower)), max_Z=list(map(str, upper)),
                               local_suffix_sha256=hashlib.sha256(suffix).hexdigest())


def stateid(R, I, C, E):
    raw = 2*(4*(2*R+I)+C)+E
    if raw in (1, 17):
        raise ArithmeticError('empty RICE state')
    return raw-int(raw > 1)-int(raw > 17)


def decode(k):
    result = []
    for R, I, C, E in product(range(2), range(2), range(4), range(2)):
        if I == 0 and C == 0 and E == 1:
            continue
        if stateid(R, I, C, E) == k:
            result.extend((R, C, I, J) for J in range(4)
                          if (I, J) != (0, 0) and int(J == C) == E)
    if not result:
        raise ArithmeticError('unrealizable RICE state')
    return result


def transport_witnesses(index, certificate):
    case = orb.CASES[index]
    ts = orb.templates(case)
    ids = {t: i for i, t in enumerate(ts)}
    permutations = orb.column_permutations(case[2], case[3])
    states = [(x[0], x[2], x[1], int(x[3] == x[1])) for x in (decode(k)[0] for k in range(30))]

    def transport(t, p):
        R, C, I, J, L, M = t
        return R, p[C], I, p[J], L, 5*p[M//5]+M % 5

    for table in certificate['tables']:
        representatives = table['argmin_template_ids']
        actual, transports = [], []
        for pos, (ii, jj) in enumerate(representatives):
            left, right = states[pos//30], states[pos % 30]
            p = next((p for p in permutations if p[ts[ii][1]] == left[2] and p[ts[jj][1]] == right[2]), None)
            if p is None:
                raise ArithmeticError('unrealizable conditional table transport')
            x, y = transport(ts[ii], p), transport(ts[jj], p)
            if stateid(x[0], x[2], x[1], int(x[3] == x[1])) != pos//30 or stateid(y[0], y[2], y[1], int(y[3] == y[1])) != pos % 30:
                raise ArithmeticError('transport changes RICE fiber')
            actual.append([ids[x], ids[y]])
            transports.append(p)
        table['representative_template_ids'] = representatives
        table['argmin_template_ids'] = actual
        table['common_column_transports'] = transports
    check(f'case{index}_actual_table_witnesses', True, 9000)


def conditional_intervals(roots):
    base = [[1-(r[q]+a[q])*(int(i == R)+int(j == C))-r[q]*int((i,j) == (I,J))
             for i, j in product(range(2), range(4))]
            for q, (R, C, I, J) in enumerate(roots)]
    lower = [[base[q][c]-2*r[q] for c in range(8)] for q in range(5)]
    if not all(1-5*r[q]-2*a[q] <= lower[q][c] <= base[q][c] <= 1
               for q, c in product(range(5), range(8))):
        raise ArithmeticError('conditional box containment')
    integrated = {}
    for mask in range(32):
        if mask.bit_count() > 3:
            continue
        for c in range(8):
            lo = algebra.integrated_matching(mask, mean, [lower[q][c] for q in range(5)], r)
            hi = algebra.integrated_matching(mask, mean, [base[q][c] for q in range(5)], r)
            if not 0 < lo <= hi:
                raise ArithmeticError('conditional integrated ordering')
            integrated[mask, c] = lo, hi
    mass, query = [None]*720, [None]*23040
    for ei, (q, s) in enumerate(EDGES):
        em = (1 << q) | (1 << s)
        for c, nq, ns in product(range(8), range(3), range(3)):
            d = base[q][c]-r[q]*nq-mean[q]
            e = base[s][c]-r[s]*ns-mean[s]
            U, code = d*e, 3*nq+ns
            for T in range(32):
                value = hbar[T]/10
                if not T >> q & 1:
                    value += hbar[T | (1 << q)]*d/4
                if not T >> s & 1:
                    value += hbar[T | (1 << s)]*e/4
                lo, hi = (F(), F()) if T & em else integrated[31 ^ (T | em), c]
                upper = value+(hi if U >= 0 else lo)*U
                qi = ceil(upper, HS)
                if not F(qi-1, HS) < upper <= F(qi, HS):
                    raise ArithmeticError('query outward rounding')
                query[72*(32*ei+T)+9*c+code] = qi
                if T == 0:
                    lower_value = value+(lo if U >= 0 else hi)*U
                    mi = floor(lower_value, HS)
                    if not F(mi, HS) <= lower_value < F(mi+1, HS):
                        raise ArithmeticError('mass outward rounding')
                    mass[72*ei+9*c+code] = mi
    if None in mass+query or max(abs(x) for x in mass+query) > 2*HS:
        raise ArithmeticError('conditional interval range')
    return mass, query


def repair(index, coarse, inputs, executable):
    rows = coarse['repair_states']
    expected = {12: (114, 170), 14: (10, 10)}
    if index not in expected:
        raise ArithmeticError('unreviewed source requires conditional repair')
    den = int(coarse['denominator'])
    check(f'case{index}_selected_values', all(F(int(row['value']), den) <= THRESHOLD for row in rows))
    check(f'case{index}_unique_selected_states', len({tuple(row['states']) for row in rows}) == len(rows))
    layouts = [(row['states'], roots) for row in rows
               for roots in product(*(decode(k) for k in row['states']))]
    check(f'case{index}_all_J_branches', (len(rows), len(layouts)) == expected[index], len(layouts))
    path = inputs / f'conditional-case{index}.bin'
    with path.open('wb') as f:
        f.write(b'E7CONDTAILBOX1'.ljust(16, b'\0'))
        f.write(struct.pack('<I', len(layouts)))
        f.write(bytes(orb.CASES[index]))
        f.write(struct.pack('<4q', HS, CS, floor(gain, CS), ceil(gain, CS)))
        f.write(struct.pack('<512q', *clo))
        f.write(struct.pack('<512q', *chi))
        for shared, roots in layouts:
            mass, query = conditional_intervals(roots)
            f.write(bytes(shared))
            f.write(bytes(v for row in roots for v in row))
            f.write(struct.pack('<720q', *mass))
            f.write(struct.pack('<23040q', *query))
    run = subprocess.run([str(executable), str(path)], capture_output=True, text=True, check=True)
    certificate = json.loads(run.stdout)
    check(f'case{index}_returned_layouts', len(certificate['layouts']) == len(layouts))
    for (shared, roots), row in zip(layouts, certificate['layouts']):
        if row['shared_states'] != list(shared) or row['roots'] != list(map(list, roots)):
            raise ArithmeticError('conditional certificate layout identity')
    minimum = F(int(certificate['minimum_numerator']), int(certificate['denominator']))
    check(f'case{index}_conditional_margin', minimum > THRESHOLD)
    return dict(selected_states=len(rows), fixed_root_layouts=len(layouts),
                minimum=str(minimum), input_sha256=sha(path), certificate=certificate)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    ap.add_argument('--keep-dir', type=Path)
    ap.add_argument('--library-dir', type=Path, default=HERE,
                    help='directory containing the pinned existing canonical dependencies')
    args = ap.parse_args()
    if not 1 <= args.threads <= 10:
        ap.error('--threads must be in 1..10')
    start = time.monotonic()
    metadata = load_dependencies(args.library_dir.resolve())
    suffix, local_metadata = coarse_intervals()
    metadata.update(local_metadata)
    cpp = Path(__file__).with_suffix('.cpp')
    conditional_cpp = Path(__file__).with_name(Path(__file__).stem+'_conditional.cpp')
    with tempfile.TemporaryDirectory(prefix='unanchored-square-source-') as td:
        directory = Path(td)
        inputs = args.keep_dir or directory
        inputs.mkdir(parents=True, exist_ok=True)
        executable, conditional_executable = directory/'coarse', directory/'conditional'
        subprocess.run(['c++', '-std=c++20', '-O3', '-pthread', str(cpp), '-o', str(executable)], check=True)
        subprocess.run(['c++', '-std=c++20', '-O3', str(conditional_cpp), '-o', str(conditional_executable)], check=True)
        orbit_path = directory/'orbits.json'
        orb.verify(orbit_path, exhaustive=True)
        answer = dict(schema='unanchored-square-source-complete-gate-v1', complete=False,
                      scope=__doc__, threshold=str(THRESHOLD), Haar_factor=str(ALPHA),
                      source_orbits=json.loads(orbit_path.read_text()), local_intervals=metadata,
                      results=[], complete_cases=[], checks=CHECKS, template_checks=source624.CHECKS,
                      producer_sha256=sha(Path(__file__)), kernel_sha256=sha(cpp),
                      conditional_kernel_sha256=sha(conditional_cpp), new_lean_verification=False)
        for index in range(20):
            body, source_metadata = source624.case_data(index)
            path = inputs/f'coarse-case{index}.bin'
            with path.open('wb') as f:
                f.write(b'E7BOTH20INTV1'.ljust(16, b'\0'))
                f.write(struct.pack('<7I', source_metadata['positive_unmasked_cells'], 5320,
                                    source_metadata['pair_representatives'], 10, 16, 32, 675))
                f.write(struct.pack('<4q', HS, CS, floor(gain, CS), ceil(gain, CS)))
                f.write(body)
                f.write(suffix)
            run = subprocess.run([str(executable), str(path), str(args.threads)],
                                 capture_output=True, text=True, check=True)
            coarse = json.loads(run.stdout)
            check(f'case{index}_coarse_dimensions', coarse['joint_shared_state_assignments'] == 30**5 and
                  len(coarse['tables']) == 10 and all(len(t['costs']) == 900 for t in coarse['tables']))
            transport_witnesses(index, coarse)
            remaining = F(int(coarse['unrepaired_minimum_numerator']), int(coarse['denominator']))
            check(f'case{index}_unselected_margin', remaining > THRESHOLD)
            if coarse['repair_states']:
                conditional = repair(index, coarse, inputs, conditional_executable)
                lower = min(remaining, F(conditional['minimum']))
            else:
                conditional, lower = None, remaining
            check(f'case{index}_complete_margin', lower > THRESHOLD)
            answer['results'].append(dict(source_metadata, input_sha256=sha(path),
                                         coarse=coarse, conditional=conditional, gate=str(lower)))
            answer['complete_cases'].append(index)
            answer['elapsed_seconds'] = time.monotonic()-start
            args.output.write_text(json.dumps(answer, indent=2)+'\n')
            print(index, 'gate', lower, 'repair states', len(coarse['repair_states']),
                  'seconds', round(answer['elapsed_seconds'], 2), flush=True)
        check('all_twenty_sources', answer['complete_cases'] == list(range(20)))
        minimum = min(answer['results'], key=lambda row: F(row['gate']))
        gamma = F(minimum['gate'])
        check('reviewed_exact_uniform_gate', gamma == EXPECTED_GATE and gamma > THRESHOLD)
        check('uniform_haar_margin', ALPHA*gamma > F(1, 42000))
        answer.update(complete=True, minimum_case=minimum['case'], gate_lower=str(gamma),
                      gate_strict=str(THRESHOLD), haar_lower=str(ALPHA*gamma), haar_strict='1/42000',
                      pair_orbit_evaluations=sum(row['coarse']['pair_orbit_evaluations'] for row in answer['results']),
                      joint_shared_state_assignments=20*30**5,
                      conditional_pair_evaluations=sum(row['conditional']['certificate']['pair_evaluations']
                                                      for row in answer['results'] if row['conditional']),
                      elapsed_seconds=time.monotonic()-start, check_count=len(CHECKS),
                      finite_evaluations=sum(c['evaluations'] for c in CHECKS))
        args.output.write_text(json.dumps(answer, indent=2)+'\n')
        print(json.dumps({k: answer[k] for k in ('gate_lower', 'haar_lower', 'minimum_case', 'elapsed_seconds')}), flush=True)


if __name__ == '__main__':
    main()
