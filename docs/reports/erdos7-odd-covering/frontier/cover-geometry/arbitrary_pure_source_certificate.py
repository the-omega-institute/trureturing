#!/usr/bin/env python3
"""Complete twenty-source certificates for two retained endpoint interfaces.

Both models cover arbitrary fixed pure3/pure5 phases and finite heights.
The root-one model keeps Report617's outside layout; the matching model
uses Report623's arbitrary per-edge endpoints and possibly colliding stars.
This producer always checks all twenty sources for both models. It uses
exact rational preprocessing and the companion signed-integer C++ kernel.
The ordinary source/convexity proof is Report624; this is not Lean evidence.
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
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODELS = {
    'root_one': ('root_one_all_stars_certificate.py',
                 '826126df7f1a7c9f3d792ee8c206c5543609a6df97d4cd31d8b07a0425d8248a',
                 1 << 21, 1 << 24, F(11, 500)),
    'matching': ('matching_endpoint_certificate.py',
                 '69153d040ad621ac0ffb671bbf218d1d527a323a3284e79db852fcba16016324',
                 1 << 23, 1 << 27, F(7, 10000)),
}
CHECKS = []
ALPHA = F(2673, 110656)
FEE616 = F(20665363, 7987200000)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


orb = module('arbitrary_pure_source_orbits', HERE / 'pure_source_template_pair_orbits.py')


def check(name, condition, evaluations=1):
    if not condition:
        raise ArithmeticError(name)
    CHECKS.append(dict(name=name, evaluations=evaluations))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_data(kind, directory):
    filename, pin, hs, cs, target = MODELS[kind]
    source_path = HERE / filename
    check(kind + '_interval_producer_pin', sha(source_path) == pin)
    source = module('arbitrary_pure_intervals_' + kind, source_path)
    path = directory / (kind + '-reference.bin')
    reference = source.generate(HERE / 'actual_pair_activation_certificate.json', path)
    data = path.read_bytes()
    # Only the two coefficient arrays and ten source-independent local
    # interval grids are imported. Old source weights, cells and orbits
    # are not inputs to this twenty-source certificate.
    length = 2 * 512 * 8 + 10 * (256 + 8192) * 8
    check(kind + '_interval_shape', len(data) > length and
          reference['local_scale'] == hs and reference['coefficient_scale'] == cs)
    suffix = data[-length:]
    coeffs = struct.unpack('<1024q', suffix[:8192])
    gain = 1 - F(1084133, 201247200)
    glo, ghi = source.fp_floor(gain, cs), source.fp_ceil(gain, cs)
    check(kind + '_coefficient_signs', 0 <= glo <= ghi <= cs and
          all(0 <= lo <= hi for lo, hi in zip(coeffs[:512], coeffs[512:])))
    screen = 2 * hs * 675
    pair_bound = screen * (ghi + sum(coeffs[512:]))
    final_bound = 10000 * 10 * pair_bound
    check(kind + '_675_integer_overflow_bounds', screen < 2**63 and final_bound < 2**120)
    metadata = dict(producer=filename, producer_sha256=pin,
                    coefficient_source_sha256=reference['source_sha256'],
                    local_interval_suffix_sha256=hashlib.sha256(suffix).hexdigest(),
                    local_scale=hs, coefficient_scale=cs, central_denominator=675,
                    integer_arithmetic_ranges=dict(screen_abs_bound=str(screen),
                         pair_budget_abs_bound=str(pair_bound),
                         final_crossproduct_abs_bound=str(final_bound)),
                    reused_data='1024 coefficient endpoints and 84480 local interval entries only')
    path.unlink()
    return suffix, (hs, cs, glo, ghi), metadata


def case_data(index):
    case = orb.CASES[index]
    z, w, zz, ww = case
    weights3 = [0 if l == z else 1 if l == w else 2 for l in range(6)]
    weights5 = [0 if m == zz else 3 if m == ww else 4 for m in range(20)]
    ts = orb.templates(case)
    cells = tuple((l, m) for l, m in product(range(6), range(20))
                  if l != z and m != zz and (l//3, m//5) != (0, 0))
    codes = []
    for R, C, I, J, L, M in ts:
        codes.append(bytes((int(m//5 == C)*4 + int((l//3, m//5) == (I, J)) +
                            int(l == L) + int(m == M))*2 + int(l//3 != R)
                           for l, m in cells))
    check(f'case{index}_templates', len(ts) == len(set(ts)) == 5320)
    check(f'case{index}_source_mass', sum(weights3) == 9 and sum(weights5) == 75)
    sums = [(sum(row[k]//8 for row in codes),
             sum((row[k]//2) % 4 for row in codes),
             sum(row[k] % 2 for row in codes)) for k in range(len(cells))]
    check(f'case{index}_mean_at_every_cell',
          all((F(x, 5320), F(y, 5320), F(b, 5320)) ==
              (F(1, 4), F(1, 7)+F(1, 5)+F(1, 19), F(1, 2)) for x, y, b in sums),
          len(cells)*5320)
    pairs, weight, column_weights = [], 0, [0]*16
    for row in orb.ordered_template_pair_orbits(case):
        mask = 0
        for c, d, ii, jj in row.column_images:
            if ts[ii][1] != c or ts[jj][1] != d:
                raise ArithmeticError('transported orbit columns')
            mask |= 1 << (4*c+d)
        if row.size % mask.bit_count():
            raise ArithmeticError('column multiplicity')
        for pos in range(16):
            if mask >> pos & 1:
                column_weights[pos] += row.size // mask.bit_count()
        pairs.append((row.first_id, row.second_id, mask))
        weight += row.size
    check(f'case{index}_orbit_coverage', weight == 5320**2 and
          column_weights == [1330**2]*16, len(pairs))
    body = (bytes(weights3+weights5) + bytes(x for cell in cells for x in cell) +
            bytes(x for t in ts for x in t) + b''.join(codes) +
            b''.join(struct.pack('<3H', *p) for p in pairs))
    metadata = dict(case=index, source=case, positive_unmasked_cells=len(cells),
                    templates=len(ts), pair_representatives=len(pairs),
                    pair_orbit_size_sum=weight, column_fiber_weights=column_weights,
                    weights3=weights3, weights5=weights5)
    return body, metadata


def write_input(path, body, metadata, scales, suffix):
    with path.open('wb') as f:
        f.write(b'E7PURE20INTV1'.ljust(16, b'\0'))
        f.write(struct.pack('<7I', metadata['positive_unmasked_cells'], 5320,
                            metadata['pair_representatives'], 10, 16, 32, 675))
        f.write(struct.pack('<4q', *scales))
        f.write(body)
        f.write(suffix)


def transport_witnesses(index, certificate):
    case = orb.CASES[index]
    ts = orb.templates(case)
    ids = {t: i for i, t in enumerate(ts)}
    perms = orb.column_permutations(case[2], case[3])

    def transport(t, p):
        R, C, I, J, L, M = t
        return R, p[C], I, p[J], L, 5*p[M//5]+M % 5

    for table in certificate['tables']:
        representatives = table['argmin_template_ids']
        actual, transports = [], []
        for pos, (ii, jj) in enumerate(representatives):
            c, d = divmod(pos, 4)
            p = next((p for p in perms if p[ts[ii][1]] == c and p[ts[jj][1]] == d), None)
            if p is None:
                raise ArithmeticError('unrealizable table witness')
            actual.append([ids[transport(ts[ii], p)], ids[transport(ts[jj], p)]])
            transports.append(p)
        table['representative_template_ids'] = representatives
        table['argmin_template_ids'] = actual
        table['common_column_transports'] = transports
    check(f'case{index}_actual_table_witness_transports', True, 160)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    ap.add_argument('--keep-dir', type=Path)
    args = ap.parse_args()
    if not 1 <= args.threads <= 10:
        ap.error('--threads must be in 1..10')
    start = time.monotonic()
    cpp = Path(__file__).with_suffix('.cpp')
    with tempfile.TemporaryDirectory(prefix='arbitrary-pure-exact-') as td:
        directory = Path(td)
        inputs = args.keep_dir or directory
        inputs.mkdir(parents=True, exist_ok=True)
        exe = directory / 'verify'
        subprocess.run(['c++', '-std=c++20', '-O3', '-pthread', str(cpp), '-o', str(exe)], check=True)
        orbit_path = directory / 'orbits.json'
        orb.verify(orbit_path, exhaustive=True)
        result = dict(schema='arbitrary-pure-source-complete-gates-v1', complete=False,
                      scope='Arbitrary pure3/pure5 phases and finite heights, one actual source; two endpoint interfaces with the same restricted mixed inventory. No arbitrary head-prime or unrestricted Erdos #7 claim.',
                      source_density_D='13832/2025', full_head_density_C='110656/2673',
                      Haar_factor=str(ALPHA), source_orbits=json.loads(orbit_path.read_text()),
                      models={}, checks=CHECKS, producer_sha256=sha(Path(__file__)),
                      kernel_sha256=sha(cpp), orbit_generator_sha256=sha(HERE/'pure_source_template_pair_orbits.py'),
                      new_lean_verification=False)
        intervals = {}
        for kind in MODELS:
            suffix, scales, metadata = local_data(kind, directory)
            intervals[kind] = suffix, scales
            result['models'][kind] = dict(complete=False, complete_cases=[], results=[],
                                         local_interval_source=metadata)
        for index in range(20):
            body, metadata = case_data(index)
            for kind, (suffix, scales) in intervals.items():
                path = inputs / f'{kind}-case{index}.bin'
                write_input(path, body, metadata, scales, suffix)
                run = subprocess.run([str(exe), str(path), str(args.threads)],
                                     capture_output=True, text=True, check=True)
                certificate = json.loads(run.stdout)
                transport_witnesses(index, certificate)
                gate = F(int(certificate['gate_lower_numerator']), int(certificate['denominator']))
                check(f'{kind}_case{index}_positive_complete_gate', gate > MODELS[kind][4])
                row = dict(metadata, input_sha256=sha(path), gate=str(gate), certificate=certificate)
                model = result['models'][kind]
                model['results'].append(row)
                model['complete_cases'].append(index)
                result['elapsed_seconds'] = time.monotonic()-start
                args.output.write_text(json.dumps(result, indent=2)+'\n')
                print(kind, index, 'gate', str(gate), 'pairs', metadata['pair_representatives'],
                      'seconds', round(result['elapsed_seconds'], 2), flush=True)
                if not args.keep_dir:
                    path.unlink()
        for kind, model in result['models'].items():
            check(kind + '_all_twenty_cases', model['complete_cases'] == list(range(20)))
            minimum = min(model['results'], key=lambda r: F(r['gate']))
            gate = F(minimum['gate'])
            check(kind + '_uniform_strict_gate', gate > MODELS[kind][4])
            model.update(complete=True, minimum_case=minimum['case'], gate_lower=str(gate),
                         gate_strict=str(MODELS[kind][4]), haar_lower=str(ALPHA*gate),
                         pair_orbit_evaluations=sum(r['certificate']['pair_orbit_evaluations'] for r in model['results']),
                         joint_column_assignments=20*1024)
            if kind == 'root_one':
                check('root_one_ten_prime_head', ALPHA*gate > F(1, 1900))
                check('root_one_Report616_same_source_network', ALPHA*(gate-FEE616) > F(1, 2100))
                model.update(haar_strict='1/1900',
                             scope='Report617 fixed root-one outside layout, five distinct linear-star roots, anchored squares; all central phases arbitrary.',
                             network616=dict(fee_upper=str(FEE616), extendible_head_lower=str(ALPHA*(gate-FEE616)),
                                             strict='1/2100', full_density_lower='1/(2100 Q_off)'))
            else:
                check('matching_ten_prime_head', ALPHA*gate > F(1, 59000))
                check('matching_simple_margin', ALPHA*F(7, 10000) > F(1, 60000))
                check('matching_does_not_pay_Report616_fee', gate < FEE616)
                model.update(haar_strict='1/59000', simple_haar_strict='1/60000',
                             scope='Report623 arbitrary edge endpoints shared by twelve retained labels of each edge; live linear-star roots may coincide; both square stars remain anchored to their corresponding linear-star roots.',
                             network616='Not paid by this gate; no whole-network conclusion inherited.')
        result.update(complete=True, elapsed_seconds=time.monotonic()-start,
                      check_count=len(CHECKS), finite_evaluations=sum(c['evaluations'] for c in CHECKS))
        args.output.write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({kind: {key: model[key] for key in ('gate_lower', 'minimum_case', 'haar_lower')}
                          for kind, model in result['models'].items()}), flush=True)


if __name__ == '__main__':
    main()
