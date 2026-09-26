#!/usr/bin/env python3
"""Certify every five-live-leaf layout using exact integer interval gates.

Rebuilds the pinned rational input, compiles the sibling C++17 checker, checks
all 1,657,470 canonical layouts, and writes a self-contained result JSON.
Temporary binaries are reconstructed at each invocation and are not sources.
"""
import argparse
import base64
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import struct
import subprocess
import sys
from tempfile import TemporaryDirectory
import zlib

COUNT = 1657470
PINS = {
    'remaining33_global_root_exclusion_certificate.json':
        'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4',
    'joint_square_pair_225_star_certificate.json':
        'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5',
    'binary_leaf_pair_library_certificate.json':
        '4f64080de7056488b7299992ce8da2b7615410e8ddccc597ade50b323bff470d',
}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def summarize(directory, manifest, result, producer, checker):
    checks = Counter()

    def ck(name, ok):
        if not ok:
            raise ArithmeticError(name)
        checks[name] += 1

    for name, pin in PINS.items():
        ck('source_pin', digest(directory / name) == pin)
    ck('manifest_pins', manifest['source_sha256'] == PINS)
    ck('manifest_target', manifest['target_gate'] == '193/100000'
       and manifest['target_q40'] == 2122057442)
    ck('manifest_full_layout_count', manifest['canonical_layout_count'] == COUNT
       and manifest['actual_layout_count'] == 5**10)
    ck('result_length', len(result) == 168 + COUNT)
    header = struct.unpack('<21Q', result[:168])
    magic, count, failed, minimum, index, attempts, screens = header[:7]
    counts, min_layout = header[7:11], header[11:21]
    ck('result_schema', magic == 0x31544c5553455255)
    ck('complete_run', count == COUNT and failed == 0)
    ck('complete_uniform_gate', minimum >= 2122057442)
    selection = result[168:]
    got_counts = Counter(selection)
    ck('all_fields_selected', set(got_counts).issubset(range(4)))
    ck('family_counts', [got_counts[i] for i in range(4)] == list(counts))
    ck('minimum_index', index < COUNT)

    # Independent simple RGS traversal checks the indexing and orbit sizes.
    canonical = 0
    actual = 0
    current = [0] * 10

    def walk(at, used):
        nonlocal canonical, actual
        if at == 10:
            if canonical == index:
                ck('minimum_layout', tuple(current) == min_layout)
            canonical += 1
            actual += (1, 3, 6, 6)[used]
            return
        for color in (4, 5):
            current[at] = color
            walk(at + 1, used)
        for color in range(min(used + 1, 3)):
            current[at] = color
            walk(at + 1, max(used, color + 1))

    walk(0, 0)
    ck('canonical_count_independent', canonical == COUNT)
    ck('actual_count_independent', actual == 5**10)
    ck('burnside_count', (5**10 + 3 * 3**10 + 2 * 2**10) // 6 == COUNT)
    gate = F(minimum, 2**40)
    target = F(193, 100000)
    ck('public_gate_lower', gate > target)
    network = json.loads((directory / 'joint_square_pair_225_star_certificate.json').read_text())
    alpha = F(network['projection_alpha'])
    ck('projection', alpha == F(2673, 110656))
    policies = []
    for policy in network['policies']:
        fee = (F(network['finite_fee_upper']) + F(network['complete_five_parent_tail'])
               + F(network['ordinary_typeI_fee']) + F(policy['fee']))
        margin = alpha * (gate - fee)
        target_margin = alpha * (target - fee)
        threshold = F(2**40) * (fee + 1 / (F(2000000) * alpha))
        threshold_integer = threshold.numerator // threshold.denominator + 1
        ck('complete_network_density', margin > F(1, 2000000))
        ck('nominal_target_pays_network', target_margin > F(1, 2000000))
        ck('integer_network_threshold', minimum >= threshold_integer)
        policies.append(dict(kind=policy['kind'], K=policy['K'], complete_fee=str(fee),
                             projected_margin=str(margin),
                             nominal_target_projected_margin=str(target_margin),
                             strict_threshold_q40=threshold_integer,
                             density_denominator=2000000))
    payload = zlib.compress(selection, 9)
    ck('selection_roundtrip', zlib.decompress(payload) == selection)
    return dict(
        schema='full-five-live-leaf-library-interval-cover-v1',
        status='PASS', new_lean_verification=False,
        scope='All ten 9qs central roles independently in live leaves 0,1,2,4,5; '
              'fixed low pure phases/nulls/central15/square7 roles, all 50 retained '
              'root incidences, and declared ordinary/private interfaces remain.',
        source_sha256=PINS, producer_sha256=digest(producer),
        checker_sha256=digest(checker), input_manifest=manifest,
        result_binary_sha256=sha256(result).hexdigest(),
        edges=[list(e) for e in combinations((7, 11, 13, 17, 19), 2)],
        canonical_layout_order='At each edge visit 4,5,then 0..min(used,2); '
                               'regular labels form a restricted-growth string.',
        canonical_layout_count=count, actual_layout_count=actual,
        family_selection_rule='First passing whole family in order 3,0,1,2; '
                              'one family for all 95 corners and every query.',
        computed_corner_count=20, represented_corner_count=95,
        corner_attempts=attempts, nonzero_screen_evaluations=screens,
        selected_family_counts=list(counts),
        minimum=dict(q40=minimum, gate_lower=str(gate),
                     canonical_index=index, layout=list(min_layout),
                     selected_family=selection[index]),
        uniform_gate='193/100000', projection_alpha=str(alpha), policies=policies,
        selection=dict(encoding='zlib-9+base64', uncompressed_bytes=len(selection),
                       compressed_bytes=len(payload),
                       sha256=sha256(selection).hexdigest(),
                       compressed_sha256=sha256(payload).hexdigest(),
                       data=base64.b64encode(payload).decode('ascii')),
        checks=dict(checks), check_count=sum(checks.values()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--cxx', default='c++')
    parser.add_argument('--threads', type=int, default=8)
    args = parser.parse_args()
    source_dir = Path(__file__).resolve().parent
    preparer = source_dir / 'full_leaf_pair_library_interval_prepare.py'
    checker = source_dir / 'full_leaf_pair_library_interval_checker.cpp'
    with TemporaryDirectory(prefix='full-leaf-interval-') as temporary:
        work = Path(temporary)
        input_path, result_path, executable = work / 'input.bin', work / 'result.bin', work / 'checker'
        subprocess.run([sys.executable, '-I', '-S', '-B', '-O', str(preparer),
                        '--directory', str(args.directory), '--output', str(input_path)], check=True)
        subprocess.run([args.cxx, '-std=c++17', '-O3', '-pthread', str(checker), '-o', str(executable)], check=True)
        subprocess.run([str(executable), str(input_path), str(result_path), str(args.threads)], check=True)
        manifest = json.loads(input_path.with_suffix('.bin.json').read_text())
        if digest(input_path) != manifest['binary_sha256'] or digest(preparer) != manifest['preparer_sha256']:
            raise ArithmeticError('prepared input or preparer hash')
        out = summarize(args.directory, manifest, result_path.read_bytes(), Path(__file__), checker)
    output = args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(dict(status=out['status'], canonical_layout_count=out['canonical_layout_count'],
                          minimum=out['minimum'], density_denominator=2000000,
                          source_gate_checks=out['input_manifest']['check_count'],
                          summary_checks=out['check_count'])))


if __name__ == '__main__':
    main()
