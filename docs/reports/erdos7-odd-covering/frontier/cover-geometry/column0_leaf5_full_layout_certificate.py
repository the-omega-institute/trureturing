#!/usr/bin/env python3
"""Certify both square7 rows at column0 leaf5 for every five-live-leaf layout.

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
}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def summarize(directory, manifest, result, producer, checker, row_role):
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
    ck('result_length', len(result) == 152 + COUNT)
    header = struct.unpack('<19Q', result[:152])
    magic, count, failed, minimum, index, attempts, screens = header[:7]
    counts, min_layout = header[7:9], header[9:19]
    ck('result_schema', magic == 0x31544c5553455255)
    ck('complete_run', count == COUNT and failed == 0)
    ck('complete_uniform_gate', minimum >= 2122057442)
    selection = result[152:]
    got_counts = Counter(selection)
    ck('all_fields_selected', set(got_counts).issubset(range(2)))
    ck('family_counts', [got_counts[i] for i in range(2)] == list(counts))
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
        schema='column0-one-row-full-layout-two-field-cover-v1',
        status='PASS', new_lean_verification=False,
        scope='All ten 9qs central roles independently in live leaves 0,1,2,4,5; '
              'fixed low pure phases/nulls/central15/square7 column0 leaf5 role, row specified by square7_roles, all 50 retained '
              'root incidences, and declared ordinary/private interfaces remain.',
        source_sha256=PINS, producer_sha256=digest(producer),
        checker_sha256=digest(checker), input_manifest=manifest,
        result_binary_sha256=sha256(result).hexdigest(),
        edges=[list(e) for e in combinations((7, 11, 13, 17, 19), 2)],
        canonical_layout_order='At each edge visit 4,5,then 0..min(used,2); '
                               'regular labels form a restricted-growth string.',
        canonical_layout_count=count, actual_layout_count=actual,
        family_selection_rule='First passing whole family in order constant_one,optimized_common_field; '
                              'one family for all 95 corners and every query.',
        square7_roles=[row_role,0,5],orbit_keys=manifest['orbit_keys'],families=manifest['families'],computed_corner_count=20, represented_corner_count=95,
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
    preparer = source_dir / 'column0_leaf5_full_layout_prepare.py'
    checker = source_dir / 'column0_leaf5_full_layout_checker.cpp'
    with TemporaryDirectory(prefix='full-leaf-interval-') as temporary:
        work = Path(temporary)
        input_path, result_path, executable = work / 'input.bin', work / 'result.bin', work / 'checker'
        subprocess.run([sys.executable, '-I', '-S', '-B', '-O', str(preparer),
                        '--directory', str(args.directory), '--output', str(input_path)], check=True)
        subprocess.run([args.cxx, '-std=c++17', '-O3', '-pthread', str(checker), '-o', str(executable)], check=True)
        manifest = json.loads(input_path.with_suffix('.bin.json').read_text())
        if digest(input_path) != manifest['binary_sha256'] or digest(preparer) != manifest['preparer_sha256']:
            raise ArithmeticError('prepared input or preparer hash')
        branches=[]
        for row_role in (0,1):
            subprocess.run([str(executable),str(input_path),str(result_path),str(args.threads),str(row_role)],check=True)
            branch=summarize(args.directory,manifest,result_path.read_bytes(),Path(__file__),checker,row_role)
            for key in ('schema','scope','status','new_lean_verification','source_sha256','producer_sha256','checker_sha256','input_manifest','edges','canonical_layout_order','family_selection_rule','orbit_keys','families'):
                branch.pop(key)
            branches.append(branch)
        out=dict(schema='column0-both-rows-full-layout-two-field-cover-v1',status='PASS',new_lean_verification=False,
                 scope='Square7 roles(row,0,5), row0 or1; all ten9qs central leaves independent. Fixed low pure phases/nulls/central15, all50 head incidences, arbitrary finite admitted higher pure/outside phases and ordinary/private interfaces remain.',
                 source_sha256=PINS,producer_sha256=digest(Path(__file__)),checker_sha256=digest(checker),input_manifest=manifest,
                 edges=[list(e)for e in combinations((7,11,13,17,19),2)],orbit_keys=manifest['orbit_keys'],families=manifest['families'],
                 canonical_layout_order='At each edge visit4,5,then0..min(used,2); regular labels form a restricted-growth string.',
                 family_selection_rule='First passing whole family in order constant_one,optimized_common_field; one family for all95 corners and every query.',
                 square7_roles=[[0,0,5],[1,0,5]],canonical_layout_count_per_role=COUNT,actual_layout_count_per_role=5**10,
                 branches=branches,summary_check_count=sum(b['check_count']for b in branches))
    output = args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(dict(status=out['status'],canonical_layout_count_per_role=COUNT,branches=[dict(square7_roles=b['square7_roles'],minimum=b['minimum'],selected_family_counts=b['selected_family_counts'])for b in branches],source_gate_checks=manifest['check_count'],summary_checks=out['summary_check_count'])))



if __name__ == '__main__':
    main()
