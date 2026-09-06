#!/usr/bin/env python3
"""Replay a residual-sublevel cover and its ambient Hadamard exclusion radius.

The root proposals and graph are reused from real_x_supergraph_patch/input.json.
No previous success report is read. The base sublevel traversal and the nearby-
matrix local/graph checks are separate certificates joined by exact rational
arithmetic. This is a computational proof, not a Lean-kernel admission result.
"""
from __future__ import annotations

import argparse
import concurrent.futures
from fractions import Fraction as F
import itertools
import json
from pathlib import Path
import subprocess

import check_real_x_global_cover as original

I, C = original.I, original.C
require = original.require
SCALE = 1 << 40
EPSILON_BITS = 18
GUARD_BITS = 12
ENTRY_RADIUS_BITS = 24
ETA = F(1, 1 << EPSILON_BITS)
DELTA = F(1, 1 << ENTRY_RADIUS_BITS)


def ambient_matrix_bounds(path: Path) -> None:
    """Enclose every complex entry ball by a real/imaginary rectangle.

    H0 = [[J+(b-1)I, J+(e-1)I],
          [J+(conj(e)-1)I, -J-(conj(b)-1)I]],
    b=(-3+4i)/5 and e=(-2+i sqrt(21))/5.
    """
    b = C.point(F(-3, 5), F(4, 5))
    e = C(I.point(F(-2, 5)), original.base.sqrtI(21) / 5)
    rows = ['40']
    for i in range(6):
        for j in range(6):
            if i < 3 and j < 3:
                z = b if i == j else C.point(1)
            elif i < 3:
                z = e if i == j - 3 else C.point(1)
            elif j < 3:
                z = e.conj() if i - 3 == j else C.point(1)
            else:
                z = -b.conj() if i == j else C.point(-1)
            nums = []
            for x in (z.re, z.im):
                lo, hi = x.lo - DELTA, x.hi + DELTA
                nums.extend([lo.numerator * SCALE // lo.denominator,
                             -((-hi.numerator * SCALE) // hi.denominator)])
            rows.append(' '.join(map(str, nums)))
    path.write_text('\n'.join(rows) + '\n', encoding='utf-8')


def exclusion_graph(data: dict, enclosures: Path) -> dict:
    """Certify only supergraph containment. No symmetry persistence is used."""
    lines = enclosures.read_text(encoding='utf-8').splitlines()
    require(len(lines) == 61 and lines[0] == '60', 'bad root enclosure count')
    rays = {}
    for line in lines[1:]:
        x = list(map(int, line.split()))
        require(len(x) == 12, 'malformed enclosure row')
        idx, mask = x[:2]
        require(0 <= idx < 60 and idx not in rays and 0 <= mask < 32,
                'invalid or repeated ray label')
        ts = [I(F(x[2+2*j], SCALE), F(x[3+2*j], SCALE)) for j in range(5)]
        rays[idx] = original.base.phase_map(
            ts, [0] + [2 * ((mask >> j) & 1) for j in range(5)])
    require(set(rays) == set(range(60)), 'missing ray label')
    canonical = set(data['canonical_vertices'])
    colors = data['noncanonical_colors']
    edges = {tuple(edge) for edge in data['allowed_edges']}
    require(len(canonical) == 6 and canonical <= set(range(60)), 'bad canonical block')
    require(len(colors) == 60 and len(edges) == 114, 'malformed graph data')
    require(len(data['allowed_edges']) == len(edges), 'duplicate graph edge')
    require(all(0 <= i < j < 60 for i, j in edges), 'bad edge endpoints')
    require(all(colors[i] in (0, 1) for i in range(60) if i not in canonical),
            'bad noncanonical coloring')
    require(all((i in canonical and j in canonical) or
                (i not in canonical and j not in canonical and colors[i] != colors[j])
                for i, j in edges), 'edge violates the exclusion supergraph')
    count = 0
    lower = F(1)
    for i, j in itertools.combinations(range(60), 2):
        ip = sum((a.conj()*b for a, b in zip(rays[i], rays[j])), C.point()) / 6
        n = ip.normsq()
        require(n.hi < 1, f'rays {i},{j} are not certified distinct')
        if (i, j) not in edges:
            require(n.lo > F(1, 10**8), f'nonedge {i},{j} failed')
            lower = min(lower, n.lo)
            count += 1
    require(count == 1656, 'pair audit is incomplete')
    return {'distinct_rays': 60, 'pair_tests': 1770,
            'certified_nonedges': count,
            'nonedge_squared_modulus_lower_bound': '1/100000000',
            'minimum_interval_lower_bound': str(lower),
            'canonical_vertices': sorted(canonical),
            'noncanonical_supergraph_bipartite': True,
            'no_cross_edges': True,
            'canonical_shift_fixed': 'not asserted for arbitrary matrix perturbations',
            'graph_equality': False}


def checked_process(arguments: list[str], report_path: Path, expected: str) -> dict:
    report_path.unlink(missing_ok=True)
    result = subprocess.run(arguments, capture_output=True, text=True)
    require(result.returncode == 0,
            f'checker failed ({result.returncode}): {result.stderr}{result.stdout}')
    report = json.loads(report_path.read_text(encoding='utf-8'))
    require(report['status'] == expected, 'unexpected checker verdict')
    return report


def run(certificate: Path, output: Path, jobs: int, max_nodes: int) -> dict:
    require(__debug__, 'reused Fraction implementation requires assertions enabled')
    require(jobs >= 1 and max_nodes >= 1, 'invalid resource budget')
    output.mkdir(parents=True, exist_ok=True)
    verdict = output / 'verification.json'
    verdict.unlink(missing_ok=True)
    data = json.loads(certificate.read_text(encoding='utf-8'))
    # The old metadata only identifies the proposal source. Its old PASS and
    # claim flags are never consumed. All root and graph inequalities are rerun.
    centers, _, _ = original.prepare(data, output)
    original.base.symbolic_audit()
    source = Path(__file__).with_suffix('.cpp')
    binary = output / 'residual_barrier_core'
    subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra', '-Werror',
                    str(source), '-o', str(binary)], check=True)
    ambient_path = output / 'ambient_matrix_bounds.txt'
    ambient_matrix_bounds(ambient_path)
    local_path = output / 'ambient_local.json'
    local_args = [str(binary), str(centers), '32', '1', str(EPSILON_BITS),
                  str(GUARD_BITS), str(local_path), str(ambient_path)]

    def local_and_graph() -> tuple[dict, dict]:
        local = checked_process(local_args, local_path, 'LOCAL_GUARDS_VERIFIED')
        require(local['guards'] == 60 and local['guard_radius_bits'] == GUARD_BITS
                and local['dyadic_bits'] == 40
                and local['max_guard_contraction_dyadic'] < SCALE,
                'incorrect or noncontracting guard collection')
        graph = exclusion_graph(data, Path(str(local_path) + '.roots'))
        return local, graph

    def chart(mask: int) -> dict:
        path = output / f'sublevel_chart_{mask:02d}.json'
        args = [str(binary), str(centers), str(mask), str(max_nodes),
                str(EPSILON_BITS), str(GUARD_BITS), str(path)]
        report = checked_process(args, path, 'SUBLEVEL_COVERED')
        require(report['chart'] == mask and report['epsilon_bits'] == EPSILON_BITS
                and report['guard_radius_bits'] == GUARD_BITS
                and report['pending'] == report['unresolved'] == 0,
                'missing coverage or mismatched sublevel constants')
        print(f'chart {mask:02d}: {report["nodes"]} boxes', flush=True)
        return report

    # These parts depend only on the same exact centre proposals, not on each
    # other's verdicts. They are checked concurrently in this invocation.
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs + 1) as pool:
        future_local = pool.submit(local_and_graph)
        charts = list(pool.map(chart, range(32)))
        local, graph = future_local.result()
    require([r['chart'] for r in charts] == list(range(32)), 'missing phase chart')
    transfer = 30 * DELTA + 36 * DELTA**2
    require(transfer < ETA, 'matrix perturbation exceeds certified base residual gap')
    report = {
        'schema': 'mub-ambient-residual-barrier-v1', 'status': 'PASS',
        'claim_level': 'computational exclusion, subject to the documented analytic interpretation',
        'base_matrix': 'H0 over Q(i,sqrt(21)); see README and exact symbolic audit',
        'ambient_complex_entry_radius': str(DELTA),
        'ambient_constraint': 'H is an order-six complex Hadamard and max_ij norm(H_ij-H0_ij) <= radius',
        'base_residual_sublevel': str(ETA), 'guard_halfwidth': str(F(1, 1 << GUARD_BITS)),
        'root_transfer_bound': str(transfer), 'root_transfer_margin': str(ETA-transfer),
        'all_32_charts_covered': True, 'coverage': charts,
        'coverage_total': {'nodes': sum(r['nodes'] for r in charts), 'pending': 0, 'unresolved': 0},
        'local_guard_audit': local, 'graph': graph,
        'conclusions': {'all_actual_common_unbiased_rays_covered': True,
                        'at_most_one_completion_up_to_phases_and_permutation': True,
                        'no_quartet_containing_the_fixed_edge': True,
                        'affinity_equals_two': 'not asserted',
                        'full_X_family_excluded': False,
                        'global_dimension_six_conjecture_solved': False},
        'lean_kernel_verified': False,
        'intrinsic_information_admission': 'not executed; no finite Arena or positive gain asserted',
        'hashes': {'driver': original.digest(Path(__file__)),
                   'sublevel_core': original.digest(source),
                   'reused_cover_core': original.digest(source.with_name('check_real_x_global_cover.cpp')),
                   'reused_Fraction_kernel': original.digest(Path(original.base.__file__)),
                   'proposal_input': original.digest(certificate),
                   'centers': original.digest(centers),
                   'ambient_bounds': original.digest(ambient_path),
                   'local_enclosures': original.digest(Path(str(local_path)+'.roots'))}}
    verdict.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--max-nodes-per-chart', type=int, default=1_500_000)
    args = parser.parse_args()
    result = run(args.certificate, args.output, args.jobs, args.max_nodes_per_chart)
    print(json.dumps({k: v for k, v in result.items() if k != 'coverage'}, indent=2))
