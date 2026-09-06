#!/usr/bin/env python3
"""Replay a seed residual-sublevel cover and a root-tube graph certificate.

All decisions use Fraction or outward dyadic arithmetic. No saved PASS is read.
The result is a computational proof under the documented analytic interpretation,
not Lean admission. Root existence, uniqueness, and exact count are not needed
by the tube-overlap consumer.
"""
from __future__ import annotations
import argparse
import concurrent.futures
from fractions import Fraction as F
import itertools
import json
from pathlib import Path
import subprocess

import check_real_x_global_cover as old

EPS = F(1, 2**18)
SIGMA = F(6, 2**24)
TAU = F(1, 2**19)
TUBE_RADIUS = F(1, 2**14)
NONEDGE = F(1, 10**8)
SAME = F(99, 100)
I, C = old.I, old.C


def require(ok, message):
    if not ok:
        raise ValueError(message)


def audit_tubes(data, center_path):
    lines = center_path.read_text().splitlines()
    require(len(lines) == 61 and lines[0] == '60', 'bad tube list')
    rays = {}
    for line in lines[1:]:
        parts = list(map(int, line.split()))
        require(len(parts) == 7, 'bad tube coordinate row')
        label, mask, *nums = parts
        require(0 <= label < 60 and label not in rays and 0 <= mask < 32,
                'duplicate or invalid tube label')
        ts = [I(F(n, old.SCALE)-TUBE_RADIUS,
                F(n, old.SCALE)+TUBE_RADIUS) for n in nums]
        chart = [0] + [2*((mask >> j) & 1) for j in range(5)]
        rays[label] = [C(old.old.rnd(z.re, 60), old.old.rnd(z.im, 60))
                       for z in old.base.phase_map(ts, chart)]
    canonical = set(data['canonical_vertices'])
    color = data['noncanonical_colors']
    edges = {tuple(e) for e in data['allowed_edges']}
    require(len(canonical) == 6 and len(color) == 60, 'bad graph labels')
    require(all(type(i) is int and 0 <= i < 60 for i in canonical), 'bad canonical labels')
    require(all(0 <= i < j < 60 for i, j in edges), 'bad edge endpoints')
    require(all(color[i] in (0, 1) for i in range(60) if i not in canonical),
            'invalid bipartition')
    require(all((i in canonical and j in canonical) or
                (i not in canonical and j not in canonical and color[i] != color[j])
                for i, j in edges), 'supergraph admits a forbidden type of edge')
    count = 0
    for i, j in itertools.combinations_with_replacement(range(60), 2):
        z = sum((a.conj()*b for a, b in zip(rays[i], rays[j])), C.point()) / 6
        ns = z.normsq()
        if i == j:
            # The two occurrences are interval-independent. Thus this bounds
            # ANY two phase vectors in the same tube, not just a vector itself.
            require(ns.lo > SAME, f'poor same-tube separation: {i}')
        elif (i, j) not in edges:
            require(ns.lo > NONEDGE, f'uncertified nonedge: {i},{j}')
            count += 1
    require(count == 1656, 'unexpected forbidden-pair count')
    return {'tubes': 60, 'forbidden_pairs': count,
            'same_tube_overlap_strict_lower': str(SAME),
            'forbidden_pair_overlap_strict_lower': str(NONEDGE),
            'canonical_vertices': sorted(canonical),
            'noncanonical_supergraph_bipartite': True,
            'root_existence_or_uniqueness_used': False}


def constants():
    require(TAU <= F(1, 4), 'approximate-root target too loose')
    require(TAU+SIGMA*(5+SIGMA) < EPS, 'seed residual budget exceeded')
    require(TAU**2 < NONEDGE <= SAME, 'within-frame graph threshold insufficient')
    require(TAU**2 < (SAME-F(1, 6))**2, 'cross-frame gap insufficient')
    return {'seed_sublevel': str(EPS), 'column_l1_matrix_radius': str(SIGMA),
            'entrywise_max_radius_guaranteed': str(SIGMA/6),
            'per_entry_approximate_residual': str(TAU),
            'seed_residual_upper_at_nearby_approximate_root':
                str(TAU+SIGMA*(5+SIGMA)),
            'two_completion_energy_lower_bound': str(TAU**2)}


def run(certificate: Path, output: Path, jobs: int, max_nodes: int):
    output.mkdir(parents=True, exist_ok=True)
    # A failed rerun must never leave a stale success verdict at this output.
    for name in ('verification.json', 'failure.json'):
        (output/name).unlink(missing_ok=True)
    require(__debug__, 'reused interval kernel requires Python assertions enabled')
    require(1 <= jobs <= 32 and max_nodes > 0, 'invalid resource limit')
    data = json.loads(certificate.read_text())
    old.base.symbolic_audit()  # exact Q(i,sqrt(21)) seed identities
    center_path, _, _ = old.prepare(data, output)
    graph = audit_tubes(data, center_path)
    budget = constants()
    source = Path(__file__).with_name('check_real_x_residual_barrier.cpp')
    binary = output/'residual_cover'
    subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra',
                    str(source), '-o', str(binary)], check=True)

    def chart(n):
        report = output/f'chart_{n:02d}.json'
        if report.exists():
            report.unlink()
        result = subprocess.run([str(binary), str(center_path), str(n),
                                 str(max_nodes), '18', '14', str(report)],
                                text=True, capture_output=True)
        require(report.exists(), f'chart {n} failed: {result.stderr[-500:]}')
        row = json.loads(report.read_text())
        require(row['chart'] == n and row['epsilon_bits'] == 18 and row['guard_radius_bits'] == 14, 'stale chart')
        require(result.returncode == 0 and row['status'] == 'SUBLEVEL_COVERED'
                and row['pending'] == 0 and row['unresolved'] == 0,
                f'INCOMPLETE chart {n}: {row}')
        return row

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        rows = list(executor.map(chart, range(32)))
    require({r['chart'] for r in rows} == set(range(32)), 'missing global chart')
    result = {'status': 'PASS',
              'claim_level': 'computational proof; analytic and implementation soundness not Lean-certified',
              'target': 'all unit-entry six-by-six Hadamard matrices H with column_l1(H-H0) <= 6*2^-24 (includes max-entry radius 2^-24)',
              'all_32_charts': True, 'covered_object': 'entire seed residual sublevel, not a sampled root list',
              'nodes': sum(r['nodes'] for r in rows), 'pending': 0, 'unresolved': 0,
              'graph': graph, 'rational_bounds': budget,
              'no_exact_root_count_asserted': True,
              'reused_concurrent_cpp_blob': 'aadd53bfcd9a32af059026dd1ebc999580bdf522',
              'reused_concurrent_commit': '648fc84fc92b66b952ba6e1c03d9b339c8ad3de8',
              'no_fixed_family_or_Jacobian_regularity_assumed': True,
              'lean_kernel_verified': False,
              'intrinsic_information_admission': 'not executed',
              'hashes': {'extension': old.digest(source),
                         'core': old.digest(source.with_name('check_real_x_global_cover.cpp')),
                         'driver': old.digest(Path(__file__)),
                         'fraction_interval_kernel': old.digest(Path(old.base.__file__)),
                         'parameter_generator': old.digest(Path(old.old.__file__)),
                         'original_driver': old.digest(Path(old.__file__)),
                         'certificate': old.digest(certificate),
                         'centers': old.digest(center_path)},
              'charts': rows}
    (output/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('certificate', type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--max-nodes', type=int, default=1200000)
    args = p.parse_args()
    try:
        result = run(args.certificate, args.output, args.jobs, args.max_nodes)
        print(json.dumps({k: v for k, v in result.items() if k != 'charts'}, indent=2))
    except Exception as exc:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output/'failure.json').write_text(json.dumps({'status': 'INCOMPLETE', 'reason': str(exc)}, indent=2)+'\n')
        raise
