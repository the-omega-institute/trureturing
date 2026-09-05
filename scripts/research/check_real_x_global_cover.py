#!/usr/bin/env python3
"""Exhaustive signed-Cayley coverage, followed by an independent graph replay.

This is a computational mathematical verifier, NOT Lean admission and NOT an
intrinsic-information score. Existing Fraction parameter/graph arithmetic is
reused. The accelerated cover core uses exact outward dyadic integer bounds;
floating-point linear algebra only proposes subsequently checked preconditioners.
"""
from __future__ import annotations

import argparse
import concurrent.futures
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import check_real_x_supergraph_patch as old

base = old.base
I, C = base.I, base.C
SCALE = 1 << 40
RADIUS = F(1, 1 << 16)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(data: dict, work: Path) -> tuple[Path, Path, list]:
    require(data['schema'] == 'x-uniform-supergraph-patch-v1', 'wrong schema')
    require(data['parameter_center'] == ['-1/5', '0'], 'wrong parameter centre')
    require(F(data['parameter_radius']) == F(1, 1 << 32), 'wrong parameter patch')
    require(len(data['center_numerators']) == len(data['chart_quarter_turns']) == 60,
            'the supplied proposal catalogue must have exactly 60 entries')
    old.cayley_identity()
    H = old.parameter_matrix([F(-1, 5), F(0)], F(1, 1 << 32))
    witnesses = old.squared_minor_separation(H)
    require(len(witnesses) == 30, 'missing Fourier seam witnesses')
    bounds = ['40']
    for row in H:
        for z in row:
            nums = []
            for x in (z.re, z.im):
                nums.extend([x.lo.numerator * SCALE // x.lo.denominator,
                             -((-x.hi.numerator * SCALE) // x.hi.denominator)])
            bounds.append(' '.join(map(str, nums)))
    bound_path = work / 'matrix_bounds.txt'
    bound_path.write_text('\n'.join(bounds) + '\n')
    centers = ['60']
    den = data['center_denominator']
    require(type(den) is int and den > 0, 'invalid centre denominator')
    for idx, (nums, chart) in enumerate(zip(data['center_numerators'],
                                          data['chart_quarter_turns'])):
        require(len(nums) == 5 and len(chart) == 6 and chart[0] == 0,
                'malformed proposed root')
        require(all(type(q) is int and 0 <= q < 4 for q in chart), 'bad phase chart')
        u = base.phase_map([I.point(F(n, den)) for n in nums], chart)
        mask = 0
        row = []
        for j, z in enumerate(u[1:]):
            require(z.re.lo == z.re.hi and z.im.lo == z.im.hi,
                    'proposed centre is not a rational point')
            s = -1 if z.re.lo < 0 else 1
            if s < 0:
                mask |= 1 << j
            t = s * z.im.lo / (1 + s * z.re.lo)
            require(-1 <= t <= 1, 'compact chart conversion failed')
            row.append(round(t * SCALE))
        centers.append(' '.join(map(str, [idx, mask, *row])))
    center_path = work / 'centers.txt'
    center_path.write_text('\n'.join(centers) + '\n')
    return center_path, bound_path, witnesses


def graph_audit(data: dict, enclosures: Path, centers: Path) -> dict:
    lines = enclosures.read_text().splitlines()
    require(len(lines) == 61 and lines[0] == '60', 'bad root enclosure catalogue')
    rays = {}
    for line in lines[1:]:
        x = list(map(int, line.split()))
        require(len(x) == 12, 'malformed root enclosure')
        idx, mask = x[:2]
        require(0 <= idx < 60 and idx not in rays and 0 <= mask < 32, 'bad label')
        ts = [I(F(x[2 + 2*j], SCALE), F(x[3 + 2*j], SCALE)) for j in range(5)]
        q = [0] + [2 * ((mask >> j) & 1) for j in range(5)]
        rays[idx] = base.phase_map(ts, q)
    boxes = {}
    for line in centers.read_text().splitlines()[1:]:
        x = list(map(int, line.split()))
        boxes[x[0]] = (x[1], [I(F(n, SCALE) - RADIUS, F(n, SCALE) + RADIUS)
                                for n in x[2:]])
    edges = {tuple(x) for x in data['allowed_edges']}
    canonical = set(data['canonical_vertices'])
    colors = data['noncanonical_colors']
    require(len(edges) == 114 and len(canonical) == 6 and len(colors) == 60,
            'malformed supergraph')
    require(all(0 <= i < j < 60 for i, j in edges), 'bad edge endpoints')
    require(all(colors[i] in (0, 1) for i in range(60) if i not in canonical),
            'bad bipartition')
    require(all((i in canonical and j in canonical) or
                (i not in canonical and j not in canonical and colors[i] != colors[j])
                for i, j in edges), 'forbidden supergraph edge')
    count = 0
    for i, j in itertools.combinations(range(60), 2):
        ip = sum((a.conj() * b for a, b in zip(rays[i], rays[j])), C.point()) / 6
        n = ip.normsq()
        require(n.hi < 1, f'rays {i},{j} are not certified distinct')
        if (i, j) not in edges:
            require(n.lo > F(1, 10**8), f'nonedge {i},{j} lacks positive margin')
            count += 1
    require(count == 1656, 'incomplete pair audit')
    for idx in canonical:
        v = rays[idx]
        w = [v[j] for j in (1, 2, 0, 4, 5, 3)]
        require(w[0].normsq().lo > 0, 'projective normalization singular')
        w = [z / w[0] for z in w]
        mask, X = boxes[idx]
        for j in range(5):
            z = w[j+1] * (-1 if (mask >> j) & 1 else 1)
            require((z + 1).normsq().lo > 0, 'inverse chart singular')
            t = C.point(0, -1) * (z - 1) / (z + 1)
            require(X[j].lo < t.re.lo <= t.re.hi < X[j].hi,
                    'shift image does not enter the same uniqueness box')
    return {'distinct_rays': 60, 'pair_tests': 1770, 'certified_nonedges': count,
            'nonedge_squared_modulus_lower_bound': '1/100000000',
            'canonical_vertices': sorted(canonical), 'canonical_shift_fixed': True,
            'noncanonical_supergraph_bipartite': True,
            'all_six_cliques_contained_in_canonical_set': True}


def run(certificate: Path, output: Path, jobs: int, max_nodes: int) -> dict:
    require(__debug__, 'the reused interval kernel requires assertions enabled')
    require(jobs > 0 and max_nodes > 0, 'invalid resource limits')
    output.mkdir(parents=True, exist_ok=True)
    data = json.loads(certificate.read_text())
    centers, bounds, witnesses = prepare(data, output)
    source = Path(__file__).with_suffix('.cpp')
    binary = output / 'cover_core'
    subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra', '-Werror',
                    str(source), '-o', str(binary)], check=True)

    def chart(mask: int) -> dict:
        report_path = output / f'chart_{mask:02d}.json'
        report_path.unlink(missing_ok=True)
        args = [str(binary), str(centers), str(mask), str(max_nodes),
                str(report_path), str(bounds)]
        if mask == 0:
            args.append(str(output / 'root_enclosures.txt'))
        result = subprocess.run(args, capture_output=True, text=True)
        require(result.returncode == 0, f'chart {mask} failed: {result.stderr}{result.stdout}')
        r = json.loads(report_path.read_text())
        require(r['chart'] == mask and r['status'] == 'COVERED' and
                r['unresolved'] == r['pending'] == 0, 'non-exhaustive chart result')
        return r

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        charts = list(executor.map(chart, range(32)))
    require([r['chart'] for r in charts] == list(range(32)), 'missing compact chart')
    graph = graph_audit(data, output / 'root_enclosures.txt', centers)
    report = {
        'status': 'PASS',
        'claim_level': 'computational proof subject to the documented analytic interpretation',
        'parameter_center': ['-1/5', '0'], 'parameter_radius': '1/4294967296',
        'all_32_compact_charts_covered': True,
        'global_root_count': 60,
        'at_most_one_complete_basis_up_to_phase_and_permutation': True,
        'no_four_MUB_with_this_fixed_edge_on_patch': True,
        'all_actual_completion_affinities': '2',
        'charts': charts, 'graph': graph, 'fourier_separation_witnesses': witnesses,
        'lean_kernel_verified': False,
        'intrinsic_information_admission': 'not executed; no score or gain asserted',
        'hashes': {'driver': digest(Path(__file__)), 'core': digest(source),
                   'existing_interval_kernel': digest(Path(base.__file__)),
                   'existing_parameter_generator': digest(Path(old.__file__)),
                   'input': digest(certificate), 'centers': digest(centers),
                   'parameter_bounds': digest(bounds),
                   'root_enclosures': digest(output / 'root_enclosures.txt')}}
    (output / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--max-nodes-per-chart', type=int, default=1_000_000)
    args = parser.parse_args()
    result = run(args.certificate, args.output, args.jobs, args.max_nodes_per_chart)
    print(json.dumps({k: v for k, v in result.items() if k not in ('charts', 'fourier_separation_witnesses')}, indent=2))
