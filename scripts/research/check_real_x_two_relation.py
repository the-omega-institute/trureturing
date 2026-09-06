#!/usr/bin/env python3
"""Check a broad-tube, two-relation MUB certificate; optionally replay all charts.

No stored success verdict is consumed. The graph is reconstructed from exact
whole-tube Fraction intervals. All first six-cliques are enumerated and compared
with the certificate, then every common-partner graph is checked five-colorable.
A full run independently invokes the shared sublevel-cover engine on all charts.
This is computational verification, not Lean-kernel admission.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
import subprocess

import check_real_x_ambient_exclusion as prior

I, C = prior.I, prior.C
N = 60
SCALE = 1 << 40
RADIUS_BITS = 5
TAU_BITS = 11
EPSILON_BITS = 8
TAU = F(1, 1 << TAU_BITS)
ORTH = TAU * TAU
MU = F(3, 4)
SIGMA = F(6, 1 << 14)
EPSILON = F(1, 1 << EPSILON_BITS)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vertices(mask: int):
    while mask:
        bit = mask & -mask
        mask -= bit
        yield bit.bit_length() - 1


def enumerate_six_cliques(adjacency: list[int]) -> list[tuple[int, ...]]:
    """Increasing DFS, maintaining common adjacency to every chosen vertex."""
    out = []
    def visit(candidates: int, chosen: tuple[int, ...]) -> None:
        if len(chosen) == 6:
            out.append(chosen)
            return
        if len(chosen) + candidates.bit_count() < 6:
            return
        while candidates:
            bit = candidates & -candidates
            candidates -= bit
            v = bit.bit_length() - 1
            visit(candidates & adjacency[v], chosen + (v,))
    visit((1 << N) - 1, ())
    return out


def tube_relations(center_path: Path) -> dict:
    require(__debug__, 'Python -O is not permitted by the reused interval implementation')
    lines = center_path.read_text().splitlines()
    require(len(lines) == N + 1 and lines[0] == str(N), 'incomplete tube centers')
    rays = {}
    radius = F(1, 1 << RADIUS_BITS)
    for line in lines[1:]:
        row = list(map(int, line.split()))
        require(len(row) == 7, 'bad center row')
        label, mask, *nums = row
        require(0 <= label < N and label not in rays and 0 <= mask < 32,
                'invalid or duplicated label')
        t = [I(F(n, SCALE) - radius, F(n, SCALE) + radius) for n in nums]
        chart = [0] + [2 * ((mask >> j) & 1) for j in range(5)]
        # Reuse the original Cayley evaluator and its outward endpoint rounding.
        rays[label] = [C(prior.old.old.rnd(z.re, 60), prior.old.old.rnd(z.im, 60))
                       for z in prior.old.base.phase_map(t, chart)]
    require(set(rays) == set(range(N)), 'missing label')
    A, B = [0] * N, [0] * N
    bounds = []
    same_lower = F(1)
    for i, j in itertools.combinations_with_replacement(range(N), 2):
        z = sum((a.conj() * b for a, b in zip(rays[i], rays[j])), C.point()) / 6
        q = z.normsq()
        bounds.append([i, j, str(q.lo), str(q.hi)])
        if i == j:
            # Independent interval occurrences cover ANY pair in the same tube.
            same_lower = min(same_lower, q.lo)
            require(q.lo > MU, f'same-tube separation failed at {i}')
        elif q.lo < ORTH:
            A[i] |= 1 << j
            A[j] |= 1 << i
        if q.lo <= F(1, 6) + TAU and q.hi >= F(1, 6) - TAU:
            B[i] |= 1 << j
            B[j] |= 1 << i
    require(ORTH < MU and all((A[i] >> i) & 1 == 0 for i in range(N)),
            'invalid injection/orthogonality threshold')
    return {'A': A, 'B': B, 'bounds': bounds, 'same_lower': str(same_lower)}


def audit_finite(cert: dict, data: dict) -> dict:
    schema = cert.get('schema')
    require(schema in ('mub-two-relation-tube-certificate-v1',
                       'mub-two-relation-partner-cover-v2'), 'unknown schema')
    require(cert.get('radius_bits') == RADIUS_BITS and cert.get('tau_bits') == TAU_BITS,
            'certificate threshold/radius mismatch')
    require(F(cert['orthogonality_threshold']) == ORTH and
            F(cert['unbiased_tolerance']) == TAU, 'inconsistent numeric thresholds')
    A, B = data['A'], data['B']
    require(cert['orthogonality_masks'] == A and cert['unbiased_masks'] == B,
            'stored relations differ from independently re-evaluated whole tubes')
    require(F(data['same_lower']) > MU, 'same-tube bound not established')
    expected = set(enumerate_six_cliques(A))
    max_partners = 0
    covers = []
    if schema.endswith('v2'):
        for item in cert['partner_covers']:
            vs, cs = item['vertices'], item['colors']
            require(all(type(v) is int and 0 <= v < N for v in vs)
                    and vs == sorted(set(vs)) and len(cs) == len(vs), 'bad cover domain')
            require(all(type(c) is int and 0 <= c < 5 for c in cs), 'invalid color')
            color = dict(zip(vs, cs))
            require(all(not ((A[v] >> w) & 1) or color[v] != color[w]
                        for v, w in itertools.combinations(vs, 2)), 'cover color collision')
            covers.append(sum(1 << v for v in vs))
        for clique in expected:
            common = (1 << N) - 1
            for v in clique:
                common &= B[v]
            require(any(common & ~cover == 0 for cover in covers), 'uncovered partner set')
            max_partners = max(max_partners, common.bit_count())
    else:
        seen = set()
        for item in cert['first_clique_certificates']:
            raw = item['first_clique']
            require(all(type(i) is int and 0 <= i < N for i in raw)
                    and len(raw) == 6 and raw == sorted(set(raw)), 'bad first clique')
            clique = tuple(raw)
            require(clique in expected and clique not in seen, 'invalid or duplicate first clique')
            seen.add(clique)
            common = (1 << N) - 1
            for v in clique:
                common &= B[v]
            partner = list(vertices(common))
            require(item['partner_vertices'] == partner, 'incorrect partner set')
            raw_color = item['five_colors']
            require(set(raw_color) == {str(v) for v in partner}, 'wrong color domain')
            color = {v: raw_color[str(v)] for v in partner}
            require(all(type(c) is int and 0 <= c < 5 for c in color.values()), 'bad color')
            require(all(not ((A[v] >> w) & 1) or color[v] != color[w]
                        for v, w in itertools.combinations(partner, 2)), 'color collision')
            max_partners = max(max_partners, len(partner))
        require(seen == expected, 'nonexhaustive first-clique certificate')
    require(cert['complete_first_clique_count'] == len(expected), 'wrong clique count')
    require(TAU <= F(1, 4) and TAU + SIGMA * (5 + SIGMA) < EPSILON,
            'residual transfer budget exhausted')
    return {
        'status': 'FINITE_CERTIFICATE_VERIFIED',
        'whole_tube_pair_checks_including_diagonal': len(data['bounds']),
        'orthogonality_supergraph_edges': sum(x.bit_count() for x in A) // 2,
        'unbiased_supergraph_edges': sum(x.bit_count() for x in B) // 2,
        'first_six_cliques': len(expected),
        'all_common_partner_graphs_five_colorable': True,
        'largest_common_partner_set': max_partners,
        'same_tube_overlap_strict_lower': str(MU),
        'tube_radius': str(F(1, 1 << RADIUS_BITS)),
        'seed_sublevel': str(EPSILON),
        'candidate_residual_tolerance': str(TAU),
        'column_l1_radius': str(SIGMA),
        'entrywise_radius': str(SIGMA / 6),
        'transferred_seed_residual_upper': str(TAU + SIGMA * (5 + SIGMA)),
        'candidate_energy_gap_conditional_on_full_cover': str(ORTH),
        'global_cover_replayed': False,
        'lean_kernel_verified': False,
    }


def audit_chart_reports(reports: list[dict]) -> dict:
    require(len(reports) == 32 and {r.get('chart') for r in reports} == set(range(32)),
            'all 32 charts must be covered exactly once')
    for r in reports:
        require(r.get('status') == 'SUBLEVEL_COVERED' and r.get('pending') == 0 and
                r.get('unresolved') == 0, 'incomplete global cover')
        require(r.get('epsilon_bits') == EPSILON_BITS and
                r.get('guard_radius_bits') == RADIUS_BITS and r.get('dyadic_bits') == 40,
                'coverage parameters differ from graph tubes')
        require(r.get('tube_uniqueness_checked') is False and
                r.get('max_guard_contraction_dyadic') is None,
                'unexpected raw-tube verification semantics')
    return {'charts': 32, 'nodes': sum(r['nodes'] for r in reports),
            'pending': 0, 'unresolved': 0, 'tube_uniqueness_used': False}


def run(certpath: Path, centers: Path, output: Path, full_cover: bool,
        jobs: int, cap: int) -> dict:
    require(1 <= jobs <= 32 and cap > 0, 'invalid resource budget')
    output.mkdir(parents=True, exist_ok=True)
    for name in ('verification.json', 'failure.json'):
        (output / name).unlink(missing_ok=True)
    data = tube_relations(centers)
    result = audit_finite(json.loads(certpath.read_text()), data)
    (output / 'overlap_intervals.json').write_text(json.dumps(data['bounds'], indent=2) + '\n')
    scriptdir = Path(__file__).resolve().parent
    result['sha256'] = {str(p.name): digest(p) for p in
                       (Path(__file__).resolve(), certpath, centers,
                        scriptdir / 'check_real_x_residual_barrier.cpp',
                        scriptdir / 'check_real_x_global_cover.cpp',
                        scriptdir / 'check_strict_x_counterexample.py')}
    if full_cover:
        source = scriptdir / 'check_real_x_residual_barrier.cpp'
        binary = (output / 'sublevel_checker').resolve()
        subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra',
                        str(source), '-o', str(binary)], check=True)
        def chart(k: int) -> dict:
            report = (output / f'chart_{k:02d}.json').resolve()
            report.unlink(missing_ok=True)
            subprocess.run([str(binary), str(centers.resolve()), str(k), str(cap),
                            str(EPSILON_BITS), str(RADIUS_BITS), str(report),
                            '--raw-tube-cover'], check=True, stdout=subprocess.DEVNULL)
            return json.loads(report.read_text())
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            reports = list(pool.map(chart, range(32)))
        result['coverage'] = audit_chart_reports(reports)
        result['global_cover_replayed'] = True
        result['status'] = 'COMPUTATIONAL_EXCLUSION_VERIFIED'
        result['claim'] = ('For unit-entry U,V and H within the stated column-l1 ball, '
                           'the specified two-frame merit is at least 2^-22. '
                           'The analytic interval interpretation and implementation '
                           'remain outside Lean kernel verification.')
    (output / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    p.add_argument('--centers', type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--full-cover', action='store_true')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--max-nodes', type=int, default=1200000)
    args = p.parse_args()
    centers = args.centers or args.certificate.with_name('centers.txt')
    try:
        result = run(args.certificate, centers, args.output, args.full_cover,
                     args.jobs, args.max_nodes)
    except Exception as exc:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / 'verification.json').unlink(missing_ok=True)
        (args.output / 'failure.json').write_text(json.dumps({'status': 'FAIL', 'error': str(exc)})+'\n')
        raise
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
