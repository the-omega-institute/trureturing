#!/usr/bin/env python3
"""Exact full-domain killed maximum for the pinned actual zero-block fixtures.

The first-exit normal form and branch-bound soundness are proved in marked_head_profile.md (RS1 and its finite optimization).
No external optimizer is used. Every rational/integer check remains active -O.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from math import lcm, prod
from hashlib import sha256
from pathlib import Path
import argparse, json

HERE = Path(__file__).resolve().parent
SOURCE_PINS = {
    'certificates/actual_zero_block_certificate.json': 'c6cb9ea79f78fdc40ad3da66d7dffa96b952195fbb57848792fdbccf7a04b0ce',
    'verify_actual_zero_block.py': '48023c2fd67f7b385c9f0e8c62decc146a91ea3f52d74e014e464db43ee785b5',
}

def need(ok, message):
    if not ok:
        raise ArithmeticError(message)

def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result

def solve(p, source):
    P = [F(1, 2)] + [F(1, 3**j) for j in range(1, 8)] + [F(1, 4374)]
    t = [1 / (1 - min(F(j, p - 1), F(7, p - 2))) / (p - 1) for j in range(9)]
    q = [1 - max(F(0), F(j, p - 1) - F(7, p - 2)) / (1 - F(7, p - 2)) for j in range(9)]
    labels = [(typ, d) for typ in (0, 1) for d in range(1, 9)]

    def cylinder(w, d, r):
        if r == 0:
            return sum(P[j] * w[j] for j in range(d, 9))
        return w[r - 1] / (2 * 3**(d - 1))

    unary, pair = [], {}
    for typ, d in labels:
        w = [3 * a + 2 * b if typ == 0 else 5 * b for a, b in zip(q, t)]
        unary.append([cylinder(w, d, r) for r in range(d + 1)])
    for i, (a, d) in enumerate(labels):
        for j, (b, e) in enumerate(labels[:i]):
            matrix, w = [], q if a == b == 0 else t
            for r in range(d + 1):
                row = []
                for s in range(e + 1):
                    nr = 1 if r == 0 else 1 + 3**(r - 1)
                    ns = 1 if s == 0 else 1 + 3**(s - 1)
                    if (nr - ns) % 3**min(d, e):
                        value = F(0)
                    else:
                        value = cylinder(w, d, r) if d >= e else cylinder(w, e, s)
                    row.append(2 * value)
                matrix.append(row)
            pair[i, j] = matrix
    fractions = [v for row in unary for v in row] + [v for matrix in pair.values() for row in matrix for v in row]
    scale = lcm(*(v.denominator for v in fractions))
    need(all((v * scale).denominator == 1 for v in fractions), 'integer objective scale')
    unary = [[int(v * scale) for v in row] for row in unary]
    pair = {ij: [[int(v * scale) for v in row] for row in matrix] for ij, matrix in pair.items()}
    for (i, j), matrix in list(pair.items()):
        pair[j, i] = list(map(list, zip(*matrix)))
    pcaps = {ij: max(v for row in matrix for v in row) for ij, matrix in pair.items()}
    bestx = [0] * 7 + [8] + [0] * 7 + [8]
    best = sum(unary[i][r] for i, r in enumerate(bestx)) + sum(pair[i, j][bestx[i]][bestx[j]] for i in range(16) for j in range(i))
    initialbest = best
    nodes = pruned = maxdepth = covered = trace_events = 0
    trace = sha256()

    def event(value):
        nonlocal trace_events
        trace_events += 1
        trace.update((json.dumps(value, separators=(',', ':')) + '\n').encode())

    def visit(ids, adj, current, x):
        nonlocal nodes, pruned, best, bestx, maxdepth, covered
        nodes += 1
        maxdepth = max(maxdepth, 16 - len(ids))
        completions = prod(len(unary[i]) for i in ids)
        event(['enter', x, current, best, completions])
        if not ids:
            covered += 1
            if current > best:
                best, bestx = current, x[:]
            event(['leaf', current])
            return
        pc = sum(pcaps[i, j] for a, i in enumerate(ids) for j in ids[:a])
        upper = current + sum(max(adj[i]) for i in ids) + pc
        event(['bound', upper])
        if upper <= best:
            pruned += 1
            covered += completions
            event(['prune-whole', completions])
            return
        chosen = branches = None
        for i in ids:
            rest = [j for j in ids if j != i]
            restpc = pc - sum(pcaps[i, j] for j in rest)
            possible, bounds = [], []
            for r, ur in enumerate(adj[i]):
                bound = current + ur + restpc + sum(max(uj + v for uj, v in zip(adj[j], pair[i, j][r])) for j in rest)
                bounds.append(bound)
                if bound > best:
                    possible.append((bound, r))
            event(['conditioned-bounds', i, bounds])
            if not possible:
                pruned += 1
                covered += completions
                event(['prune-all-choices', i, completions])
                return
            if branches is None or len(possible) < len(branches):
                chosen, branches = i, possible
        i = chosen
        rest = [j for j in ids if j != i]
        each_count = prod(len(unary[j]) for j in rest)
        excluded = len(unary[i]) - len(branches)
        covered += excluded * each_count
        event(['split', i, branches, excluded * each_count])
        for upper, r in sorted(branches, reverse=True):
            if upper <= best:
                covered += each_count
                event(['prune-choice', i, r, upper, each_count])
                continue
            nxt = {j: [uj + v for uj, v in zip(adj[j], pair[i, j][r])] for j in rest}
            xx = x[:]
            xx[i] = r
            visit(rest, nxt, current + adj[i][r], xx)

    domain = prod(len(row) for row in unary)
    visit(list(range(16)), {i: row[:] for i, row in enumerate(unary)}, 0, [-1] * 16)
    need(covered == domain, 'the disjoint branch/prune partition covers the entire normal-form domain')
    need(best == initialbest, 'the literal spur candidate is globally optimal')
    baseline = sum(P[j] * (q[j] + 3 * t[j]) for j in range(9))
    S = F(273, 64)
    exact = S * (baseline + F(best, scale))
    G3 = sum(P[j] * (j + 1)**2 for j in range(9))
    b = P[8] / (p - 1)
    Jt = sum(P[j] * t[j] * (j + 1)**2 for j in range(9))
    split = S * (G3 - b + 3 * Jt)
    deltas = [sum(P[j] * (t[j] - t[a - 1]) for j in range(a, 9)) for a in range(1, 9)]
    need(all(delta > 0 for delta in deltas), 'strict radial increments')
    general_gap = S * sum((2 * a + 1) * min(b, deltas[a - 1]) for a in range(1, 9))
    row = next(row for row in source['rows'] if row['prime'] == p)
    need(exact == F(row['killed_square_lower']), 'exact maximum equals the pinned literal lower witness')
    need(exact < F(row['killed_square_upper']), 'new maximum strictly tightens the old bracket')
    need(split - general_gap == F(row['killed_square_upper']), 'general radial separation specializes to the pinned upper bound')
    need(b == F(row['assigned_bad_mass']) and 3 * S * Jt == F(row['positive_current_frontier_exact']), 'same actual law and positive frontier')
    G = S * G3
    H = F(source['source']['centered_test_square_hinge81'])
    baseline_gap = (273 - S) * b
    xi_gap = 3 * S * 17 * P[8] * (t[8] - t[7])
    need(baseline_gap + xi_gap == split - exact, 'same-test split supremum loss decomposition')
    deleted_positive = F(12849, 64) * b
    retained_negative = H - G + 81 - F(561, 64) * b
    need(retained_negative > F(165, 8) and deleted_positive > 0, 'additional strict same-test hinge losses')
    return {
        'prime': p, 'original_test_labels': row['test_label_count'],
        'normal_form_labels': labels, 'normal_form_domain_product': domain,
        'integer_scale': scale, 'candidate_objective_integer': initialbest,
        'optimal_objective_integer': best, 'maximizer': bestx,
        'nodes': nodes, 'whole_node_prunes': pruned, 'maxdepth': maxdepth,
        'covered_completions': covered, 'trace_events': trace_events, 'trace_sha256': trace.hexdigest(),
        'killed_max_exact': str(exact), 'split_killed_baseline_plus_Xi': str(split),
        'split_sup_gap_exact': str(split - exact), 'Gamma_q_exact': str(S * (G3 - b)),
        'Xi_exact': str(3 * S * Jt), 'general_radial_split_gap_lower': str(general_gap),
        'radial_delta_by_depth': [str(delta) for delta in deltas],
        'split_baseline_gap_at_maximizer': str(baseline_gap),
        'split_Xi_gap_at_maximizer': str(xi_gap),
        'hinge81_at_maximizer': str(H),
        'deleted_positive_hinge81_at_maximizer': str(deleted_positive),
        'retained_negative_hinge81_at_maximizer': str(retained_negative),
    }

def compute(source_root):
    for name, pin in SOURCE_PINS.items():
        need(sha256(read_artifact_bytes(source_root / name)).hexdigest() == pin, 'pinned prerequisite: ' + name)
    source = json.loads(read_artifact_text(source_root / 'certificates/actual_zero_block_certificate.json'), object_pairs_hook=unique)
    rows = [solve(p, source) for p in (17, 19)]
    factor = F(source['p19_with_explicit_physical17_history']['factor'])
    extension = {
        'original_test_labels': 576, 'physical17_mixed_charge': '0', 'factor': str(factor),
        'killed_max_exact': str(factor * F(rows[1]['killed_max_exact'])),
        'split_sup_gap_exact': str(factor * F(rows[1]['split_sup_gap_exact'])),
    }
    return {
        'schema': 'actual-first-exit-killed-maximum-v1', 'source_pins': SOURCE_PINS,
        'rows': rows, 'p19_with_explicit_physical17_history': extension,
        'scope': 'Exact complete-test maxima for the two pinned actual finite families, plus the zero-mixed-charge physical17 extension. All original labels remain independent. This does not give a universal KC frontier bound or permit adding the separate positive17 and19 fixtures as one chain.',
    }

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=HERE)
    parser.add_argument('--certificate', type=Path, default=HERE / 'certificates/actual_radial_maximum_certificate.json')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = compute(args.source_root)
    # Normalize tuples identically on write and compare.
    result = json.loads(json.dumps(result))
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2) + '\n')
    else:
        need(json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique) == result, 'complete deterministic certificate match')
    print('PASS exact killed maxima, all normal-form choices, both split-sup gaps and same-test hinge losses')
