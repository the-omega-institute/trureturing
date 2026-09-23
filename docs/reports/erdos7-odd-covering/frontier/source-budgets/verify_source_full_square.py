#!/usr/bin/env python3
"""Check a complete source-square certificate using exact integer arithmetic.

The source masses are first checked against the literal original AP masks.
The sparse feasible flow is then checked against every reconstructed graph
capacity. No optimization library, numerical status, or flow-search code is
used by this verifier. All checks remain active under Python -O.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import lcm
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
sys.dont_write_bytecode = True
FLOW = 'certificates/source_norms/source-budgets/source_full_square_flow.json'
WEIGHTED_FLOW = 'certificates/source_norms/source-budgets/source_full_square_r{}_flow.json'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable source module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def positive_integer(value, label):
    require(isinstance(value, (int, str)) and not isinstance(value, bool), label)
    answer = int(value)
    require(answer > 0 and str(answer) == str(value), label)
    return answer


def partition(src, prime, N, queries):
    axis = src.prefix_partition(prime, N, queries)
    require(sum(m for _, m, _ in axis) == prime**N, 'Complete original-coordinate partition')
    for a, r in queries:
        require(all(d >= a or (x-r) % prime**d for x, _, d in axis),
                'Every original and test indicator is constant on each partition leaf')
        require(sum(m for x, m, _ in axis if x % prime**a == r) == prime**(N-a),
                'Exact query Haar count')
    return axis


def literal_cylinders(src, family, law, choices):
    """Count actual source membership independently of the closed mass formula."""
    N = law.N
    require(len(family) == N*N+5*N, 'Complete actual original inventory')
    require(not any(c['exponents'][1] and c['exponents'][2] for c in family),
            'Original five and seven masks factor after fixing the three coordinate')
    queries = [{(c['exponents'][k], c['coordinate_residues'][k])
                for c in family if c['exponents'][k]} for k in range(3)]
    three = [(a, r) for a in range(N+1) for r in choices(a)]
    queries[0].update(three)
    queries[0].update((2, r) for r in range(9))
    for k in (1, 2):
        queries[k].update((a, 4) for a in range(1, N+1))
    axes = [partition(src, p, N, queries[k]) for k, p in enumerate((3, 5, 7))]
    counts = {(a, r, b, e): 0 for a, r in three for b, e in product(range(N+1), repeat=2)}
    r8 = {0: 11, 3: 10, 1: 8, 4: 8, 7: 8}
    for x, m3, _ in axes[0]:
        active = [c for c in family if x % 3**c['exponents'][0] == c['coordinate_residues'][0]]
        if any(not c['exponents'][1] and not c['exponents'][2] for c in active):
            continue
        require(x % 9 in r8, 'Literal pure-three source support')
        factor = r8[x % 9] if law.weighted else 1
        kept = []
        for k, p in ((1, 5), (2, 7)):
            forbidden = [(p**c['exponents'][k], c['coordinate_residues'][k])
                         for c in active if c['exponents'][k]]
            kept.append([sum(m for y, m, _ in axes[k]
                             if (a == 0 or y % p**a == 4)
                             and all(y % d != r for d, r in forbidden))
                         for a in range(N+1)])
        for a, r in three:
            if x % 3**a != r:
                continue
            for b, e in product(range(N+1), repeat=2):
                counts[a, r, b, e] += factor*m3*kept[0][b]*kept[1][e]
    total = counts[0, 0, 0, 0]
    require(total > 0 and law.haar_normalization == F(total, (8 if law.weighted else 1)*105**N),
            'Closed normalization equals the full actual surviving Haar integral')
    for key, count in counts.items():
        require(law.mass(*key) == F(count, total), 'Closed cylinder formula equals actual AP membership')
    three_masks = {(a, r): sum(1 << i for i, (x, _, _) in enumerate(axes[0]) if x % 3**a == r)
                   for a, r in three}
    for (a, r), (b, s) in product(three, repeat=2):
        expected = 0 if (r-s) % 3**min(a, b) else three_masks[(a, r) if a >= b else (b, s)]
        require(three_masks[a, r] & three_masks[b, s] == expected,
                'Every ternary pair intersection matches the actual partition masks')
    for k, p in ((1, 5), (2, 7)):
        masks = [sum(1 << i for i, (x, _, _) in enumerate(axes[k]) if a == 0 or x % p**a == 4)
                 for a in range(N+1)]
        require(all(masks[a] & masks[b] == masks[max(a, b)]
                    for a, b in product(range(N+1), repeat=2)), 'Nested clean-coordinate intersections')
    center = sum(F((2*a+1)*(2*b+1)*(2*e+1)*counts[a, 4 % 3**a, b, e], total)
                 for a, b, e in product(range(N+1), repeat=3))
    require(center == law.centered_square(), 'Complete centered square agrees with literal original masks')
    return center, tuple(map(len, axes))


def verify(base, io, src, family, certificate=None, fixed_residue=None):
    formula = module('complete_square_source', base/'frontier/source-budgets/source_full_square.py')
    anchored = fixed_residue is not None
    path = WEIGHTED_FLOW.format(fixed_residue) if anchored else FLOW
    cert_bytes = io.read_artifact_bytes(certificate or base/path)
    cert = json.loads(cert_bytes, object_pairs_hook=io._unique)
    fields = {'N', 'h', 'weighted', 'denominator', 'value', 'flows'}
    if anchored:
        fields.update(('fixed_label', 'fixed_residue'))
    require(isinstance(cert, dict) and set(cert) == fields,
            'Exact sparse-flow certificate fields')
    require(type(cert['N']) is int and type(cert['h']) is int and type(cert['weighted']) is bool,
            'Typed source parameters')
    N = cert['N']
    require(N >= 4 and cert['h'] == N, 'Complete source period in the proved compression range')
    require(cert['weighted'] == anchored, 'Declared plain or weighted certificate law')
    anchor = (2, 0, 0)
    if anchored:
        require(cert['fixed_label'] == list(anchor) and all(type(v) is int for v in cert['fixed_label']),
                'Only the pure9 test label is fixed; the source law is unchanged')
        require(type(cert['fixed_residue']) is int and cert['fixed_residue'] == fixed_residue
                and fixed_residue in formula.choices(2), 'Canonical fixed pure9 test residue')
    D = positive_integer(cert['denominator'], 'Positive exact capacity scale')
    value = positive_integer(cert['value'], 'Positive exact flow value')
    law = formula.CompressedSource(N, cert['weighted'])
    complete_center, partitions = literal_cylinders(src, family, law, formula.choices)
    labels = [v for v in product(range(1, N+1), range(N+1), range(N+1))
              if not anchored or v != anchor]
    start, end = len(labels), len(labels)+1
    balance = [0]*(end+1)
    pending = {}
    require(isinstance(cert['flows'], list), 'Sparse flow array')
    for row in cert['flows']:
        require(isinstance(row, list) and len(row) == 3, 'Sparse flow triple')
        u, v, raw = row
        require(type(u) is int and type(v) is int and 0 <= u <= end and 0 <= v <= end and u != v,
                'Valid distinct flow endpoints')
        flow = positive_integer(raw, 'Strictly positive sparse flow')
        require((u, v) not in pending, 'Unique original edge per sparse flow')
        pending[u, v] = flow
        balance[u] += flow
        balance[v] -= flow
    sparse_count = len(pending)
    raw_masses = {(a, r, b, e): law.mass(a, r, b, e)
                  for a, b, e in product(range(N+1), repeat=3) for r in formula.choices(a)}
    mass_scale = lcm(D, *(x.denominator for x in raw_masses.values()))
    scale_ratio = mass_scale//D
    masses = {}
    for key, probability in raw_masses.items():
        scaled = probability*mass_scale
        require(scaled.denominator == 1 and scaled >= 0, 'Exact nonnegative cylinder units')
        masses[key] = scaled.numerator
    require(masses[0, 0, 0, 0] == mass_scale, 'Actual source is normalized')
    good, bad = {0: 0}, {}
    for a in range(1, N+1):
        roots = formula.choices(a)
        target = [r for r in roots if r % 3 == 1]
        other = [r for r in roots if r % 3 == 0]
        require(len(target) == 1 and len(other)+1 == len(roots), 'Complete good/bad partition')
        require(target[0] == 4 % 3**a, 'Good choices are exactly the centered4 layout')
        good[a], bad[a] = target[0], other
    powers = [3**a for a in range(N+1)]

    def intersection(left, r, right, s):
        a, b, e = left
        aa, bb, ee = right
        if (r-s) % powers[min(a, aa)]:
            return 0
        return masses[max(a, aa), r if a >= aa else s, max(b, bb), max(e, ee)]

    def unary(label, residue):
        a, b, e = label
        original = masses[a, residue, b, e]+2*sum(
            masses[a, residue, max(b, bb), max(e, ee)]
            for bb, ee in product(range(N+1), repeat=2))
        return original+(2*intersection(label, residue, anchor, fixed_residue) if anchored else 0)

    # L_c = L_4 + I_(9,c) - I_(9,4) on the SAME full source probability law.
    baseline_shift = F(0)
    if anchored:
        cross = 2*sum(intersection(v, good[v[0]], anchor, fixed_residue)
                      - intersection(v, good[v[0]], anchor, 4)
                      for v in product(range(N+1), repeat=3))
        difference_square = (masses[2, fixed_residue, 0, 0]+masses[2, 4, 0, 0]
                             - 2*intersection(anchor, fixed_residue, anchor, 4))
        baseline_shift = F(cross+difference_square, mass_scale)

    # Twice the unary gain plus all (bad/bad - good/good) pair scores.
    d = [2*(max(unary(label, r) for r in bad[label[0]])-unary(label, good[label[0]]))
         for label in labels]
    original_edges = 0

    def verify_edge(u, v, cap):
        nonlocal original_edges
        require(type(cap) is int and cap >= 0, 'Exact nonnegative graph capacity')
        require(cap % scale_ratio == 0, 'Graph capacity integral at the certificate scale')
        cap //= scale_ratio
        flow = pending.pop((u, v), 0)
        require(flow <= cap, 'Sparse flow respects the reconstructed capacity')
        require(cap > 0 or flow == 0, 'No flow on an omitted zero-capacity edge')
        original_edges += cap > 0

    pair_blocks = 0
    for i, left in enumerate(labels):
        a = left[0]
        for j in range(i+1, len(labels)):
            right = labels[j]
            aa = right[0]
            G = 2*intersection(left, good[a], right, good[aa])
            B = 2*max(intersection(left, r, right, s) for r in bad[a] for s in bad[aa])
            require(G >= 0 and B >= 0, 'Nonnegative exact pair scores')
            d[i] += B-G
            d[j] += B-G
            verify_edge(i, j, G+B)
            verify_edge(j, i, G+B)
            pair_blocks += 1
    required = 0
    for i, amount in enumerate(d):
        if amount > 0:
            verify_edge(start, i, amount)
            require(amount % scale_ratio == 0, 'Exact source capacity scaling')
            required += amount//scale_ratio
        elif amount < 0:
            verify_edge(i, end, -amount)
    require(not pending, 'Every positive sparse flow belongs to an actual original edge')
    require(balance == [value if i == start else -value if i == end else 0 for i in range(end+1)],
            'Flow conserved at every middle vertex, with the stated source/sink value')
    require(value <= required, 'Feasible flow does not exceed total source capacity')
    gain_upper = F(required-value, 2*D)
    require(baseline_shift+gain_upper <= 0, 'This entire layout branch lies below the original centered square')
    result = dict(N=N, h=N, weighted=law.weighted, free_labels=len(labels), pair_blocks=pair_blocks,
                original_directed_edges=original_edges, sparse_nonzero_flows=sparse_count,
                canonical_cylinders=len(masses), partition_leaves=partitions,
                checked_vertices=len(balance), denominator=str(D), cylinder_scale=str(mass_scale),
                required=str(required), verified_flow=str(value), max_gain_upper=str(gain_upper),
                complete_centered4_value=str(complete_center), flow_sha256=sha256(cert_bytes).hexdigest())
    if anchored:
        result.update(fixed_label=anchor, fixed_residue=fixed_residue,
                      baseline_shift=str(baseline_shift), branch_upper=str(complete_center+baseline_shift+gain_upper),
                      upper_minus_center=str(baseline_shift+gain_upper),
                      scope='One fixed pure9 test branch on the same complete weighted source law. '
                            'All three canonical branches are required for a global maximum.')
    else:
        result.update(complete_actual_gamma=str(complete_center),
                      scope='Exact complete plain-source maximum, attained by centered4. '
                            'Ordinary compression and integer-flow proof; no new Lean theorem.')
    return result


def verify_all(base, io, src, family):
    plain = verify(base, io, src, family)
    branches = [verify(base, io, src, family, fixed_residue=r) for r in (0, 3, 4)]
    require(plain['N'] == 12 and all(row['N'] == 12 for row in branches), 'Declared complete F12 sources')
    center = branches[0]['complete_centered4_value']
    require(all(row['complete_centered4_value'] == center for row in branches), 'Same weighted reference law')
    require({row['fixed_residue'] for row in branches} == {0, 3, 4}, 'All canonical pure9 choices covered')
    require(max(F(row['branch_upper']) for row in branches) == F(center), 'Matching global upper and actual lower')
    return dict(plain=plain, weighted=dict(N=12, h=12, weighted=True, branches=branches,
                complete_actual_gamma=center,
                scope='Exact complete weighted F12 maximum, attained by centered4, from all three pure9 test branches. '
                      'No probability conditioning, other-height or unrestricted covering conclusion.'))


def self_test(base, io, src, family):
    """Reject false full-value witnesses that defeat different proof hypotheses."""
    cert = json.loads(io.read_artifact_bytes(base/FLOW), object_pairs_hook=io._unique)
    N = cert['N']
    start, end = N*(N+1)**2, N*(N+1)**2+1
    first = next(v for u, v, _ in cert['flows'] if u == start)
    last = next(u for u, v, _ in cert['flows'] if v == end)
    require(first != last, 'Distinct positive and negative unary vertices')
    value = cert['value']
    cases = (
        ('capacity', [[start, first, value], [first, last, value], [last, end, value]],
         'Sparse flow respects the reconstructed capacity'),
        ('unknown-edge', [[start, end, value]], 'Every positive sparse flow belongs to an actual original edge'),
        ('conservation', cert['flows'][1:], 'Flow conserved at every middle vertex'))
    with TemporaryDirectory(prefix='source-square-refutations-') as temporary:
        path = Path(temporary)/'false-flow.json'
        for name, flows, expected in cases:
            wrong = dict(cert, flows=flows)
            path.write_text(json.dumps(wrong))
            rejected = False
            try:
                verify(base, io, src, family, path)
            except ValueError as error:
                require(expected in str(error), 'Named false proof rejected for its intended violated hypothesis')
                rejected = True
            require(rejected, 'False complete-square certificate was accepted: '+name)
    return dict(rejected_false_proofs=[name for name, _, _ in cases])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--fixed-residue', type=int, choices=(0, 3, 4))
    parser.add_argument('--all', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    io = module('complete_square_io', args.base/'certificate_io.py')
    src = module('complete_square_original', args.base/'frontier/source-budgets/irredundant_whole_j_finite_source.py')
    sharp = module('complete_square_family', args.base/'frontier/source-budgets/source_mean_sharpness.py')
    require(not args.all or args.certificate is None and args.fixed_residue is None,
            'Complete verification uses the canonical four certificates')
    require(not args.self_test or not args.all and args.certificate is None and args.fixed_residue is None,
            'False-proof checks use the canonical plain certificate')
    path = FLOW if args.fixed_residue is None else WEIGHTED_FLOW.format(args.fixed_residue)
    cert = json.loads(io.read_artifact_bytes(args.certificate or args.base/path), object_pairs_hook=io._unique)
    require(type(cert['N']) is int and cert['N'] >= 4, 'Declared source height')
    family, _, _ = sharp.original_source(src, cert['N'])
    result = self_test(args.base, io, src, family) if args.self_test else (
        verify_all(args.base, io, src, family) if args.all else verify(
            args.base, io, src, family, args.certificate, args.fixed_residue))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
