#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Exact finite inputs/results consumed by the stable relation boundary volume.

Only Python's standard library is used. Generate with --output PATH; compare
the entire canonical byte stream with --check PATH. No floating arithmetic,
randomness, repository mutation outside --output, or external dispatch.
The explicit inputs are reconstructed examples, not recovered attachments.
"""

import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


SET = (
    (0, 0, 0, 0), (1, 0, 0, 0), (-1, 0, 0, 0),
    (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1),
    (1, 1, 0, 0), (1, 0, 1, 0), (1, 0, 0, 1),
    (2, -1, 3, -2),
)
ONE = (1, 0, 0, 0)
A = (0, 1, 0, 0)
B = (0, 0, 1, 0)
R = ((0, 0, -1), (1, 0, 0), (0, -1, 0))
IDENTITY = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def qmul(x, y):
    a, u, v, w = x
    b, r, s, t = y
    return (a*b-u*r-v*s-w*t,
            a*r+b*u+v*t-w*s,
            a*s+b*v+w*r-u*t,
            a*t+b*w+u*s-v*r)


def norm(x):
    return sum(t*t for t in x)


def conj(x):
    return (x[0], -x[1], -x[2], -x[3])


def readout(word):
    q = ONE
    for letter in word:
        require(letter in 'ab', 'word alphabet')
        q = qmul(q, A if letter == 'a' else B)
    return q


def substitute(word):
    return ''.join('b' if letter == 'a' else 'ba' for letter in word)


def rq(q):
    s, x, y, z = q
    return (s, -z, x, -y)


# A second arithmetic realization: exact Gaussian-integer 2x2 matrices.
# Each scalar is (real, imaginary), never Python's floating complex type.
def gadd(x, y):
    return (x[0]+y[0], x[1]+y[1])


def gmul(x, y):
    return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])


def phi(q):
    s, x, y, z = q
    return (((s, -z), (-y, -x)), ((y, -x), (s, z)))


def gaussian_matmul(x, y):
    return tuple(tuple(gadd(gmul(x[i][0], y[0][j]),
                           gmul(x[i][1], y[1][j]))
                       for j in range(2)) for i in range(2))


def gaussian_det(m):
    a = gmul(m[0][0], m[1][1])
    b = gmul(m[0][1], m[1][0])
    return (a[0]-b[0], a[1]-b[1])


def matmul(x, y):
    return tuple(tuple(sum(x[i][k]*y[k][j] for k in range(len(y)))
                       for j in range(len(y[0]))) for i in range(len(x)))


def transpose(x):
    return tuple(zip(*x))


def det3(m):
    return sum(m[0][i]*(m[1][(i+1) % 3]*m[2][(i+2) % 3]
                       - m[1][(i+2) % 3]*m[2][(i+1) % 3])
               for i in range(3))


def epsilon(t):
    if len(set(t)) != 3:
        return 0
    return (-1) ** sum(t[i] > t[j] for i in range(3) for j in range(i+1, 3))


def quarter_turns(d):
    for p in range(d):
        for q in range(p+1, d):
            target = list(range(d))
            sign = [1]*d
            target[p], target[q], sign[q] = q, p, -1
            yield {'plane': [p, q], 'target': target, 'sign': sign}


def constraints(d, generators, triples):
    index = {t: i for i, t in enumerate(triples)}
    for g in generators:
        for i, t in enumerate(triples):
            j = index[tuple(g['target'][k] for k in t)]
            s = g['sign'][t[0]]*g['sign'][t[1]]*g['sign'][t[2]]
            yield i, j, s


def signed_components(n, equations):
    """Solve t_i=s*t_j by parity components and inconsistent signed cycles."""
    parent = list(range(n))
    weight = [1]*n
    zero = [False]*n

    def find(i):
        if parent[i] != i:
            p = parent[i]
            root, w = find(p)
            weight[i] *= w
            parent[i] = root
        return parent[i], weight[i]

    for i, j, s in equations:
        ri, wi = find(i)
        rj, wj = find(j)
        factor = s*wi*wj
        if ri == rj:
            if factor == -1:
                zero[ri] = True
        else:
            # Canonical smallest-index root avoids deep trees.
            lo, hi = sorted((ri, rj))
            parent[hi] = lo
            weight[hi] = factor
            zero[lo] = zero[lo] or zero[hi]
    roots = [find(i) for i in range(n)]
    active = sorted({r for r, w in roots if not zero[r]})
    basis = []
    for root in active:
        v = [w if r == root else 0 for r, w in roots]
        first = next(x for x in v if x)
        basis.append([x*first for x in v])
    return basis


def rational_rank(equations):
    """Separate exact linear-constraint method: sparse Fraction elimination."""
    pivots = {}
    for i, j, s in equations:
        row = {i: Fraction(1)}
        row[j] = row.get(j, Fraction(0))-s
        row = {k: v for k, v in row.items() if v}
        while row:
            p = min(row)
            if p not in pivots:
                a = row[p]
                pivots[p] = {k: v/a for k, v in row.items()}
                break
            a = row[p]
            for k, v in pivots[p].items():
                z = row.get(k, Fraction(0))-a*v
                if z:
                    row[k] = z
                else:
                    row.pop(k, None)
    return len(pivots)


def tensor_results():
    rows = []
    for d in range(2, 11):
        triples = list(product(range(d), repeat=3))
        generators = list(quarter_turns(d))
        equations = list(constraints(d, generators, triples))
        basis = signed_components(d**3, equations)
        rank = rational_rank(equations)
        require(rank == d**3-len(basis), 'rank/component agreement')
        require(len(basis) == (1 if d == 3 else 0), 'expected fixed dimension')
        if d == 3:
            require(basis == [[epsilon(t) for t in triples]], 'epsilon basis')
        require(all(v[i] == s*v[j] for v in basis for i, j, s in equations),
                'all constraint residuals')
        rows.append({'basis': basis, 'constraint_count': len(equations),
                     'dimension': d, 'fixed_dimension': len(basis),
                     'generators': generators, 'rational_rank': rank,
                     'residual_nonzero_count': 0,
                     'signed_component_rank': d**3-len(basis)})
    return rows


def quaternion_results():
    pairs, triples = [], []
    for i, x in enumerate(SET):
        for j, y in enumerate(SET):
            xy = qmul(x, y)
            require(norm(xy) == norm(x)*norm(y), 'pair norm')
            require(phi(xy) == gaussian_matmul(phi(x), phi(y)), 'Pauli pair')
            require(gaussian_det(phi(xy)) == (norm(xy), 0), 'determinant norm')
            pairs.append([i, j, list(xy), norm(xy)])
            for k, z in enumerate(SET):
                left = qmul(xy, z)
                right = qmul(x, qmul(y, z))
                require(left == right, 'associativity')
                require(norm(left) == norm(x)*norm(y)*norm(z), 'triple norm')
                ml = gaussian_matmul(gaussian_matmul(phi(x), phi(y)), phi(z))
                mr = gaussian_matmul(phi(x), gaussian_matmul(phi(y), phi(z)))
                require(ml == mr == phi(left), 'Pauli triple')
                require(rq(qmul(x, y)) == qmul(rq(x), rq(y)), 'rotation product')
                triples.append([i, j, k, list(left), norm(left)])
    inverses = []
    for i, x in enumerate(SET):
        if norm(x):
            inverse = tuple(Fraction(t, norm(x)) for t in conj(x))
            require(qmul(x, inverse) == qmul(inverse, x) == ONE, 'inverse')
            inverses.append([i, [str(t) for t in inverse]])
    return {'input_set': SET, 'inverse_rows': inverses, 'pair_count': len(pairs),
            'pair_fields': ['left_index', 'right_index', 'product', 'norm'],
            'pairs': pairs, 'triple_count': len(triples),
            'triple_fields': ['x_index', 'y_index', 'z_index', 'common_product', 'norm'],
            'triples': triples}


def word_results():
    rows = []
    for n in range(9):
        for letters in product('ab', repeat=n):
            word = ''.join(letters)
            image = substitute(word)
            q = readout(word)
            target = readout(image)
            require(target == rq(q), 'word equivariance')
            m = phi(ONE)
            for letter in image:
                m = gaussian_matmul(m, phi(A if letter == 'a' else B))
            require(m == phi(target), 'independent word arithmetic')
            rows.append([word, image, list(q), list(target)])
    require(len(rows) == 511, 'word count')
    return {'alphabet': {'a': 'alpha', 'b': 'beta'}, 'count': len(rows),
            'fold': 'q0=1; q(k+1)=q(k)*Q(letter(k+1)), in printed left-to-right order',
            'image_max_length': max(len(row[1]) for row in rows),
            'length_domain': list(range(9)),
            'row_fields': ['word', 'substituted_word', 'Q_word', 'Q_image_equals_R_Q_word'],
            'rows': rows, 'substitution': {'a': 'b', 'b': 'ba'}}


def interface_results():
    c = qmul(B, A)
    minus_b = qmul(c, A)
    plus_b = qmul(A, c)
    require(minus_b == tuple(-t for t in B) and plus_b == B, 'representative order')
    require(matmul(transpose(R), R) == IDENTITY and det3(R) == 1, 'SO rotation')
    require(matmul(matmul(R, R), R) == IDENTITY and R != IDENTITY, 'order three')
    m = ((0, 1), (1, 1))
    s = matmul(matmul(m, m), m)
    d = (2, 1)
    native_null_next = tuple(sum(s[i][j]*d[j] for j in range(2)) for i in range(2))
    require(native_null_next == (4, 7), 'native null advances')
    calibrated = []
    cross_mats = (((0, 0, 0), (0, 0, -1), (0, 1, 0)),
                  ((0, 0, 1), (0, 0, 0), (-1, 0, 0)),
                  ((0, -1, 0), (1, 0, 0), (0, 0, 0)))
    for coefficient in (-2, 2):
        gram = [[-Fraction(1, 2)*sum(matmul(cross_mats[i], cross_mats[j])[k][k]
                                     for k in range(3))*coefficient**2
                 for j in range(3)] for i in range(3)]
        require(gram == [[coefficient**2*int(i == j) for j in range(3)] for i in range(3)],
                'uncalibrated metric trace')
        calibrated.append({'c': coefficient, 'trace_metric': [[str(t) for t in row] for row in gram]})
    return {'R': R, 'R_determinant': det3(R), 'R_order': 3,
            'calibration': calibrated,
            'native_25': {'composition': d, 'quantity': 7},
            'native_null_after_25': {'composition': native_null_next, 'quantity': 29},
            'representatives': [['empty-selection', [], list(ONE)],
                                ['2', 'alpha', list(A)], ['3', 'beta', list(B)],
                                ['5', ['beta', 'alpha'], list(c)],
                                ['25', [['beta', 'alpha'], 'alpha'], list(minus_b)]],
            'reversed_25': [['alpha', ['beta', 'alpha']], list(plus_b)],
            'quartic_normalized_values': ['1', '1/3'],
            'volume_same_metrics': {'g1': ['1', '1', '1'], 'g2': ['4', '1/4', '1'],
                                   'T_123': 1, 'B1_23': ['1', '0', '0'],
                                   'B2_23': ['1/4', '0', '0']}}


def seam_results():
    eps = {t: epsilon(t) for t in product(range(3), repeat=3)}
    kernel = [[sum(eps[(i, j, k)]*eps[(l, j, k)] for j in range(3) for k in range(3))
               for l in range(3)] for i in range(3)]
    require(kernel == [[2*int(i == j) for j in range(3)] for i in range(3)], 'typed contraction')
    require(matmul(matmul(R, kernel), transpose(R)) == tuple(map(tuple, kernel)),
            'open kernel symmetry')
    fx = ((1, 0, 0), (0, 0, -1), (0, 1, 0))
    fy = ((0, -1, 0), (1, 0, 0), (0, 0, 1))
    edges = [('p', 0, 1, IDENTITY), ('q', 0, 1, R), ('loop', 0, 0, R)]
    transformed = []
    frames = (fx, fy, IDENTITY)
    for label, v, w, u in edges:
        transformed.append([label, v, w, matmul(matmul(transpose(frames[w]), u), frames[v])])
    based_loop = transpose(R)  # p forward, q backward
    gauged_loop = matmul(transpose(transformed[1][3]), transformed[0][3])
    expected = matmul(matmul(transpose(fx), based_loop), fx)
    require(gauged_loop == expected and based_loop != IDENTITY, 'holonomy conjugacy')
    require(transformed[2][3] == matmul(matmul(transpose(fx), R), fx), 'self loop')
    return {'components': [[0, 1], [2]], 'contraction_kernel': kernel,
            'edges': edges, 'frames': frames, 'gauged_edges': transformed,
            'parallel_based_loop': based_loop, 'gauged_parallel_based_loop': gauged_loop,
            'self_loop': R, 'single_edge_flat_gauge': {'frames': [IDENTITY, R],
                                                    'transport': R,
                                                    'gauged_transport': matmul(transpose(R), R)}}


def certificate():
    return {'arithmetic': 'integer tuples, Gaussian-integer matrices, Fraction constraints',
            'input_provenance': 'Explicit reconstruction; original attachment input sets unavailable',
            'interfaces': interface_results(), 'license': 'MIT for this program and its result data',
            'limitations': ['Finite word domain is not the domain of all bracketed trees',
                            'Quarter-turn samples do not prove the all-dimension theorem',
                            'Self-check methods are not independent author review',
                            'No actual Monster tensor or physical instrument instantiated',
                            'No Lean, RH, physical-dimension or global-novelty certification'],
            'quaternions': quaternion_results(), 'schema': 'fib-stable-relation-boundary-v1',
            'seams': seam_results(),
            'tensor_coordinate_order': 'lexicographic product(range(d), repeat=3), zero-based',
            'tensor_equation': 't[i,j,k]=sign[i]*sign[j]*sign[k]*t[target[i],target[j],target[k]]',
            'tensors': tensor_results(), 'words': word_results()}


def canonical_bytes(value):
    # Object keys are sorted; arrays retain mathematical input order.
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(',', ':'))+'\n').encode('utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', type=Path)
    args = parser.parse_args()
    payload = canonical_bytes(certificate())
    if args.output:
        args.output.write_bytes(payload)
    elif args.check:
        require(args.check.read_bytes() == payload, 'canonical result bytes differ')
    else:
        print(payload.decode('utf-8'), end='')
    if args.output or args.check:
        print('EXACT_FINITE_CERTIFICATE_PASSED')


if __name__ == '__main__':
    main()
