#!/usr/bin/env python3
"""Exact dyadic interval replay for a six-dimensional MUB parameter patch.

No floating-point or third-party operations participate in acceptance.
Local root existence uses the contraction theorem; completeness uses the
Segre linear-section degree bound described in the companion README.
This checker is not a Lean kernel proof.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from pathlib import Path

BITS = 120
SCALE = 1 << BITS


def ceil_div(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError('positive denominator required')
    return -((-a) // b)


class I:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo: int, hi: int | None = None):
        self.lo, self.hi = lo, lo if hi is None else hi
        if self.lo > self.hi:
            raise ValueError('empty interval')

    @staticmethod
    def rat(v: str | int | Fraction) -> 'I':
        v = Fraction(v)
        return I((v.numerator * SCALE) // v.denominator,
                 ceil_div(v.numerator * SCALE, v.denominator))

    @staticmethod
    def box(lo: str, hi: str) -> 'I':
        return I(I.rat(lo).lo, I.rat(hi).hi)

    def __add__(self, other: 'I | int') -> 'I':
        if isinstance(other, int):
            other = I.rat(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self) -> 'I':
        return I(-self.hi, -self.lo)

    def __sub__(self, other: 'I | int') -> 'I':
        return self + (-other)

    def __rsub__(self, other: int) -> 'I':
        return I.rat(other) - self

    def __mul__(self, other: 'I | int') -> 'I':
        if isinstance(other, int):
            return I(self.lo * other, self.hi * other) if other >= 0 else -(self * (-other))
        p = (self.lo * other.lo, self.lo * other.hi,
             self.hi * other.lo, self.hi * other.hi)
        return I(min(p) // SCALE, ceil_div(max(p), SCALE))

    __rmul__ = __mul__

    def inv(self) -> 'I':
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError('interval contains zero')
        if self.hi < 0:
            return -((-self).inv())
        return I(SCALE * SCALE // self.hi, ceil_div(SCALE * SCALE, self.lo))

    def __truediv__(self, other: 'I | int') -> 'I':
        if isinstance(other, int):
            other = I.rat(other)
        return self * other.inv()

    def sq(self) -> 'I':
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo * self.lo, self.hi * self.hi)
        high = max(self.lo * self.lo, self.hi * self.hi)
        return I(low // SCALE, ceil_div(high, SCALE))

    def abs_upper(self) -> int:
        return max(abs(self.lo), abs(self.hi))

    def inside(self, other: 'I') -> bool:
        return other.lo < self.lo and self.hi < other.hi


class Z:
    __slots__ = ('re', 'im')

    def __init__(self, re: I | int = 0, im: I | int = 0):
        self.re = I.rat(re) if isinstance(re, int) else re
        self.im = I.rat(im) if isinstance(im, int) else im

    def __add__(self, w: 'Z') -> 'Z':
        return Z(self.re + w.re, self.im + w.im)

    def __neg__(self) -> 'Z':
        return Z(-self.re, -self.im)

    def __sub__(self, w: 'Z') -> 'Z':
        return self + (-w)

    def __mul__(self, w: 'Z') -> 'Z':
        return Z(self.re * w.re - self.im * w.im,
                 self.re * w.im + self.im * w.re)

    def conj(self) -> 'Z':
        return Z(self.re, -self.im)

    def abs2(self) -> I:
        return self.re.sq() + self.im.sq()

    def inv(self) -> 'Z':
        den = self.abs2()
        return Z(self.re / den, -self.im / den)

    def scale(self, c: I | int) -> 'Z':
        return Z(self.re * c, self.im * c)


def cayley(t: I, sgn: int = 1) -> Z:
    den = 1 + t.sq()
    return Z((1 - t.sq()) / den, (2 * t) / den).scale(sgn)


def cayley_derivative(t: I, sgn: int) -> Z:
    qi = Z(1, -t).inv()
    return (Z(0, 2) * qi * qi).scale(sgn)


def polynomial(coeffs: list[int], t: Fraction) -> Fraction:
    y = Fraction(0)
    for c in coeffs:
        y = y * t + c
    return y


def exact_seed(doc: dict) -> list[list[Z]]:
    prescribed = [[5, 1, -11, 1], [3, -1, -13, -1]]
    if doc['seed']['polynomials'] != prescribed:
        raise ValueError('unexpected seed')
    parameter = doc['seed'].get('parameter_box')
    coefficient_boxes = None
    if parameter is not None:
        a = I.box(*parameter['real'])
        b = I.box(*parameter['imag'])
        if not (a.lo > 0 and b.lo > 0 and a.hi < SCALE and b.hi < SCALE):
            raise ValueError('parameter outside declared patch')
        coefficient_boxes = [[1 + a, b, a - 3, b], [1 - a, -b, -a - 3, -b]]
    groups = []
    for group_id, (coeffs, boxes) in enumerate(zip(prescribed, doc['seed']['root_intervals'])):
        if len(boxes) != 3:
            raise ValueError('three roots required')
        prev = None
        group = []
        for lo, hi in boxes:
            lo, hi = Fraction(lo), Fraction(hi)
            if not lo < hi or (prev is not None and not prev < lo):
                raise ValueError('root boxes must be ordered and disjoint')
            if coefficient_boxes is None:
                if polynomial(coeffs, lo) * polynomial(coeffs, hi) >= 0:
                    raise ValueError('no strict sign change')
            else:
                def evaluate(t):
                    ans = I(0)
                    for c in coefficient_boxes[group_id]:
                        ans = ans * I.rat(t) + c
                    return ans
                left, right = evaluate(lo), evaluate(hi)
                if not (left.hi < 0 < right.lo or right.hi < 0 < left.lo):
                    raise ValueError('no uniform strict sign change over parameter box')
            group.append(cayley(I.box(str(lo), str(hi))))
            prev = hi
        groups.append(group)
    r, s = groups

    def circ(v):
        a, b, c = v
        return [[a, b, c], [c, a, b], [b, c, a]]

    A = circ([r[0] * r[1], r[1], Z(1)])
    B = circ([s[0] * s[1], s[1], Z(1)])
    return [[A[i][j] if i < 3 and j < 3 else
             B[i][j - 3] if i < 3 else
             B[j][i - 3].conj() if j < 3 else
             -A[j - 3][i - 3].conj()
             for j in range(6)] for i in range(6)]


def sum_z(v: list[Z]) -> Z:
    ans = Z()
    for x in v:
        ans = ans + x
    return ans


def phasors(t: list[I], signs: list[int]) -> list[Z]:
    if len(signs) != 5 or any(s not in (-1, 1) for s in signs):
        raise ValueError('bad chart')
    return [Z(1)] + [cayley(x, s) for x, s in zip(t, signs)]


def system(H: list[list[Z]], t: list[I], signs: list[int], jac: bool = False):
    u = phasors(t, signs)
    g = [sum_z([H[j][a].conj() * u[j] for j in range(6)]) for a in range(5)]
    f = [v.abs2() - 6 for v in g]
    if not jac:
        return f
    deriv = [cayley_derivative(x, s) for x, s in zip(t, signs)]
    J = [[2 * (g[a].conj() * H[j + 1][a].conj() * deriv[j]).re
          for j in range(5)] for a in range(5)]
    return f, J


def inverse_rational(A: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(A)
    aug = [row[:] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(A)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if aug[i][k]), None)
        if pivot is None:
            raise ValueError('singular rational midpoint Jacobian')
        aug[k], aug[pivot] = aug[pivot], aug[k]
        c = aug[k][k]
        aug[k] = [x / c for x in aug[k]]
        for i in range(n):
            if i != k:
                c = aug[i][k]
                aug[i] = [x - c * y for x, y in zip(aug[i], aug[k])]
    return [row[n:] for row in aug]


def validate_box(H: list[list[Z]], item: dict):
    center = [I.rat(Fraction(v, 1 << 48)) for v in item['center_numerators']]
    radius = I.rat(Fraction(1, 1 << item.get('radius_bits', 30)))
    if len(center) != 5 or any(c.lo != c.hi for c in center):
        raise ValueError('five exact dyadic coordinates required')
    if radius.lo != radius.hi or radius.lo <= 0:
        raise ValueError('bad radius')
    X = [I(c.lo - radius.lo, c.hi + radius.hi) for c in center]
    signs = item['signs']
    _, pointJ = system(H, center, signs, True)
    raw = inverse_rational([[Fraction(v.lo + v.hi, 2 * SCALE) for v in row] for row in pointJ])
    C = [[I.rat(Fraction(round(v * (1 << 48)), 1 << 48)) for v in row] for row in raw]
    f0 = system(H, center, signs)
    _, J = system(H, X, signs, True)
    R = [[I.rat(int(i == j)) - sum((C[i][k] * J[k][j] for k in range(5)), I(0))
          for j in range(5)] for i in range(5)]
    contraction = max(sum(x.abs_upper() for x in row) for row in R)
    if contraction >= SCALE:
        raise ValueError('not a strict contraction')
    K = []
    for i in range(5):
        value = center[i] - sum((C[i][k] * f0[k] for k in range(5)), I(0))
        value = value + sum((R[i][j] * I(-radius.hi, radius.hi) for j in range(5)), I(0))
        if not value.inside(X[i]):
            raise ValueError('Krawczyk image not strictly inside box')
        K.append(value)
    return K, X, contraction, min(min(k.lo - x.lo, x.hi - k.hi) for k, x in zip(K, X))


def complex_system(H: list[list[Z]], x: list[I], jac: bool = False):
    n = 5
    u = [Z(1)] + [Z(x[j], x[n + j]) for j in range(n)]
    inv = [v.inv() for v in u]
    g = [sum_z([H[j][a].conj() * u[j] for j in range(6)]) for a in range(n)]
    h = [sum_z([H[j][a] * inv[j] for j in range(6)]) for a in range(n)]
    f = [g[a] * h[a] - Z(6) for a in range(n)]
    values = [z.re for z in f] + [z.im for z in f]
    if not jac:
        return values
    J = [[H[j + 1][a].conj() * h[a] - g[a] * H[j + 1][a] * inv[j + 1] * inv[j + 1]
          for j in range(n)] for a in range(n)]
    realJ = [[z.re for z in row] + [-z.im for z in row] for row in J]
    realJ += [[z.im for z in row] + [z.re for z in row] for row in J]
    return values, realJ


def validate_complex_box(H: list[list[Z]], item: list[int], radius_bits: int = 26):
    if len(item) != 10:
        raise ValueError('ten real coordinates required')
    center = [I.rat(Fraction(v, 1 << 40)) for v in item]
    rad = 1 << (BITS - radius_bits)
    X = [I(c.lo - rad, c.hi + rad) for c in center]
    _, pointJ = complex_system(H, center, True)
    raw = inverse_rational([[Fraction(v.lo + v.hi, 2 * SCALE) for v in row] for row in pointJ])
    C = [[I.rat(Fraction(round(v * (1 << 48)), 1 << 48)) for v in row] for row in raw]
    f0 = complex_system(H, center)
    _, J = complex_system(H, X, True)
    R = [[I.rat(int(i == j)) - sum((C[i][k] * J[k][j] for k in range(10)), I(0))
          for j in range(10)] for i in range(10)]
    contraction = max(sum(v.abs_upper() for v in row) for row in R)
    if contraction >= SCALE:
        raise ValueError('complex box is not contracting')
    K = []
    for i in range(10):
        val = center[i] - sum((C[i][k] * f0[k] for k in range(10)), I(0))
        val = val + sum((R[i][j] * I(-rad, rad) for j in range(10)), I(0))
        if not val.inside(X[i]):
            raise ValueError('complex Krawczyk image not inside')
        K.append(val)
    return [Z(1)] + [Z(K[j], K[5 + j]) for j in range(5)], X, contraction


def expand_complex_center_hints(doc: dict):
    reps = doc.get('complex_orbit_center_numerators')
    if reps is None:
        return doc.get('complex_boxes')

    def center(u):
        u = [v * u[0].inv() for v in u]
        x = [z.re for z in u[1:]] + [z.im for z in u[1:]]
        return [round(Fraction(t.lo + t.hi, 2 * SCALE) * (1 << 40)) for t in x]

    data = []
    for b in doc['boxes']:
        t = [I.rat(Fraction(v, 1 << 48)) for v in b['center_numerators']]
        data.append(center(phasors(t, b['signs'])))
    # Symmetry is used only to generate center hints. Every resulting box is
    # independently checked below; no numerical path tracking is trusted.
    for row in reps:
        if len(row) != 10:
            raise ValueError('bad complex orbit representative')
        u = [Z(1)] + [Z(I.rat(Fraction(row[j], 1 << 40)),
                        I.rat(Fraction(row[5 + j], 1 << 40))) for j in range(5)]
        for sig in (False, True):
            for th in (False, True):
                v = [z.conj().inv() for z in u] if sig else u[:]
                if th:
                    v = [-v[3].conj(), -v[5].conj(), -v[4].conj(),
                         v[0].conj(), v[2].conj(), v[1].conj()]
                for _ in range(3):
                    data.append(center(v))
                    v = [v[1], v[2], v[0], v[4], v[5], v[3]]
    return data


def complete_complex_cover(H: list[list[Z]], doc: dict, unit_vectors: list[list[Z]]):
    data = expand_complex_center_hints(doc)
    if data is None:
        return None
    if len(data) != 252:
        raise ValueError('252 boxes required for degree saturation')
    roots, domains, rates = [], [], []
    for j, item in enumerate(data):
        try:
            u, X, rate = validate_complex_box(H, item, doc.get('complex_radius_bits', 26))
        except (ValueError, ZeroDivisionError) as e:
            raise ValueError('complex box ' + str(j) + ': ' + str(e)) from e
        roots.append(u)
        domains.append(X)
        rates.append(rate)
    for j, u in enumerate(roots):
        for v in roots[:j]:
            if not any((a - b).abs2().lo > 0 for a, b in zip(u, v)):
                raise ValueError('complex roots not certified distinct')
    matches = []
    for v in unit_vectors:
        hits = []
        for j, X in enumerate(domains):
            coords = [z.re for z in v[1:]] + [z.im for z in v[1:]]
            if all(a.inside(b) for a, b in zip(coords, X)):
                hits.append(j)
        if len(hits) != 1:
            raise ValueError('real ray not matched to unique complex box')
        matches.append(hits[0])
    if len(set(matches)) != 60:
        raise ValueError('real-to-complex match not injective')
    nonreal = [j for j in range(252) if j not in matches]
    gaps = []
    for j in nonreal:
        sep = max(max(z.abs2().lo - SCALE, SCALE - z.abs2().hi, 0) for z in roots[j][1:])
        if sep <= 0:
            raise ValueError('nonphysical complex root not separated from unit torus')
        gaps.append(sep)
    return {
        'nonsingular_distinct_complex_roots': 252,
        'physical_roots_matched': matches,
        'nonphysical_roots': len(nonreal),
        'complex_contraction_upper': str(Fraction(max(rates), SCALE)),
        'minimum_nonphysical_squared_modulus_gap': str(Fraction(min(gaps), SCALE)),
        'degree_bound': 252,
        'degree_bound_reason': 'linear section of Segre(P5 x P5), degree binomial(10,5); sum of degrees of all irreducible intersection components is bounded by 252',
        'global_exhaustiveness_via_degree_saturation': True,
        'degree_bound_formalized_in_Lean': False,
    }


def replay(doc: dict) -> dict:
    if doc.get('schema') != 'mub6-exact-seed-root-boxes-v1':
        raise ValueError('wrong schema')
    H = exact_seed(doc)
    boxes = doc['boxes']
    vectors, domains, ratios, margins = [], [], [], []
    for box in boxes:
        K, X, r, m = validate_box(H, box)
        vectors.append(phasors(K, box['signs']))
        domains.append(X)
        ratios.append(r)
        margins.append(m)
    n = len(vectors)
    for i in range(n):
        for j in range(i):
            if not any((v - w).abs2().lo > 0 for v, w in zip(vectors[i], vectors[j])):
                raise ValueError('root boxes not proved projectively distinct')
    excluded, unresolved = [], []
    minimum = None
    for i in range(n):
        for j in range(i):
            inner = sum_z([v.conj() * w for v, w in zip(vectors[i], vectors[j])])
            sq = inner.abs2()
            if sq.lo > 0:
                excluded.append([j, i])
                minimum = sq.lo if minimum is None else min(minimum, sq.lo)
            else:
                unresolved.append([j, i])

    def R(u):
        return [u[1], u[2], u[0], u[4], u[5], u[3]]

    def theta(u):
        return [-u[3].conj(), -u[5].conj(), -u[4].conj(),
                u[0].conj(), u[2].conj(), u[1].conj()]

    def identify(u):
        inv = u[0].inv()
        u = [v * inv for v in u]
        hits = []
        for j, box in enumerate(boxes):
            try:
                t = []
                for v, sgn in zip(u[1:], box['signs']):
                    z = v.scale(sgn)
                    t.append(z.im / (1 + z.re))
                if all(v.inside(X) for v, X in zip(t, domains[j])):
                    hits.append(j)
            except ZeroDivisionError:
                pass
        if len(hits) != 1:
            raise ValueError('symmetry image is not uniquely enclosed')
        return hits[0]

    Rp = [identify(R(u)) for u in vectors]
    Tp = [identify(theta(u)) for u in vectors]
    if sorted(Rp) != list(range(n)) or sorted(Tp) != list(range(n)):
        raise ValueError('not permutations')
    for j in range(n):
        if Rp[Rp[Rp[j]]] != j or Tp[Tp[j]] != j or Tp[Rp[j]] != Rp[Rp[Tp[j]]]:
            raise ValueError('bad projective dihedral relations')
    proved_edges = set()
    for j in range(n):
        other = Tp[j]
        for _ in range(3):
            if j == other:
                raise ValueError('antiunitary orthogonality fixed a ray')
            proved_edges.add(tuple(sorted((j, other))))
            other = Rp[other]
    fixed = [j for j in range(n) if Rp[j] == j]
    eigenvalue = {j: R(vectors[j])[0] for j in fixed}
    for j in fixed:
        for k in fixed:
            if j < k and (eigenvalue[j] - eigenvalue[k]).abs2().lo > 0:
                proved_edges.add((j, k))
    if set(map(tuple, unresolved)) != proved_edges:
        raise ValueError('some unresolved pair has no exact symmetry proof')
    nbr = [set() for _ in range(n)]
    for i, j in proved_edges:
        nbr[i].add(j)
        nbr[j].add(i)
    components = []
    remaining = set(range(n))
    while remaining:
        todo = [min(remaining)]
        part = set()
        while todo:
            j = todo.pop()
            if j in part:
                continue
            part.add(j)
            todo.extend(nbr[j] - part)
        remaining -= part
        ordered = sorted(part)
        complete = all(j == k or k in nbr[j] for j in part for k in part)
        colour = {ordered[0]: 0}
        todo = [ordered[0]]
        bip = True
        while todo:
            j = todo.pop()
            for k in nbr[j]:
                if k not in colour:
                    colour[k] = 1 - colour[j]
                    todo.append(k)
                elif colour[k] == colour[j]:
                    bip = False
        sides = [sum(v == c for v in colour.values()) for c in (0, 1)]
        complete_bip = bip and all((k in nbr[j]) == (colour[j] != colour[k])
                                  for j in part for k in part)
        if complete:
            kind = 'K' + str(len(part))
        elif complete_bip:
            kind = 'K' + ','.join(map(str, sorted(sides)))
        else:
            kind = 'other'
        components.append({'vertices': ordered, 'type': kind})
    cliques = []

    def clique(chosen: list[int], candidates: set[int]):
        if len(chosen) == 6:
            cliques.append(chosen)
            return
        if len(chosen) + len(candidates) < 6:
            return
        for v in sorted(candidates):
            clique(chosen + [v], {w for w in candidates if w > v} & nbr[v])

    clique([], set(range(n)))
    cover = complete_complex_cover(H, doc, vectors)
    return {
        'complex_cover': cover,
        'verified_distinct_local_roots': n,
        'parameter_box': doc['seed'].get('parameter_box'),
        'arithmetic': 'outward-rounded integer dyadic intervals, 120 fractional bits',
        'existence_uniqueness': 'strict box self-map and contraction for preconditioned Newton map',
        'contraction_upper': str(Fraction(max(ratios), SCALE)),
        'minimum_inclusion_margin': str(Fraction(min(margins), SCALE)),
        'excluded_pairs': len(excluded),
        'symmetry_certified_orthogonal_pairs': len(proved_edges),
        'R_permutation': Rp,
        'Theta_permutation': Tp,
        'components': components,
        'minimum_excluded_normalized_inner_product_squared': str(Fraction(minimum, 36 * SCALE)),
        'possible_six_cliques_within_certified_set': cliques,
        'global_exhaustiveness_via_segre_degree_bound': cover is not None,
        'all_pairs_on_certified_set_classified': True,
        'strict_X_seam_nonmembership_proved': False,
        'Lean_kernel_checked': False,
        'scope': 'Interval arithmetic certifies local simple roots, symmetry identification, and nonedges. With complex_cover present, 252 nonsingular distinct complex roots exhaust the Segre linear-section degree; exactly 60 are physical. The contraction, symmetry, and degree theorems are mathematical inputs, not claimed as Lean-kernel-checked. No assertion is made outside the stated rectangle or for other Hadamard families.',
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    report = replay(json.loads(args.certificate.read_text()))
    rendered = json.dumps(report, indent=2)
    if args.report:
        args.report.write_text(rendered + '\n')
    print(rendered)


if __name__ == '__main__':
    main()
