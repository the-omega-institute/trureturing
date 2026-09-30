#!/usr/bin/env python3
"""Exact finite-field check of the MSRD/LRS bouquet construction.

For k=2,3,4 this script constructs K=F_p^2 (p>k), checks the virtual
rank criterion, and exhausts all 2^(4k)=16^k boundary regions.  All
arithmetic is implemented below with pairs (a,b) representing a+b*u,
u^2=d, so no external packages are needed.
"""
from __future__ import annotations

from itertools import product
import json
import sys

Elt = tuple[int, int]


def is_prime(n: int) -> bool:
    return n > 1 and all(n % q for q in range(2, int(n ** 0.5) + 1))


def prime_factors(n: int) -> list[int]:
    out = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            out.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        out.append(n)
    return out


class Fp2:
    """F_p[u]/(u^2-d), with d a nonsquare and p odd."""

    def __init__(self, p: int):
        if p == 2 or not is_prime(p):
            raise ValueError("p must be odd prime")
        self.p = p
        self.d = next(x for x in range(2, p)
                      if pow(x, (p - 1) // 2, p) == p - 1)
        self.zero: Elt = (0, 0)
        self.one: Elt = (1, 0)
        self.u: Elt = (0, 1)
        self.minus_one: Elt = (p - 1, 0)

    def add(self, x: Elt, y: Elt) -> Elt:
        p = self.p
        return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)

    def neg(self, x: Elt) -> Elt:
        p = self.p
        return ((-x[0]) % p, (-x[1]) % p)

    def sub(self, x: Elt, y: Elt) -> Elt:
        return self.add(x, self.neg(y))

    def mul(self, x: Elt, y: Elt) -> Elt:
        p, d = self.p, self.d
        a, b = x
        c, e = y
        return ((a * c + b * e * d) % p, (a * e + b * c) % p)

    def pow(self, x: Elt, n: int) -> Elt:
        out = self.one
        while n:
            if n & 1:
                out = self.mul(out, x)
            x = self.mul(x, x)
            n >>= 1
        return out

    def inv(self, x: Elt) -> Elt:
        if x == self.zero:
            raise ZeroDivisionError
        return self.pow(x, self.p * self.p - 2)

    def sigma(self, x: Elt) -> Elt:
        # Frobenius x |-> x^p, since u^p=-u for nonsquare d.
        return (x[0], (-x[1]) % self.p)

    def primitive(self) -> Elt:
        order = self.p * self.p - 1
        factors = prime_factors(order)
        for a in range(self.p):
            for b in range(self.p):
                x = (a, b)
                if x == self.zero:
                    continue
                if all(self.pow(x, order // q) != self.one for q in factors):
                    return x
        raise RuntimeError("no primitive element found")

    def norm(self, x: Elt, ell: int) -> Elt:
        out = self.one
        cur = x
        for _ in range(ell):
            out = self.mul(out, cur)
            cur = self.sigma(cur)
        return out

    def rank(self, rows: list[list[Elt]]) -> int:
        """Gaussian rank over K, exact (no package arithmetic)."""
        if not rows:
            return 0
        a = [[tuple(v) for v in row] for row in rows]
        nr, nc = len(a), len(a[0])
        r = 0
        for c in range(nc):
            piv = next((i for i in range(r, nr) if a[i][c] != self.zero), None)
            if piv is None:
                continue
            a[r], a[piv] = a[piv], a[r]
            iv = self.inv(a[r][c])
            a[r] = [self.mul(v, iv) for v in a[r]]
            for i in range(nr):
                if i == r or a[i][c] == self.zero:
                    continue
                q = a[i][c]
                a[i] = [self.sub(a[i][j], self.mul(q, a[r][j]))
                        for j in range(nc)]
            r += 1
            if r == nr:
                break
        return r


def next_odd_prime(n: int) -> int:
    q = max(3, n)
    if q % 2 == 0:
        q += 1
    while not is_prime(q):
        q += 2
    return q


def vector_add(f: Fp2, x: list[Elt], y: list[Elt]) -> list[Elt]:
    return [f.add(a, b) for a, b in zip(x, y)]


def vector_sub(f: Fp2, x: list[Elt], y: list[Elt]) -> list[Elt]:
    return [f.sub(a, b) for a, b in zip(x, y)]


def construct_central(f: Fp2, k: int, gamma: Elt) -> list[tuple[list[Elt], list[Elt]]]:
    """Return [(a_j,b_j)] from the LRS norm/Frobenius prescription."""
    blocks = []
    for j in range(k):
        x = f.pow(gamma, j)
        a, b = [], []
        for ell in range(k):
            n_ell = f.norm(x, ell)
            a.append(f.mul(f.one, n_ell))  # sigma^ell(1)=1
            sigma_u = f.u if ell % 2 == 0 else f.neg(f.u)
            b.append(f.mul(sigma_u, n_ell))
        blocks.append((a, b))
    return blocks


def virtual_choices(f: Fp2, blocks: list[tuple[list[Elt], list[Elt]]], k: int):
    """Exhaust all none/one/pair block choices of total size k."""
    options = []
    for a, b in blocks:
        apb = vector_add(f, a, b)
        amb = vector_sub(f, a, b)
        options.append([(), (a,), (b,), (apb,), (amb,), (a, b)])
    checked = bad = 0
    bad_choice = None
    for choice in product(*options):
        rows = [row for block in choice for row in block]
        if len(rows) != k:
            continue
        checked += 1
        if f.rank(rows) != k:
            bad += 1
            if bad_choice is None:
                bad_choice = choice
    return checked, bad, bad_choice


def boundary_rows(f: Fp2, blocks: list[tuple[list[Elt], list[Elt]]], k: int):
    """Loop-j rows (a,+e_j),(a,-e_j),(b,+e_j),(b,-e_j)."""
    rows = []
    for j, (a, b) in enumerate(blocks):
        ep = [f.one if i == j else f.zero for i in range(k)]
        em = [f.neg(f.one) if i == j else f.zero for i in range(k)]
        rows.extend([a + ep, a + em, b + ep, b + em])
    return rows


def loop_counts(mask: int, j: int) -> tuple[int, int, int]:
    base = 4 * j
    a = ((mask >> base) & 1) + ((mask >> (base + 1)) & 1)
    b = ((mask >> (base + 2)) & 1) + ((mask >> (base + 3)) & 1)
    return a, b, a + b


def graph_loop_cost(c: int, alpha: int, beta: int, a: int, b: int) -> int:
    # OA_j, OB_j, A_jB_j, and the four boundary legs, exactly as in the
    # bouquet graph. Boundary region sides are encoded by a and b.
    return ((alpha != c) + (beta != c) + (alpha != beta)
            + (a if alpha == 0 else 2 - a)
            + (b if beta == 0 else 2 - b))


def graph_mincut(mask: int, k: int) -> int:
    # Outer pair assignments are independent once the center side c is fixed.
    best = 10 ** 9
    for c in (0, 1):
        cost = 0
        for j in range(k):
            a, b, _ = loop_counts(mask, j)
            cost += min(graph_loop_cost(c, alpha, beta, a, b)
                        for alpha in (0, 1) for beta in (0, 1))
        best = min(best, cost)
    return best


def run_case(k: int) -> dict:
    p = next_odd_prime(k + 1)
    f = Fp2(p)
    gamma = f.primitive()
    blocks = construct_central(f, k, gamma)
    virtual_total, virtual_bad, bad_choice = virtual_choices(f, blocks, k)
    c_rows = [row for a, b in blocks for row in (a, b)]
    central_rank = f.rank(c_rows)
    rows = boundary_rows(f, blocks, k)
    total = 1 << (4 * k)
    rank_fail = cut_fail = formula_fail = 0
    first_failure = None
    e = (0, 0, 1, 2, 2)
    for mask in range(total):
        selected = [rows[i] for i in range(4 * k) if (mask >> i) & 1]
        complement = [rows[i] for i in range(4 * k) if not ((mask >> i) & 1)]
        rank_r = f.rank(selected)
        rank_c = f.rank(complement)
        entropy = rank_r + rank_c - 2 * k
        h_r = h_c = partial = E = 0
        counts = []
        for j in range(k):
            _, _, r = loop_counts(mask, j)
            counts.append(r)
            h_r += r > 0
            h_c += r < 4
            partial += 0 < r < 4
            E += e[r]
        expected_rank_r = h_r + min(k, E)
        expected_rank_c = h_c + min(k, 2 * k - E)
        expected_cut = partial + min(E, 2 * k - E)
        cut = graph_mincut(mask, k)
        if rank_r != expected_rank_r or rank_c != expected_rank_c:
            rank_fail += 1
            if first_failure is None:
                first_failure = {
                    "kind": "rank", "mask": mask, "counts": counts,
                    "rank_r": rank_r, "expected_rank_r": expected_rank_r,
                    "rank_c": rank_c, "expected_rank_c": expected_rank_c,
                }
        if cut != expected_cut:
            cut_fail += 1
            if first_failure is None:
                first_failure = {
                    "kind": "cut", "mask": mask, "counts": counts,
                    "cut": cut, "expected_cut": expected_cut,
                }
        if entropy != expected_cut:
            formula_fail += 1
            if first_failure is None:
                first_failure = {
                    "kind": "entropy", "mask": mask, "counts": counts,
                    "entropy": entropy, "expected_cut": expected_cut,
                }
    return {
        "k": k,
        "p": p,
        "nonsquare_d": f.d,
        "gamma": gamma,
        "central_rank": central_rank,
        "virtual_choices": virtual_total,
        "virtual_bad": virtual_bad,
        "boundary_subsets": total,
        "rank_formula_fail": rank_fail,
        "cut_formula_fail": cut_fail,
        "entropy_cut_fail": formula_fail,
        "first_failure": first_failure,
    }


def main() -> int:
    ks = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [2, 3, 4]
    results = [run_case(k) for k in ks]
    print(json.dumps(results, indent=2, sort_keys=True))
    ok = all(all(result[key] == 0 for key in
                 ("virtual_bad", "rank_formula_fail", "cut_formula_fail", "entropy_cut_fail"))
              and result["central_rank"] == result["k"]
              for result in results)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
