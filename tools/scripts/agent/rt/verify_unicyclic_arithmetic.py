#!/usr/bin/env python3
"""Direct finite checks for ARITHMETIC_UNICYCLIC_EXACT_RT.md.

The proof is symbolic. This certificate checks the displayed open-edge state
against brute-force cycle min-cuts for every boundary subset at d=3, L=3,4,
and checks the unit criterion at d=9, L=3.
"""
from __future__ import annotations

import itertools
import math
import sys

import numpy as np


def state(d: int, L: int, alpha: int) -> dict[tuple[int, ...], complex]:
    omega = np.exp(2j * np.pi / d)
    amplitudes: dict[tuple[int, ...], complex] = {}
    for x in itertools.product(range(d), repeat=L + 1):
        labels = []
        for i in range(L):
            labels.extend(((x[i] + x[i + 1]) % d,
                           (x[i] + 2 * x[i + 1]) % d))
        labels_t = tuple(labels)
        phase = omega ** ((x[0] * x[L] + alpha * x[0] * x[0]) % d)
        amplitudes[labels_t] = phase / (d ** ((L + 1) / 2))
    if len(amplitudes) != d ** (L + 1):
        raise AssertionError("boundary label map is not injective")
    norm = sum(abs(z) ** 2 for z in amplitudes.values())
    if abs(norm - 1.0) > 1e-10:
        raise AssertionError(f"normalization failed: {norm}")
    return amplitudes


def entropy(amplitudes: dict[tuple[int, ...], complex],
            d: int, L: int, mask: int) -> float:
    selected = [i for i in range(2 * L) if (mask >> i) & 1]
    complement = [i for i in range(2 * L) if not ((mask >> i) & 1)]
    rows = list(itertools.product(range(d), repeat=len(selected)))
    cols = list(itertools.product(range(d), repeat=len(complement)))
    row_index = {v: i for i, v in enumerate(rows)}
    col_index = {v: i for i, v in enumerate(cols)}
    matrix = np.zeros((len(rows), len(cols)), dtype=complex)
    for labels, amplitude in amplitudes.items():
        r = tuple(labels[i] for i in selected)
        c = tuple(labels[i] for i in complement)
        matrix[row_index[r], col_index[c]] = amplitude
    singular = np.linalg.svd(matrix, compute_uv=False)
    probabilities = singular[singular > 1e-9] ** 2
    return float(-sum(p * math.log(p) for p in probabilities))


def mincut(L: int, mask: int) -> int:
    best = 10 ** 9
    for vertex_side in itertools.product((0, 1), repeat=L):
        crossing = sum(vertex_side[i] != vertex_side[(i + 1) % L]
                        for i in range(L))
        for i in range(L):
            for leg in (0, 1):
                crossing += vertex_side[i] != ((mask >> (2 * i + leg)) & 1)
        best = min(best, crossing)
    return best


def unit_criterion(d: int, L: int, alpha: int) -> bool:
    for k in range(L + 1):
        inv2 = pow(2, -1, d)
        ck = (2 * alpha + ((-1) ** L) *
              (pow(inv2, k, d) + pow(inv2, L - k, d))) % d
        if math.gcd(ck, d) != 1:
            return False
    return True


def run() -> None:
    for L in (3, 4):
        d = 3
        alpha = 1 if L % 2 else 0
        amplitudes = state(d, L, alpha)
        for mask in range(1 << (2 * L)):
            observed = entropy(amplitudes, d, L, mask)
            expected = mincut(L, mask) * math.log(d)
            if abs(observed - expected) > 1e-8:
                raise AssertionError((d, L, mask, observed, expected))
        print(f"PASS d={d} L={L}: {1 << (2 * L)} boundary regions")
    if not unit_criterion(9, 3, 1):
        raise AssertionError("odd-cycle d=9 criterion failed")
    print("PASS d=9 L=3: all c_k are units")


if __name__ == "__main__":
    run()
