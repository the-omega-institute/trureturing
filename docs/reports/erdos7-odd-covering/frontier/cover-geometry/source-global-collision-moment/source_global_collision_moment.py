#!/usr/bin/env python3
"""Exact finite checks for the coupled collision moment formulas.

The program checks only the finite embedding probabilities and their
factorisation.  It deliberately does not claim an odd whole-cover instance.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path


def child_subsets(s: int, r: int):
    return tuple(combinations(range(s), r))


def embeddings(s: int, r: int, depth: int):
    """Return image sets of compatible rooted embeddings through `depth`.

    A word is a tuple of base-s digits, least significant first.  For depth
    at most two this exhaustive generator is small enough for exact checks.
    """
    choices = child_subsets(s, r)
    out = [frozenset({()})]
    if depth == 0:
        return tuple(out)
    level = [frozenset({(c,) for c in C}) for C in choices]
    out = level
    for b in range(2, depth + 1):
        next_level = []
        for image in out:
            nodes = _node_words(image)
            for selected in product(choices, repeat=len(nodes)):
                grown = set(image)
                for w, C in zip(nodes, selected):
                    grown.update(w + (c,) for c in C)
                next_level.append(frozenset(grown))
        out = next_level
    return tuple(out)


def _node_words(image):
    # The selected prefixes at the previous level are exactly the nodes where
    # a child subset must be selected.  Deduplication is deterministic.
    return tuple(sorted(image))


def in_image(image, word):
    return tuple(word) in image


def common_prefix_length(w, w2):
    ell = 0
    for a, b in zip(w, w2):
        if a != b:
            break
        ell += 1
    return ell


def kappa_formula(r, s, w, w2):
    b = len(w)
    if w == w2:
        return Fraction(r, s) ** b
    ell = common_prefix_length(w, w2)
    return (
        Fraction(r, s) ** ell
        * Fraction(r * (r - 1), s * (s - 1))
        * Fraction(r, s) ** (2 * (b - ell - 1))
    )


def kappa_exact(r, s, w, w2):
    imgs = embeddings(s, r, len(w))
    hits = sum(in_image(img, w) and in_image(img, w2) for img in imgs)
    return Fraction(hits, len(imgs))


def safe_coordinate_factor(U, r, a, a2, alpha, alpha2):
    good = [u for u in U if u % (r**a) == alpha % (r**a)
            and u % (r**a2) == alpha2 % (r**a2)]
    return Fraction(len(good), len(U))


def pair_factor_exact(U, r, s, a, a2, alpha, alpha2, w, w2):
    """Brute-force joint survival probability over u and one common tree."""
    imgs = embeddings(s, r, len(w))
    total = 0
    for u in U:
        if u % (r**a) != alpha % (r**a) or u % (r**a2) != alpha2 % (r**a2):
            continue
        total += sum(in_image(img, w) and in_image(img, w2) for img in imgs)
    return Fraction(total, len(U) * len(imgs))


def run_case(r, s, depth):
    imgs = embeddings(s, r, depth)
    checks = 0
    for w in _words(s, depth):
        for w2 in _words(s, depth):
            exact = kappa_exact(r, s, w, w2)
            formula = kappa_formula(r, s, w, w2)
            if exact != formula:
                raise AssertionError((r, s, depth, w, w2, exact, formula))
            checks += 1

    # A nontrivial safe-coordinate law with correlated prefix constraints.
    U = tuple(u for u in range(r**(depth + 1)) if u not in {0})
    a, a2 = max(1, depth - 1), depth
    alpha, alpha2 = 1, 1
    w = tuple(range(depth))
    w2 = tuple(reversed(range(depth)))
    rho = safe_coordinate_factor(U, r, a, a2, alpha, alpha2)
    kappa = kappa_formula(r, s, w, w2)
    exact_joint = pair_factor_exact(U, r, s, a, a2, alpha, alpha2, w, w2)
    if exact_joint != rho * kappa:
        raise AssertionError(("factor", r, s, depth, exact_joint, rho * kappa))
    return {"r": r, "s": s, "depth": depth,
            "embedding_count": len(imgs), "kappa_checks": checks,
            "rho": str(rho), "kappa": str(kappa),
            "joint": str(exact_joint)}


def _words(s, depth):
    if depth == 0:
        return [()]
    words = [()]
    for _ in range(depth):
        words = [w + (c,) for w in words for c in range(s)]
    return words


def main():
    cases = [run_case(2, 3, 1), run_case(2, 3, 2),
             run_case(3, 5, 1), run_case(3, 5, 2)]
    result = {
        "status": "PASS",
        "scope": "finite common-tree probability identities only",
        "cases": cases,
        "checks": sum(c["kappa_checks"] for c in cases),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
