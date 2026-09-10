"""Direct 56D head-padding control, adapted from the dispatcher artifact
/tmp/trureturing-5040-autonomous-padding.py (2026-09-08).
This constructs a frame directly. It does not fit Householder parameters.
"""

import itertools
import math
from fractions import Fraction

import numpy as np


def positive_control56():
    head, tail = 4, (2, 1, 1)
    tails = list(itertools.product(*(range(n + 1) for n in tail)))
    states = [None] + [(d, h) for d in tails if sum(d) for h in range(head + 1)]
    index = {b: j for j, b in enumerate(states)}
    dimension = len(states)
    assert dimension == 56
    matrices = np.zeros((4, dimension, dimension), dtype=np.float64)
    supports = set()
    for j, state in enumerate(states):
        if state is None:
            column = [(0, 0, Fraction(1))]
        else:
            d, h = state
            remaining = sum(d)
            if remaining == 1:
                column = [(0, index[(d, h - 1)], Fraction(1))] if h else [
                    (d.index(1) + 1, 0, Fraction(1))]
            else:
                column = [(0, index[(d, h - 1)], Fraction(h, h + remaining - 1))] if h else []
                for label, count in enumerate(d, start=1):
                    if count:
                        successor = tuple(n - int(k == label - 1) for k, n in enumerate(d))
                        column.append((label, index[(successor, h)], Fraction(count, remaining)
                                       * Fraction(remaining - 1, h + remaining - 1)))
        assert sum((p for _, _, p in column), Fraction(0)) == 1
        support = {(label, destination) for label, destination, _ in column}
        assert supports.isdisjoint(support)
        supports.update(support)
        for label, destination, probability in column:
            matrices[label, destination, j] = math.sqrt(probability)
    initial_probabilities = [Fraction(0) for _ in states]
    for h in range(head + 1):
        initial_probabilities[index[(tail, h)]] = Fraction(math.comb(h + 3, 3), 70)
    assert sum(initial_probabilities, Fraction(0)) == 1
    initial = np.array([math.sqrt(p) for p in initial_probabilities])
    return matrices, initial
