#!/usr/bin/env python3
"""Exact two-row-class envelope for independent prime-power layouts.

The cap arrays must come from one supported probability in an application.
This module maximizes an upper envelope, not the actual layout moment.
No nonstandard packages are used. See report 396 for the source theorem.
"""

from fractions import Fraction as F
from itertools import product
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _caps(plain, first, second):
    arrays = tuple(tuple(a) for a in (plain, first, second))
    require(len(arrays[0]) > 0, "cap arrays must be nonempty")
    require(len({len(a) for a in arrays}) == 1, "cap lengths differ")
    for array in arrays:
        require(all(type(x) in (int, F) and x >= 0 for x in array),
                "caps must be nonnegative exact integers or Fractions")
    return tuple(tuple(F(x) for x in a) for a in arrays)


def layout_envelope(plain, first, second):
    """Return (exact maximum, maximizing F/W word) in quadratic time.

    State is the number of earlier F choices. Ties are resolved
    deterministically. Backpointers avoid copying full words per state.
    """
    plain, first, second = _caps(plain, first, second)
    scores = {0: F(0)}
    parents = []
    for j, (m, f, w) in enumerate(zip(plain, first, second)):
        next_scores = {}
        parent = {}
        for u, score in scores.items():
            v = j - u
            base = score + (2 * j + 1) * m
            candidates = (
                (u + 1, base + (2 * j + 3 + 4 * u) * f + 2 * v * w, "F"),
                (u, base + 2 * u * f + (2 * j + 3 + 4 * v) * w, "W"),
            )
            for target, value, color in candidates:
                if target not in next_scores or value > next_scores[target]:
                    next_scores[target] = value
                    parent[target] = (u, color)
        scores = next_scores
        parents.append(parent)
    u = max(scores, key=scores.get)
    maximum = scores[u]
    word = []
    for parent in reversed(parents):
        u, color = parent[u]
        word.append(color)
    return maximum, "".join(reversed(word))


def ordered_pair_envelope(word, plain, first, second):
    """Independent oracle: enumerate all original ordered P/Q labels."""
    plain, first, second = _caps(plain, first, second)
    require(len(word) == len(plain) and set(word) <= {"F", "W"},
            "word must assign F/W to every depth")
    bounds = {"F": first, "W": second}
    labels = tuple(product(("P", "Q"), range(len(word))))
    value = F(0)
    for (kind_i, i), (kind_j, j) in product(labels, repeat=2):
        depth = max(i, j)
        if kind_i == kind_j == "P":
            value += plain[depth]
        elif kind_i == "P":
            value += bounds[word[j]][depth]
        elif kind_j == "P":
            value += bounds[word[i]][depth]
        elif word[i] == word[j]:
            value += bounds[word[i]][depth]
    return value


def heavy_row_caps(height):
    require(type(height) is int and height >= 0, "height must be nonnegative")
    plain = tuple((F(1, 3**j) + F(1, 5**j)) / 2 for j in range(height + 1))
    first = tuple(F(1, 2 * 5**j) for j in range(height + 1))
    second = tuple(F(1, 3 * 3**j) for j in range(height + 1))
    return plain, first, second


def finite_bound(height):
    require(type(height) is int and height >= 2, "height must be at least two")
    return F(3319, 675) + sum(
        ((2 * j + 1) * (F(3, 2 * 3**j) + F(1, 2 * 5**j))
         for j in range(3, height + 1)), F(0))


def geometric_tail(base, start):
    """Sum (2j+1)/base**j for all j>=start."""
    require(type(base) is int and base > 1, "base must exceed one")
    require(type(start) is int and start >= 0, "start must be nonnegative")
    z = F(1, base)
    return z**start * (F(2 * start + 1) / (1 - z) + 2 * z / (1 - z)**2)


def verify():
    expected = {
        "FFF": F(439, 90), "FFW": F(3319, 675),
        "FWF": F(3191, 675), "FWW": F(6589, 1350),
        "WFF": F(2831, 675), "WFW": F(5869, 1350),
        "WWF": F(6029, 1350), "WWW": F(71, 15),
    }
    caps = heavy_row_caps(2)
    for word, value in expected.items():
        require(ordered_pair_envelope(word, *caps) == value, "three-depth table")
    maximum, word = layout_envelope(*caps)
    require((maximum, word) == (F(3319, 675), "FFW"), "three-depth maximum")
    require(F(46, 9) - maximum == F(131, 675), "initial gap")
    require(layout_envelope(*heavy_row_caps(1))[0] == F(21, 5), "root boundary")

    # Asymmetric nonmonotone arrays exercise the reusable recurrence;
    # monotonicity is not required for equality of these two computations.
    cases = [heavy_row_caps(k) for k in range(7)]
    cases += [
        ((1, F(2, 7), F(1, 2)), (F(2, 3), F(3, 5), 0),
         (F(1, 4), 0, F(2, 7))),
        ((0, 0, 0), (0, 0, 0), (0, 0, 0)),
    ]
    words_checked = 0
    for arrays in cases:
        values = {"".join(w): ordered_pair_envelope("".join(w), *arrays)
                  for w in product("FW", repeat=len(arrays[0]))}
        value, witness = layout_envelope(*arrays)
        require(value == max(values.values()) == values[witness], "DP vs pair oracle")
        words_checked += len(values)

    for k in range(2, 33):
        target = 2 * (3 - F(k + 2, 3**k))
        gap = F(131, 675) + sum(
            (F(2 * j + 1, 2) * (F(1, 3**j) - F(1, 5**j))
             for j in range(3, k + 1)), F(0))
        require(target - finite_bound(k) == gap > 0, "finite gap identity")
        require(layout_envelope(*heavy_row_caps(k))[0] <= finite_bound(k),
                "finite tail dominates full envelope")
    limit = F(3319, 675) + F(3, 2) * geometric_tail(3, 3) + geometric_tail(5, 3) / 2
    require(limit == F(60709, 10800), "infinite bound")
    require(6 - limit == F(4091, 10800), "infinite gap")
    for base in (3, 5):
        for start in range(8):
            require(geometric_tail(base, start) - geometric_tail(base, start + 1)
                    == F(2 * start + 1, base**start), "tail recurrence")
    invalid = [([], [], []), ([1], [1, 2], [1]), ([1.0], [1], [1]),
               ([1], [-1], [1]), ([True], [1], [1])]
    for arrays in invalid:
        try:
            layout_envelope(*arrays)
        except ValueError:
            pass
        else:
            raise ValueError("invalid cap input accepted")
    return {
        "three_depth_values": {key: str(value) for key, value in expected.items()},
        "maximum_envelope": str(maximum), "maximizing_class_word": word,
        "independent_words_checked": words_checked,
        "finite_identity_heights": [2, 32], "limit_bound": str(limit),
        "scope": "exact envelope arithmetic; all-height proof is in report 396",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
