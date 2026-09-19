#!/usr/bin/env python3
"""Exact fixed-old-load optimizer for independently selected CRT labels.

The input scores[y][i][k] is an arbitrary integer/Fraction table. Every label
digit_modulus*c independently selects a residue. Empty old cylinders are
retained. All digit residues, including zero, participate. No monotonicity,
convexity, positive coefficients, or common-digit hypothesis is used.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction
from itertools import product
from math import gcd


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


class ExactSignedDigitDP:
    def __init__(self, old_points, cofactors=(1, 3, 5, 9, 15, 45),
                 digit_modulus=7, old_modulus=45):
        self.points = tuple(old_points)
        self.cofactors = tuple(cofactors)
        self.q = digit_modulus
        self.m = old_modulus
        require(type(self.q) is int and self.q > 0, 'positive digit modulus')
        require(type(self.m) is int and self.m > 0, 'positive old modulus')
        require(gcd(self.q, self.m) == 1, 'coprime CRT factors')
        require(self.points and len(set(self.points)) == len(self.points),
                'nonempty distinct old points')
        require(all(type(x) is int and 0 <= x < self.m for x in self.points),
                'old points in canonical residue range')
        require(self.cofactors and len(set(self.cofactors)) == len(self.cofactors),
                'nonempty distinct label cofactors')
        require(all(type(c) is int and c > 0 and self.m % c == 0
                    for c in self.cofactors), 'cofactors divide old modulus')
        self.n = len(self.cofactors)
        self.full = (1 << self.n) - 1
        # Keep one original residue for each distinct mask, including empty.
        self.cylinders = []
        for c in self.cofactors:
            masks = {}
            for b in range(c):
                mask = tuple(int(x % c == b) for x in self.points)
                masks.setdefault(mask, b)
            self.cylinders.append(tuple((b, mask) for mask, b in masks.items()))
        self.singleton = (self.cofactors.index(self.m)
                          if self.m in self.cofactors else None)
        self.singleton_bit = 0 if self.singleton is None else 1 << self.singleton
        self.empty_singleton = next((b for b, mask in self.cylinders[self.singleton]
                                     if not any(mask)), None) if self.singleton is not None else None
        self.subsets = [tuple(t for t in range(s + 1) if t & s == t)
                        for s in range(self.full + 1)]
        # Reuse these old-residue states for every digit and every score query.
        self.states = {}
        for s in range(self.full + 1):
            if s & self.singleton_bit:
                continue
            es = [e for e in range(self.n) if s >> e & 1]
            states = []
            for choices in product(*(self.cylinders[e] for e in es)):
                loads = tuple(sum(mask[i] for _, mask in choices)
                              for i in range(len(self.points)))
                residues = [None] * self.n
                for e, (b, _) in zip(es, choices):
                    residues[e] = b
                states.append((loads, tuple(residues)))
            self.states[s] = states

    def optimize(self, old_loads, scores):
        A = tuple(old_loads)
        require(len(A) == len(self.points) and
                all(type(a) is int and a >= 0 for a in A),
                'one nonnegative integer old load per row')
        require(len(scores) == self.q, 'one score block per digit including zero')
        for table in scores:
            require(len(table) == len(A), 'one score row per old point')
            for a, row in zip(A, table):
                require(len(row) > a + self.n, 'all possible loads represented')
                require(all(type(v) in (int, Fraction) for v in row),
                        'exact integer or Fraction scores only')
        blocks, witnesses = [], []
        for y in range(self.q):
            g = [None] * (self.full + 1)
            wr = [None] * (self.full + 1)
            table = scores[y]
            for s, states in self.states.items():
                best = best_singleton = None
                best_r = best_singleton_r = None
                for loads, residues in states:
                    k = tuple(a + b for a, b in zip(A, loads))
                    value = sum(table[i][ki] for i, ki in enumerate(k))
                    if best is None or value > best:
                        best, best_r = value, residues
                    if self.singleton is not None:
                        # An empty cylinder supplies gain 0 only if realizable.
                        gain = 0 if self.empty_singleton is not None else None
                        b45 = self.empty_singleton
                        for i, ki in enumerate(k):
                            delta = table[i][ki + 1] - table[i][ki]
                            if gain is None or delta > gain:
                                gain, b45 = delta, self.points[i]
                        candidate = value + gain
                        if best_singleton is None or candidate > best_singleton:
                            rr = list(residues)
                            rr[self.singleton] = b45
                            best_singleton, best_singleton_r = candidate, tuple(rr)
                g[s], wr[s] = best, best_r
                if self.singleton is not None:
                    g[s | self.singleton_bit] = best_singleton
                    wr[s | self.singleton_bit] = best_singleton_r
            blocks.append(g)
            witnesses.append(wr)
        previous = [None] * (self.full + 1)
        previous[0] = 0
        trace = []
        for y in range(self.q):
            current = [None] * (self.full + 1)
            selected = [None] * (self.full + 1)
            for s, subs in enumerate(self.subsets):
                for t in subs:
                    if previous[s ^ t] is None:
                        continue
                    candidate = previous[s ^ t] + blocks[y][t]
                    if current[s] is None or candidate > current[s]:
                        current[s], selected[s] = candidate, t
            previous = current
            trace.append(selected)
        partition, labels, s = [0] * self.q, [None] * self.n, self.full
        for y in reversed(range(self.q)):
            t = trace[y][s]
            require(t is not None, 'reachable traceback')
            partition[y] = t
            for e, c in enumerate(self.cofactors):
                if t >> e & 1:
                    b = witnesses[y][t][e]
                    residue = b + c * (((y - b) * pow(c, -1, self.q)) % self.q)
                    labels[e] = {'cofactor': c, 'modulus': self.q * c,
                                 'old_residue': b, 'digit': y, 'residue': residue}
            s ^= t
        require(s == 0 and all(r is not None for r in labels), 'complete partition')
        answer = previous[self.full]
        loads = [[A[i] + sum(int(x % c == r['old_residue'] and y == r['digit'])
                            for c, r in zip(self.cofactors, labels))
                  for i, x in enumerate(self.points)] for y in range(self.q)]
        replay = sum(scores[y][i][loads[y][i]]
                     for y in range(self.q) for i in range(len(A)))
        require(replay == answer, 'direct optimizing witness replay')
        # Under a common-digit restriction all other digit blocks are empty.
        common = max(blocks[y][self.full] +
                     sum(blocks[z][0] for z in range(self.q) if z != y)
                     for y in range(self.q))
        return {'value': answer, 'common_digit_value': common, 'labels': labels,
                'digit_partition': partition, 'load_by_digit': loads,
                'block_values': blocks,
                'cylinder_counts': [len(cy) for cy in self.cylinders],
                'old_states_without_singleton': sum(map(len, self.states.values())),
                'subset_transitions': self.q * 3 ** self.n}
