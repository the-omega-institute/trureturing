#!/usr/bin/env python3
"""Exact PG1 signed-score optimizer for weighted CRT labels.

The JSON input specifies six nonnegative integer digit_weights, one for each
cofactor (1,3,5,9,15,45), and an old_labels list. Each old label has cofactor
and weight, plus an optional fixed residue; otherwise every residue is free.
Duplicate old cofactors represent separate auxiliary roles. No pooling of
distinct labels is performed here. In particular an original mod9 label can
remain fixed while another mod9 auxiliary label is independently free.

point_scores contains one integer row per actual PG1 point, or scores has
shape [7][16][maxload+1]. maxload is computed from the complete old domain and
the sum of the six weights. Signed, nonmonotone and nonconvex scores are
allowed, but they must depend only on the resulting weighted total load.
This does not optimize an objective retaining separate original and auxiliary
loads. All original residue choices, empty cylinders, and digit zero remain.

The Python replay is exact and supports Fraction scores. The faster C++
oracle accepts integer scores with an optional common positive denominator.
Executables and complete all-A outputs are temporary. No physical height
or outer auxiliary-profile quantifier is inferred from an oracle query.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
DEFAULT_SOURCE = HERE / 'certificates/mod3_conditioned_geometry_certificate.json'
COFACTORS = (1, 3, 5, 9, 15, 45)
_spec = spec_from_file_location('weighted_base_dp', HERE / 'exact_signed_digit_dp.py')
_base = module_from_spec(_spec)
_spec.loader.exec_module(_base)
require = _base.require


class WeightedDigitDP(_base.ExactSignedDigitDP):
    """The existing residue domain with true weighted increments per label."""
    def __init__(self, old_points, weights):
        super().__init__(old_points)
        self.weights = tuple(weights)
        require(len(self.weights) == self.n == 6 and
                all(type(u) is int and u >= 0 for u in self.weights),
                'six nonnegative integer label weights')
        require(self.singleton == 5 and self.empty_singleton is not None,
                'PG1 permits an empty cofactor45 cylinder')
        self.states = {}
        for s in range(32):
            es = [e for e in range(5) if s >> e & 1]
            states = []
            # Do not deduplicate by the former unit loads: unequal weighted
            # loads must retain their distinct labeled residue choices.
            for choices in product(*(self.cylinders[e] for e in es)):
                loads = tuple(sum(self.weights[e] * mask[i]
                                  for e, (_, mask) in zip(es, choices))
                              for i in range(len(self.points)))
                residues = [None] * 6
                for e, (a, _) in zip(es, choices):
                    residues[e] = a
                states.append((loads, tuple(residues)))
            self.states[s] = states

    def optimize(self, old_loads, scores):
        A = tuple(old_loads)
        require(len(A) == len(self.points) and
                all(type(a) is int and a >= 0 for a in A), 'valid old row loads')
        require(len(scores) == 7 and all(len(t) == len(A) for t in scores),
                'one score row per digit and old point')
        require(all(len(row) > a + sum(self.weights) and
                    all(type(v) in (int, Fraction) for v in row)
                    for table in scores for a, row in zip(A, table)),
                'exact scores cover all weighted loads')
        blocks, witnesses = [], []
        for y in range(7):
            best, wr = [None] * 64, [None] * 64
            for s, states in self.states.items():
                for loads, residues in states:
                    k = [a+b for a, b in zip(A, loads)]
                    value = sum(scores[y][i][ki] for i, ki in enumerate(k))
                    if best[s] is None or value > best[s]:
                        best[s], wr[s] = value, residues
                    gains = [(0, self.empty_singleton)]
                    gains += [(scores[y][i][ki+self.weights[5]]-scores[y][i][ki], x)
                              for i, (ki, x) in enumerate(zip(k, self.points))]
                    gain, a45 = max(gains, key=lambda pair: pair[0])
                    t = s | 32
                    if best[t] is None or value+gain > best[t]:
                        rr = list(residues)
                        rr[5] = a45
                        best[t], wr[t] = value+gain, tuple(rr)
            blocks.append(best)
            witnesses.append(wr)
        previous = [None] * 64
        previous[0] = 0
        trace = []
        for y in range(7):
            current, choices = [None] * 64, [None] * 64
            for s in range(64):
                for t in self.subsets[s]:
                    if previous[s ^ t] is None:
                        continue
                    value = previous[s ^ t] + blocks[y][t]
                    if current[s] is None or value > current[s]:
                        current[s], choices[s] = value, t
            previous = current
            trace.append(choices)
        labels, partitions, s = [], [0] * 7, 63
        for y in range(6, -1, -1):
            t = trace[y][s]
            partitions[y] = t
            for e, c in enumerate(self.cofactors):
                if t >> e & 1:
                    a = witnesses[y][t][e]
                    residue = a + c * (((y-a) * pow(c, -1, 7)) % 7)
                    labels.append({'cofactor': c, 'modulus': 7*c, 'weight': self.weights[e],
                                   'old_residue': a, 'digit': y, 'residue': residue})
            s ^= t
        require(s == 0 and len(labels) == 6, 'complete independent digit partition')
        labels.sort(key=lambda r: r['cofactor'])
        loads = [[A[i] + sum(r['weight'] * int(x % r['cofactor'] == r['old_residue']
                                             and y == r['digit']) for r in labels)
                  for i, x in enumerate(self.points)] for y in range(7)]
        require(sum(scores[y][i][loads[y][i]] for y in range(7) for i in range(len(A)))
                == previous[63], 'literal weighted Python traceback')
        common = max(blocks[y][63] + sum(blocks[z][0] for z in range(7) if z != y)
                     for y in range(7))
        return {'value': previous[63], 'common_digit_value': common, 'labels': labels,
                'digit_partition': partitions, 'load_by_digit': loads}


class Oracle:
    def __init__(self, digit_weights, old_labels, source=DEFAULT_SOURCE, binary=None):
        raw = read_artifact_bytes(Path(source))
        self.source_sha256 = sha256(raw).hexdigest()
        self.case = next(c for c in json.loads(raw)['cases'] if c['name'] == 'PG1')
        self.points, self.xs = self.case['points'], self.case['old_points']
        require(self.points == [t for t in range(315)
                                if all(t % d != a for d, a in self.case['family'])],
                'literal actual PG1 survivor carrier')
        require(len(self.points) == 75 and len(self.xs) == 16 and
                self.xs == sorted({t % 45 for t in self.points}), 'PG1 carrier dimensions')
        self.ri = {x: i for i, x in enumerate(self.xs)}
        self.present = {(t % 7, self.ri[t % 45]) for t in self.points}
        self.dp = WeightedDigitDP(self.xs, digit_weights)
        self.old_labels = [dict(r) for r in old_labels]
        choices = []
        for r in self.old_labels:
            c, weight = r['cofactor'], r['weight']
            require(type(c) is int and c in COFACTORS and type(weight) is int and weight >= 0,
                    'valid nonnegative weighted old cofactor')
            if 'residue' in r:
                a = r['residue']
                require(type(a) is int and 0 <= a < c, 'fixed original residue is canonical')
                choices.append(((a, tuple(int(x % c == a) for x in self.xs)),))
            else:
                choices.append(self.dp.cylinders[COFACTORS.index(c)])
        old = {}
        for realization in product(*choices):
            A = tuple(sum(r['weight'] * mask[i] for r, (_, mask) in zip(self.old_labels, realization))
                      for i in range(16))
            old.setdefault(A, tuple(a for a, _ in realization))
        self.old = sorted(old.items())
        self.maxload = max(max(A) for A, _ in self.old) + sum(self.dp.weights)
        require(self.maxload < 2**31-1, 'weighted load indices fit the C++ representation')
        self.state_count = sum(map(len, self.dp.states.values()))
        require(self.state_count == 3024, 'complete labeled weighted state domain')
        domain = []
        for s, states in self.dp.states.items():
            for loads, _ in states:
                domain.append(' '.join(map(str, (s, *loads))) + '\n')
        for A, _ in self.old:
            domain.append(' '.join(map(str, A)) + '\n')
        self.domain = ''.join(domain)
        self.domain_sha256 = sha256(self.domain.encode()).hexdigest()
        self._temporary_binary = None
        self.last_seconds = None
        if binary is not None:
            self.binary = Path(binary).resolve()
            require(self.binary.is_file(), 'supplied C++ executable exists')
        else:
            compiler = next((path for name in ('clang++', 'g++', 'c++')
                             if (path := shutil.which(name)) is not None), None)
            require(compiler is not None, 'available C++17 compiler')
            self._temporary_binary = TemporaryDirectory(prefix='pg1-weighted-oracle-build-')
            self.binary = Path(self._temporary_binary.name) / 'oracle'
            try:
                subprocess.run([compiler, '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror',
                                str(HERE / 'pg1_weighted_score_oracle.cpp'), '-o', str(self.binary)],
                               check=True, capture_output=True, text=True)
            except BaseException:
                self.close()
                raise

    def close(self):
        if self._temporary_binary is not None:
            self._temporary_binary.cleanup()
            self._temporary_binary = None

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def score_tensor(self, payload):
        require(('scores' in payload) != ('point_scores' in payload), 'exactly one score layout')
        if 'scores' in payload:
            return payload['scores']
        rows = payload['point_scores']
        require(len(rows) == 75, 'one score row per actual PG1 point')
        scores = [[[0] * (self.maxload+1) for _ in self.xs] for _ in range(7)]
        for t, row in zip(self.points, rows):
            scores[t % 7][self.ri[t % 45]] = row
        return scores

    def optimize(self, scores, denominator=1, check_indices=()):
        require(type(denominator) is int and denominator > 0, 'positive integer denominator')
        require(len(scores) == 7 and all(len(plane) == 16 for plane in scores),
                'seven digit planes and sixteen old rows')
        require(all(len(row) == self.maxload+1 and all(type(v) is int for v in row)
                    for plane in scores for row in plane), 'integer scores cover the dynamic total load')
        require(all(not any(scores[y][i]) for y in range(7) for i in range(16)
                    if (y, i) not in self.present), 'absent physical points have zero score')
        check_indices = tuple(sorted(set(check_indices)))
        require(all(type(i) is int and 0 <= i < len(self.old) for i in check_indices),
                'valid additional Python comparison indices')
        bound = sum(max(map(abs, row)) for plane in scores for row in plane)
        require(4*bound < 2**61, 'all signed64 scores, differences and partial DP values fit')
        score_text = ''.join(' '.join(map(str, row)) + '\n' for plane in scores for row in plane)
        header = f'{len(self.old)} {self.state_count} {self.maxload} {self.dp.weights[5]}\n'
        with TemporaryDirectory(prefix='pg1-weighted-oracle-query-') as tmp:
            input_path, output_path = Path(tmp)/'input.txt', Path(tmp)/'values.txt'
            write_certificate_text(input_path, header+score_text+self.domain)
            completed = subprocess.run([str(self.binary), str(input_path), str(output_path)],
                                       check=True, capture_output=True, text=True)
            runtime = json.loads(completed.stdout)
            values = [tuple(map(int, line.split())) for line in read_artifact_text(output_path).splitlines()]
        require(len(values) == len(self.old) and all(len(row) == 3 for row in values) and
                [row[0] for row in values] == list(range(len(self.old))), 'complete ordered old-A output')
        winner, maximum, _ = max(values, key=lambda r: r[1])
        common_winner, _, common = max(values, key=lambda r: r[2])
        require(runtime['queries'] == len(self.old) and runtime['maximum_numerator'] == maximum and
                runtime['maximizing_A_index'] == winner, 'summary agrees with every old-A result')
        self.last_seconds = runtime['seconds']
        replays = {}
        for i in sorted(set(check_indices) | {winner, common_winner}):
            replay = self.dp.optimize(self.old[i][0], scores)
            require((replay['value'], replay['common_digit_value']) == values[i][1:],
                    'independent Python weighted DP comparison')
            replays[i] = replay
        A, residues = self.old[winner]
        labels = [{'modulus': r['cofactor'], 'residue': a, 'weight': r['weight'],
                   'role': r.get('role', 'old')} for r, a in zip(self.old_labels, residues)]
        labels += replays[winner]['labels']
        loads = [sum(r['weight'] * int(t % r['modulus'] == r['residue']) for r in labels)
                 for t in self.points]
        require(sum(scores[t % 7][self.ri[t % 45]][b] for t, b in zip(self.points, loads)) == maximum,
                'literal weighted-label winner on all75 actual points')
        return {'scope': 'Exact complete weighted-label maximum for this explicit old-label domain and scalar total-load score table; no unsupplied auxiliary or physical-height quantifier.',
                'source_sha256': self.source_sha256, 'domain_sha256': self.domain_sha256,
                'score_sha256': sha256(score_text.encode()).hexdigest(),
                'old_labels': self.old_labels, 'digit_weights': list(self.dp.weights),
                'old_A_count': len(self.old), 'weighted_subset_states': self.state_count,
                'maximum_load': self.maxload, 'score_abs_bound': bound,
                'int64_guard': '4*score_abs_bound < 2^61',
                'maximum_numerator': maximum, 'denominator': denominator,
                'maximum': str(Fraction(maximum, denominator)),
                'common_digit_maximum_numerator': common,
                'maximizing_A_index': winner, 'common_maximizing_A_index': common_winner,
                'maximizing_A': list(A), 'weighted_labels': labels, 'actual_point_loads': loads,
                'digit_partition': replays[winner]['digit_partition'],
                'python_comparisons': [{'A_index': i, 'maximum_numerator': replays[i]['value'],
                                       'common_digit_maximum_numerator': replays[i]['common_digit_value']}
                                      for i in check_indices]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('score_file', type=Path)
    parser.add_argument('--source', type=Path, default=DEFAULT_SOURCE)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.loads(read_artifact_text(args.score_file))
    with Oracle(payload['digit_weights'], payload['old_labels'], args.source, args.binary) as oracle:
        result = oracle.optimize(oracle.score_tensor(payload), payload.get('denominator', 1))
        seconds = oracle.last_seconds
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        write_certificate_text(args.output, output)
        print(json.dumps({'output': str(args.output), 'maximum': result['maximum'], 'seconds': seconds}))
    else:
        print(output, end='')


if __name__ == '__main__':
    main()
