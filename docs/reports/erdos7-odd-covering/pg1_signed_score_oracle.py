#!/usr/bin/env python3
"""Exact PG1 twelve-label optimizer for arbitrary integer point-score tables.

Input JSON contains either point_scores[75][13], in source PG1.points order,
or scores[7][16][13], in digit then PG1.old_points order. Columns give the
score at load B=0,...,12. Absent physical points have zero score. An optional
positive integer denominator supplies the common score denominator.

The maximum includes all 11808 realizable old A loads, empty residue classes,
and all seven independent digits, including zero. Scores need not be positive,
increasing, or convex. Outer auxiliary profiles and heights are not quantified.

The standard-library driver compiles adjacent pg1_signed_score_oracle.cpp into
a temporary directory using an available C++ compiler. --binary can reuse an
existing executable. No generated executable, raw input, or all-A value table
is retained. Each global winner is checked with the original Python optimizer
and by literal evaluation of all twelve original labels at all 75 points.
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
import time

HERE = Path(__file__).resolve().parent
DEFAULT_SOURCE = HERE / 'certificates/mod3_conditioned_geometry_certificate.json'
_spec = spec_from_file_location('exact_signed_digit_dp', HERE / 'exact_signed_digit_dp.py')
_dp = module_from_spec(_spec)
_spec.loader.exec_module(_dp)
require = _dp.require


class Oracle:
    """Use as a context manager; one compiled binary serves repeated queries."""
    def __init__(self, source=DEFAULT_SOURCE, binary=None):
        raw = read_artifact_bytes(Path(source))
        self.source_sha256 = sha256(raw).hexdigest()
        self.case = next(c for c in json.loads(raw)['cases'] if c['name'] == 'PG1')
        self.points = self.case['points']
        self.xs = self.case['old_points']
        require(self.points == [t for t in range(315)
                                if all(t % d != a for d, a in self.case['family'])],
                'literal PG1 remaining carrier')
        require(len(self.points) == 75 and len(self.xs) == 16 and
                self.xs == sorted({t % 45 for t in self.points}), 'PG1 carrier dimensions')
        self.ri = {x: i for i, x in enumerate(self.xs)}
        self.present = {(t % 7, self.ri[t % 45]) for t in self.points}
        self.dp = _dp.ExactSignedDigitDP(self.xs)
        require(self.dp.singleton == 5 and self.dp.empty_singleton is not None,
                'legally realizable empty singleton')
        old = {}
        for choices in product(*self.dp.cylinders):
            A = tuple(sum(mask[i] for _, mask in choices) for i in range(16))
            old.setdefault(A, tuple(a for a, _ in choices))
        self.old = sorted(old.items())
        self.state_count = sum(map(len, self.dp.states.values()))
        require(len(self.old) == 11808 and self.state_count == 3024,
                'complete old-load and subset-state counts')
        domain = []
        for mask, states in self.dp.states.items():
            for loads, _ in states:
                domain.append(' '.join(map(str, (mask, *loads))) + '\n')
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
            require(compiler is not None, 'an available C++17 compiler is required')
            self._temporary_binary = TemporaryDirectory(prefix='pg1-score-oracle-build-')
            self.binary = Path(self._temporary_binary.name) / 'oracle'
            try:
                subprocess.run([compiler, '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror',
                                str(HERE / 'pg1_signed_score_oracle.cpp'), '-o', str(self.binary)],
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
        require(len(rows) == 75, 'one score row per PG1 physical point')
        scores = [[[0] * 13 for _ in self.xs] for _ in range(7)]
        for t, row in zip(self.points, rows):
            scores[t % 7][self.ri[t % 45]] = row
        return scores

    def optimize(self, scores, denominator=1, check_indices=()):
        require(type(denominator) is int and denominator > 0, 'positive integer denominator')
        require(len(scores) == 7 and all(len(plane) == 16 for plane in scores),
                'seven digit planes and sixteen old rows')
        require(all(len(row) == 13 and all(type(v) is int for v in row)
                    for plane in scores for row in plane), 'integer scores at all loads 0 through 12')
        require(all(not any(scores[y][i]) for y in range(7) for i in range(16)
                    if (y, i) not in self.present), 'absent physical points have zero score')
        check_indices = tuple(sorted(set(check_indices)))
        require(all(type(i) is int and 0 <= i < len(self.old) for i in check_indices),
                'valid optional Python comparison indices')
        bound = sum(max(map(abs, row)) for plane in scores for row in plane)
        # A block/partial DP value is bounded by the corresponding sum of row
        # bounds; gain differences and the common-digit baseline use <= 4x.
        require(4 * bound < 2**61, 'every signed int64 score and DP intermediate fits')
        score_text = ''.join(' '.join(map(str, row)) + '\n' for plane in scores for row in plane)
        input_text = f'{len(self.old)} {self.state_count}\n' + score_text + self.domain
        with TemporaryDirectory(prefix='pg1-score-oracle-query-') as tmp:
            input_path = Path(tmp) / 'input.txt'
            values_path = Path(tmp) / 'values.txt'
            write_certificate_text(input_path, input_text)
            completed = subprocess.run([str(self.binary), str(input_path), str(values_path)],
                                       check=True, capture_output=True, text=True)
            runtime = json.loads(completed.stdout)
            values = [tuple(map(int, line.split())) for line in read_artifact_text(values_path).splitlines()]
        require(len(values) == 11808 and all(len(row) == 3 for row in values) and
                [row[0] for row in values] == list(range(11808)), 'complete ordered all-A result')
        winner, maximum, common_at_winner = max(values, key=lambda row: row[1])
        common_winner, _, common_maximum = max(values, key=lambda row: row[2])
        require(runtime['queries'] == 11808 and runtime['maximum_numerator'] == maximum and
                runtime['maximizing_A_index'] == winner, 'C++ summary agrees with complete values')
        self.last_seconds = runtime['seconds']
        checks = []
        replay_cache = {}
        for i in sorted(set(check_indices) | {winner, common_winner}):
            replay = self.dp.optimize(self.old[i][0], scores)
            require((replay['value'], replay['common_digit_value']) == values[i][1:],
                    f'C++ and Python equality at old A index {i}')
            replay_cache[i] = replay
            if i in check_indices:
                checks.append({'A_index': i, 'maximum_numerator': replay['value'],
                               'common_digit_maximum_numerator': replay['common_digit_value']})
        replay = replay_cache[winner]
        A, old_residues = self.old[winner]
        labels = [{'modulus': c, 'residue': a} for c, a in zip(self.dp.cofactors, old_residues)]
        labels += replay['labels']
        loads = [sum(t % label['modulus'] == label['residue'] for label in labels) for t in self.points]
        literal = sum(scores[t % 7][self.ri[t % 45]][b] for t, b in zip(self.points, loads))
        require(literal == maximum, 'literal twelve-label score on all 75 physical points')
        return {'scope': 'exact maximum of the supplied point-score table over the original twelve low labels on PG1; no quantification over outer auxiliary profiles or heights',
                'source_sha256': self.source_sha256, 'domain_sha256': self.domain_sha256,
                'score_sha256': sha256(score_text.encode()).hexdigest(),
                'old_A_count': 11808, 'old_subset_state_count': 3024,
                'score_abs_bound': bound, 'int64_guard': '4*score_abs_bound < 2^61',
                'maximum_numerator': maximum, 'denominator': denominator,
                'maximum': str(Fraction(maximum, denominator)),
                'common_digit_maximum_numerator': common_maximum,
                'common_digit_maximum': str(Fraction(common_maximum, denominator)),
                'common_maximizing_A_index': common_winner,
                'maximizing_A_index': winner, 'old_points': self.xs,
                'maximizing_A': list(A), 'old_residues': list(old_residues),
                'twelve_labels': labels, 'digit_partition': replay['digit_partition'],
                'points': self.points, 'B_loads': loads, 'python_comparisons': checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('score_file', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--source', type=Path, default=DEFAULT_SOURCE)
    parser.add_argument('--binary', type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    payload = json.loads(read_artifact_text(args.score_file))
    with Oracle(args.source, args.binary) as oracle:
        result = oracle.optimize(oracle.score_tensor(payload), payload.get('denominator', 1))
        solve_seconds = oracle.last_seconds
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        write_certificate_text(args.output, text)
        print(json.dumps({'output': str(args.output), 'maximum': result['maximum'],
                          'solve_seconds': solve_seconds, 'total_seconds': time.monotonic() - started}))
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
