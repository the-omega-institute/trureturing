"""Recompute the finite-prefix barrier from the actual Lean table literals.

Usage: python check_twenty_state_prefix.py path/to/GoldenBase4TwentyStatePrefixBarrier.lean
Python standard library only. Labels use integer square roots, never the
reference automaton. This checks a finite witness, not infinite correctness or
Lean elaboration. It intentionally requires the first error to be present.
"""
from __future__ import annotations
import ast
from bisect import bisect_right
from collections import deque
from hashlib import sha256
from math import isqrt
from pathlib import Path
import json
import re
import sys


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def vector(source: str, name: str) -> list[int]:
    match = re.search(r'\bdef\s+' + re.escape(name) + r'\s*:[\s\S]*?:=\s*!\[([^\]]*)\]', source)
    require(match is not None, 'missing table: ' + name)
    value = ast.literal_eval('[' + match.group(1) + ']')
    require(len(value) == 20 and all(type(v) is int for v in value), 'invalid table: ' + name)
    return value


def verify(source: str) -> dict:
    a, b, output = (vector(source, name) for name in ('zeroTarget', 'oneTarget', 'output'))
    require(all(0 <= q < 13 for q in a), 'zero target type')
    require(all(13 <= b[q] < 20 for q in range(13)), 'one target type')
    require(all(0 <= d < 4 for d in output), 'digit domain')
    require(a[0] == 0 and output[0] == 0, 'initial anchors')
    require('if q.val < 13 then .previousZero else .previousOne' in source, 'type guard')
    require('else if q.val < 13 then some (oneTarget q) else none' in source, 'partial-step guard')

    def run(word: list[int]) -> tuple[int, int] | None:
        q = 0
        for bit in word:
            if bit == 1 and q >= 13:
                return None
            q = (a if bit == 0 else b)[q]
        return q, output[q]

    fib = [1, 2]
    while fib[-1] <= 4 ** 1999:
        fib.append(fib[-1] + fib[-2])

    def word_of(q: int) -> list[int]:
        last = bisect_right(fib, q)
        remaining, bits = q, []
        for f in reversed(fib[:last]):
            bit = int(f <= remaining)
            bits.append(bit)
            remaining -= bit * f
        require(remaining == 0 and bits[0] == 1, 'greedy value')
        require(all(not (x and y) for x, y in zip(bits, bits[1:])), 'noncanonical word')
        # Independently evaluate using the exact two-register append recurrence.
        value = shifted = 0
        for bit in bits:
            value, shifted = shifted + bit, value + shifted + 2 * bit
        require(value == q, 'input value')
        return bits

    floor_phi = lambda q: (q + isqrt(5*q*q)) // 2
    errors = []
    zero_padding_checks = 0
    for n in range(2000):
        q = 4 ** n
        bits = word_of(q)
        result = run(bits)
        require(result is not None, 'undefined legal input')
        expected = floor_phi(4*q) - 4*floor_phi(q)
        if result[1] != expected:
            errors.append({'n': n, 'actual': result[1], 'expected': expected,
                           'state': result[0], 'word_length': len(bits)})
        if n < 79 or n == 367:
            for zeros in (1, 2, 7):
                require(run([0]*zeros + bits) == result, 'leading-zero change')
                zero_padding_checks += 1
    require(errors and errors[0] == {'n': 367, 'actual': 1, 'expected': 0,
                                   'state': 10, 'word_length': 1057}, 'wrong first failure')
    require([row['n'] for row in errors] == [367, 1164], 'changed finite regression')
    access = {0: []}
    queue = deque([0])
    while queue:
        q = queue.popleft()
        for bit in (0, 1):
            if bit and q >= 13:
                continue
            target = (a if bit == 0 else b)[q]
            if target not in access:
                access[target] = access[q] + [bit]
                queue.append(target)
    require(len(access) == 20, 'not all twenty states reachable')
    signatures = {(output[b[q]], a[b[q]]) for q in range(13)}
    require(len(signatures) == 7, 'different slot count')
    failure_word = ''.join(map(str, word_of(4 ** 367)))
    return {'status': 'PASS', 'states': 20, 'previous_zero_states': 13,
            'previous_one_states': 7, 'distinct_output_return_signatures': 7,
            'reachable_states': len(access), 'legal_transition_entries': 33,
            'initial_power_indices_correct': [0, 366], 'first_error': errors[0],
            'checked_power_indices': [0, 1999], 'errors_in_checked_range': errors,
            'leading_zero_checks': zero_padding_checks,
            'failure_word_sha256': sha256(failure_word.encode()).hexdigest(),
            'source_sha256': sha256(source.encode()).hexdigest(),
            'floating_point_used': False, 'reference_automaton_used_as_oracle': False,
            'lean_executed': False, 'all_powers_correct': False,
            'new_global_state_lower_bound': False}


def main() -> None:
    require(len(sys.argv) == 2, 'usage: check_twenty_state_prefix.py Lean_source')
    source = Path(sys.argv[1]).read_text()
    result = verify(source)
    mutations = {
        'changed_zero_transition': source.replace('![0,8,7,6,5,4,4,3,3,2,2,2,1,',
                                                 '![0,8,6,6,5,4,4,3,3,2,2,2,1,', 1),
        'changed_output': source.replace('![0,3,3,3,3,0,0,0,0,0,1,1,1,',
                                        '![0,3,3,3,3,0,0,0,0,0,0,1,1,', 1),
        'missing_type_guard': source.replace('if q.val < 13 then .previousZero',
                                            'if q.val < 14 then .previousZero', 1),
    }
    rejected = []
    for name, content in mutations.items():
        require(content != source, 'mutation did not apply')
        try:
            verify(content)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('mutation accepted: ' + name)
    result['rejected_mutations'] = rejected
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
