"""Independent exhaustive experiment for arXiv:2411.11914v2, Conjecture 6.2.

Only this seat's code. No imported stack-sorting or orchestrator implementation.
Run: python3 probe/check_syy.py > probe/python_results.json
"""
import itertools
import json
import math
import time


def valley_runs(word):
    runs = []
    for i, value in enumerate(word):
        # The definition itself, without relying on a running-minimum invariant.
        if all(value < earlier for earlier in word[:i]):
            runs.append([])
        runs[-1].append(value)
    return tuple(tuple(run) for run in runs)


def reverse_runs(word):
    return tuple(value for run in valley_runs(word) for value in reversed(run))


def west(word):
    stack, output = [], []
    for value in word:
        while stack and stack[-1] < value:
            output.append(stack.pop())
        stack.append(value)
    while stack:
        output.append(stack.pop())
    return tuple(output)


def machine(word):
    return west(reverse_runs(word))


def inspect(n):
    words = list(itertools.permutations(range(1, n + 1)))
    edge = {word: machine(word) for word in words}
    fixed = sum(word == target for word, target in edge.items())
    sortable = sum(target == tuple(range(1, n + 1)) for target in edge.values())
    violations = [dict(word=word, image=target) for word, target in edge.items()
                  if word != target and not word[::-1] < target[::-1]]
    assert all(sorted(word) == sorted(target) for word, target in edge.items())
    # Independent functional-graph traversal, not inference from the potential.
    completed = set()
    nontrivial_cycles = []
    for initial in words:
        path, position = [], {}
        current = initial
        while current not in completed and current not in position:
            position[current] = len(path)
            path.append(current)
            current = edge[current]
        if current in position:
            cycle = path[position[current]:]
            if len(cycle) >= 2:
                nontrivial_cycles.append(cycle)
        completed.update(path)
    assert len(completed) == math.factorial(n)
    return dict(n=n, permutations=len(words), fixed_points=fixed, sortable=sortable,
                potential_violations=violations, nontrivial_cycles=nontrivial_cycles)


if __name__ == '__main__':
    started = time.monotonic()
    assert valley_runs((2, 4, 3, 1, 5)) == ((2, 4, 3), (1, 5))
    assert west((3, 1, 2, 4)) == (1, 2, 3, 4)
    rows = [inspect(n) for n in range(1, 9)]
    observed_fixed = [row['fixed_points'] for row in rows]
    expected_fixed = [1, 1, 2, 4, 9, 23, 65, 199]
    observed_sortable = [row['sortable'] for row in rows]
    expected_sortable = [2 ** (n - 1) for n in range(1, 9)]
    results = dict(range='all S_n, 1 <= n <= 8', rows=rows,
                   anchors=dict(fixed_observed=observed_fixed,
                                fixed_expected=expected_fixed,
                                fixed_match=observed_fixed == expected_fixed,
                                sortable_observed=observed_sortable,
                                sortable_expected=expected_sortable,
                                sortable_match=observed_sortable == expected_sortable),
                   nontrivial_cycle_count=sum(len(r['nontrivial_cycles']) for r in rows),
                   potential_violation_count=sum(len(r['potential_violations']) for r in rows),
                   wall_s=time.monotonic() - started)
    print(json.dumps(results, indent=2))
