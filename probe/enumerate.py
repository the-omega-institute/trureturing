"""Independent exhaustive probe: whole-word vincular containment, top first.

No imported probe implementation or external data. Run from the repository root.
"""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import json
import time


def contains(word, adjacency=(False, True), decreasing=False):
    for i, j, k in combinations(range(len(word)), 3):
        if adjacency[0] and j != i + 1:
            continue
        if adjacency[1] and k != j + 1:
            continue
        a, b, c = word[i], word[j], word[k]
        if (a > b > c) if decreasing else (a < b < c):
            return True
    return False


def stack_sort(word, adjacency=(False, True), decreasing=False):
    stack, output = [], []
    for x in word:
        while contains([x] + stack, adjacency, decreasing):
            output.append(stack.pop(0))
        stack.insert(0, x)
    return tuple(output + stack)


def digits(word):
    return ''.join(map(str, word))


def main():
    started = time.monotonic()
    anchors = {}
    for label, adjacency, expected in [
        ('123', (False, False), '463215'),
        ('_123_', (True, True), '263415'),
        ('_12_3', (True, False), '426315'),
        ('1_23_', (False, True), '632415'),
    ]:
        actual = digits(stack_sort((5, 1, 4, 3, 6, 2), adjacency))
        anchors[label] = {'expected': expected, 'actual': actual, 'pass': actual == expected}
    assert all(a['pass'] for a in anchors.values())
    summary = {'anchors': anchors, 'by_n': {}, 'preimages_765432819': [], 'preimages_n5': {}}
    for n in range(2, 10):
        start_n = time.monotonic()
        counts, downcounts = Counter(), Counter()
        for p in permutations(range(1, n + 1)):
            out = stack_sort(p)
            counts[out] += 1
            downcounts[stack_sort(p, decreasing=True)] += 1
            if n == 9 and out == (7, 6, 5, 4, 3, 2, 8, 1, 9):
                summary['preimages_765432819'].append(list(p))
            if n == 5 and out in [(3, 2, 4, 1, 5), (4, 3, 2, 1, 5)]:
                summary['preimages_n5'].setdefault(digits(out), []).append(list(p))
        histogram = Counter(counts.values())
        # Source quantifies over all S_n, including zero-preimage permutations.
        factorial = sum(counts.values())
        histogram[0] = factorial - len(counts)
        largest = max(counts.values())
        downlargest = max(downcounts.values())
        summary['by_n'][n] = {
            'input_count': factorial,
            'maximum_1_23': largest,
            'maximum_3_21': downlargest,
            'maximizers_1_23': [digits(p) for p in sorted(counts) if counts[p] == largest],
            'maximizers_3_21': [digits(p) for p in sorted(downcounts) if downcounts[p] == downlargest],
            'histogram': dict(sorted(histogram.items())),
            'conjectured_maximizer_fibre': counts[tuple(range(n - 1, 0, -1)) + (n,)],
            'seconds': time.monotonic() - start_n,
        }
        print(n, json.dumps(summary['by_n'][n]), flush=True)
    summary['fibre_765432819'] = len(summary['preimages_765432819'])
    summary['seconds'] = time.monotonic() - started
    Path('probe/enumeration.json').write_text(json.dumps(summary, indent=2) + '\n')
    assert summary['by_n'][9]['maximum_1_23'] > 128
    assert len([k for k in summary['by_n'][5]['histogram'] if k > 4]) >= 2


if __name__ == '__main__':
    main()
