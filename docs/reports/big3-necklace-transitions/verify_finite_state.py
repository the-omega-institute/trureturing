"""Rebuild one finite non-tree state from actual prefix reversals.

No solver, producer probe, saved cycle, or coset indices are consumed.
This finite reader does not prove the all-n Big-3 conjecture.
"""
import itertools
import json
import math
from collections import Counter
from pathlib import Path


def flip(p, length):
    return p[:length][::-1] + p[length:]


def orbit(start, lengths):
    seen, pending = {start}, [start]
    while pending:
        p = pending.pop()
        for length in lengths:
            q = flip(p, length)
            if q not in seen:
                seen.add(q)
                pending.append(q)
    return seen


def verify(data):
    n = data['n']
    vertices = set(itertools.permutations(range(n)))
    chosen, covered = [], set()
    for row in data['c_selected_E_representatives']:
        p = tuple(row)
        assert p in vertices
        block = orbit(p, (n - 1, n - 2))
        assert len(block) == 2 * (n - 1)
        assert not block & covered, 'Repeated selected E coset'
        chosen.append(block)
        covered.update(block)
    graph = {p: {flip(p, n), flip(p, n - 1)} for p in vertices}
    for p in covered:
        graph[p].remove(flip(p, n - 1))
        graph[p].add(flip(p, n - 2))
    assert all(len(neighbors) == 2 for neighbors in graph.values())
    assert all(p in graph[q] for p, neighbors in graph.items() for q in neighbors)
    assert all(flip(p, n) in graph[p] for p in vertices)
    start = min(vertices)
    p, previous, visited, edges = start, None, set(), Counter()
    while p not in visited:
        visited.add(p)
        q = min(q for q in graph[p] if q != previous)
        lengths = [k for k in (n, n - 1, n - 2) if flip(p, k) == q]
        assert len(lengths) == 1
        edges[lengths[0]] += 1
        previous, p = p, q
    assert p == start, 'The closing edge must return to the initial vertex'
    assert visited == vertices and len(visited) == math.factorial(n)
    return {'n': n, 'selected_E_cosets': len(chosen),
            'distinct_valid_vertices': len(visited), 'closed_cycle': True,
            'all_a_matching_edges_present': True,
            'edge_prefix_length_counts': dict(sorted(edges.items())),
            'scope': 'one finite state; no all-n claim'}


if __name__ == '__main__':
    path = Path(__file__).with_name('finite-state.json')
    print(json.dumps(verify(json.loads(path.read_text())), indent=2))
