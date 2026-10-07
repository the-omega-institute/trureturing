"""Read a finite Big-3 certificate using literal prefix reversals only.

No producer imports, solver, saved adjacency or permutation IDs are consumed.
This establishes native finite evidence, not Lean or the all-n conjecture.
"""
import hashlib
import itertools
import json
import math
from collections import Counter
from pathlib import Path


def flip(vertex, length):
    return vertex[:length][::-1] + vertex[length:]


def polygon(start, lengths):
    vertices = [start]
    for length in lengths:
        vertices.append(flip(vertices[-1], length))
    assert vertices[-1] == start
    assert len(set(vertices[:-1])) == len(lengths)
    return vertices


def canonical_circle(values):
    values = tuple(values)
    return min(row[i:] + row[:i]
               for row in (values, values[::-1]) for i in range(len(row)))


def toggle(graph, vertices):
    for left, right in zip(vertices, vertices[1:]):
        assert (right in graph[left]) == (left in graph[right])
        if right in graph[left]:
            graph[left].remove(right)
            graph[right].remove(left)
        else:
            graph[left].add(right)
            graph[right].add(left)


def circuit_lengths(graph):
    unseen = set(graph)
    lengths = []
    while unseen:
        start = next(iter(unseen))
        previous, vertex, count = None, start, 0
        while vertex in unseen:
            unseen.remove(vertex)
            count += 1
            choices = graph[vertex] - {previous}
            assert choices
            following = min(choices)
            previous, vertex = vertex, following
        assert vertex == start
        lengths.append(count)
    return sorted(lengths)


def verify(directory):
    data = json.loads((directory / 'factor.json').read_text())
    n = data['dimension']
    assert n == 9
    raw_word = (directory / 'hamilton-n9-word.txt').read_bytes()
    assert raw_word.endswith(b'\n') and raw_word.count(b'\n') == 1
    word = raw_word[:-1].decode('ascii')
    assert hashlib.sha256(raw_word).hexdigest() == data['word_file_sha256']
    assert hashlib.sha256(word.encode()).hexdigest() == data['word_sha256']
    assert len(word) == math.factorial(n) and set(word) <= set('abc')
    start = tuple(data['start'])
    assert start == tuple(range(1, n + 1))
    vertex, seen = start, set()
    for symbol in word:
        assert vertex not in seen
        seen.add(vertex)
        vertex = flip(vertex, n - 'abc'.index(symbol))
    assert len(seen) == math.factorial(n) and vertex == start
    assert word[-1] == 'a'
    del seen

    whole_e = [(x, tuple(row)) for x, row in data['full_E_suppliers']]
    ts = [tuple(row) for row in data['T_representatives']]
    h = tuple(data['defused_representative'])
    assert h == (-3, 5, 0, 4, 3, 2, -1, 1, -2)
    labels = tuple(sorted(h))
    assert len(set(labels)) == n
    suppliers = [(x, canonical_circle(row)) for x, row in whole_e]
    suppliers += [(row[0], canonical_circle(row[1:])) for row in ts]
    suppliers += [(row[-1], canonical_circle(row[:-1])) for row in ts]
    assert len(set(suppliers)) == len(suppliers)
    assert len(whole_e) == 2212 and len(ts) == 372
    graph = {row: {flip(row, n), flip(row, n - 1)}
             for row in itertools.permutations(labels)}
    for x, row in whole_e:
        assert len(row) == n - 1 and set(row + (x,)) == set(labels)
        toggle(graph, polygon(row + (x,), [n - 1, n - 2] * (n - 1)))
    for row in ts:
        assert len(row) == n and set(row) == set(labels)
        toggle(graph, polygon(row, ([n, n - 2] + [n - 1, n - 2] * (n - 3)) * 2))
    assert all(len(neighbors) == 2 for neighbors in graph.values())
    assert all(row in graph[other] for row, neighbors in graph.items() for other in neighbors)

    # Check the supplied word against the independently rebuilt supplier factor.
    rename = dict(zip(range(1, n + 1), labels))
    vertex = tuple(rename[x] for x in start)
    seen = set()
    for symbol in word:
        assert vertex not in seen
        seen.add(vertex)
        other = flip(vertex, n - 'abc'.index(symbol))
        assert other in graph[vertex]
        vertex = other
    assert vertex == tuple(rename[x] for x in start)
    assert seen == set(graph)
    del seen

    # Revert the O8 rejoin and verify the full input, then its actual outside paths.
    o = polygon(h, [n, n - 1, n - 2, n - 1] * 2)
    assert all((o[i + 1] in graph[o[i]]) == (i % 2 == 0) for i in range(8))
    restored = [(x, canonical_circle(row)) for x, row in data['restored_E']]
    reserved = [(h[0], canonical_circle(h[1:])), (h[-1], canonical_circle(h[:-1]))]
    assert restored == reserved and all(supplier in suppliers for supplier in restored)
    toggle(graph, o)
    assert circuit_lengths(graph) == [922, 361958]
    for i in (1, 3, 5, 7):
        left, right = o[i], o[i + 1]
        graph[left].remove(right)
        graph[right].remove(left)
    endpoints = {row: i for i, row in enumerate(o[:-1])}
    visited, lengths = set(), {}
    for left_index in range(8):
        left = o[left_index]
        if left in visited:
            continue
        previous, vertex, count = None, left, 0
        while True:
            assert vertex not in visited
            visited.add(vertex)
            if count and vertex in endpoints:
                right_index = endpoints[vertex]
                break
            choices = graph[vertex] - {previous}
            assert len(choices) == 1
            previous, vertex = vertex, next(iter(choices))
            count += 1
        lengths[f'{min(left_index, right_index)}{max(left_index, right_index)}'] = count
    assert lengths == {'07': 361957, '15': 752, '24': 152, '36': 15}
    assert visited == set(graph)
    del graph
    beta = {0: 7, 7: 0, 1: 5, 5: 1, 2: 4, 4: 2, 3: 6, 6: 3}
    trace, index = [0], 0
    for _ in range(4):
        index = beta[index]
        trace.append(index)
        index ^= 1
        trace.append(index)
    assert trace == [0, 7, 6, 3, 2, 4, 5, 1, 0]
    return {'n': n, 'distinct_vertices': math.factorial(n), 'closed': True,
            'closing_generator': word[-1], 'whole_E': len(whole_e), 'T': len(ts),
            'supplier_disjoint': True, 'input_circuits': [922, 361958],
            'outside_path_lengths': lengths, 'endpoint_trace': trace,
            'word_sha256': data['word_sha256'],
            'generator_counts': dict(sorted(Counter(word).items())),
            'scope': 'finite native certificate; no Lean, official acceptance or all-n claim'}


if __name__ == '__main__':
    print(json.dumps(verify(Path(__file__).parent), indent=2))
