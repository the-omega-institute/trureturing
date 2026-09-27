#!/usr/bin/env python3
"""Literal original-AP cactus controls with exact block-cut messages.

Standard library only. Every full coordinate height is retained. Exact
conditional extension counts are checked against direct CRT enumeration.
Finite controls do not replace the general cactus noncoverage proof.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def factor(n):
    result = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        result[n] = 1
    return result


def crt(congruences):
    x, modulus = 0, 1
    for residue, m in congruences:
        x += ((residue-x)*pow(modulus, -1, m) % m)*modulus
        modulus *= m
        x %= modulus
    return x


def biconnected_edge_blocks(neighbors):
    """Tarjan edge-stack decomposition of the literal prime-support graph."""
    discovery, low, stack, blocks = {}, {}, [], []

    def visit(p, parent):
        discovery[p] = low[p] = len(discovery)
        for q in sorted(neighbors[p]):
            if q == parent:
                continue
            if q not in discovery:
                stack.append((p, q))
                visit(q, p)
                low[p] = min(low[p], low[q])
                if low[q] >= discovery[p]:
                    block = []
                    while True:
                        edge = stack.pop()
                        block.append(tuple(sorted(edge)))
                        if edge == (p, q):
                            break
                    blocks.append(tuple(sorted(block)))
            elif discovery[q] < discovery[p]:
                stack.append((p, q))
                low[p] = min(low[p], discovery[q])

    visit(min(neighbors), None)
    assert len(discovery) == len(neighbors) and not stack
    return tuple(sorted(blocks))


def control(name, family):
    assert all(d > 1 and d % 2 and 0 <= a < d for d, a in family.items())
    supports = {d: factor(d) for d in family}
    primes = sorted(set().union(*(s.keys() for s in supports.values())))
    heights = {p: max(s.get(p, 0) for s in supports.values()) for p in primes}
    sizes = {p: p**heights[p] for p in primes}
    neighbors = {p: set() for p in primes}
    pure = {p: [] for p in primes}
    for d, support in supports.items():
        if len(support) == 1:
            pure[next(iter(support))].append(d)
        for p, q in combinations(support, 2):
            neighbors[p].add(q)
            neighbors[q].add(p)
    graph_blocks = biconnected_edge_blocks(neighbors)
    blocks = []
    incident = {p: [] for p in primes}
    label_assignment = {}
    for i, edges in enumerate(graph_blocks):
        vertices = tuple(sorted(set().union(*(set(e) for e in edges))))
        assert (len(edges) == 1 and len(vertices) == 2) or (
            len(edges) == len(vertices) and all(sum(p in edge for edge in edges) == 2 for p in vertices))
        labels = tuple(sorted(d for d in family if len(supports[d]) >= 2 and supports[d].keys() <= set(vertices)))
        assert labels
        for d in labels:
            assert d not in label_assignment
            label_assignment[d] = i
        blocks.append({'id':i,'kind':'bridge' if len(vertices)==2 else 'cycle',
                       'vertices':vertices,'edges':edges,'original_labels':labels})
        for p in vertices:
            incident[p].append(i)
    assert set(label_assignment) == {d for d in family if len(supports[d]) >= 2}
    root = 3 if 3 in primes else min(primes)
    counts, domains, subtree_primes = {}, {}, {}
    node_parent_block, block_parent = {}, {}
    node_child_blocks, block_child_vertices = {}, {}
    messages, block_subtree_primes, block_first_extension = {}, {}, {}

    def visit_vertex(p, parent_block):
        assert p not in node_parent_block
        node_parent_block[p] = parent_block
        child_blocks = [i for i in incident[p] if i != parent_block]
        node_child_blocks[p] = child_blocks
        weights = [int(all(x % d != family[d] for d in pure[p])) for x in range(sizes[p])]
        descendants = {p}
        for i in child_blocks:
            visit_block(i, p)
            for x in range(sizes[p]):
                weights[x] *= messages[i][x]
            descendants |= block_subtree_primes[i]
        counts[p] = tuple(weights)
        domains[p] = tuple(x for x, value in enumerate(weights) if value)
        subtree_primes[p] = descendants
        assert domains[p]
        if p != root:
            assert F(len(domains[p]), sizes[p]) >= F(2, 3)

    def visit_block(i, p):
        assert i not in block_parent
        block_parent[i] = p
        block = blocks[i]
        children = tuple(q for q in block['vertices'] if q != p)
        block_child_vertices[i] = children
        for q in children:
            visit_vertex(q, i)
        block_subtree_primes[i] = {p}.union(*(subtree_primes[q] for q in children))
        weights = [0]*sizes[p]
        tuple_counts = [0]*sizes[p]
        first = {}
        for x in range(sizes[p]):
            for words in product(*(domains[q] for q in children)):
                residue = crt([(x, sizes[p])]+[(word, sizes[q]) for q, word in zip(children, words)])
                if all(residue % d != family[d] for d in block['original_labels']):
                    multiplicity = prod(counts[q][word] for q, word in zip(children, words))
                    assert multiplicity > 0
                    weights[x] += multiplicity
                    tuple_counts[x] += 1
                    first.setdefault(x, words)
        messages[i] = tuple(weights)
        block_first_extension[i] = first
        block.update({'parent':p,'child_vertices':children,
                      'child_actual_feasible_densities':{q:F(len(domains[q]),sizes[q]) for q in children},
                      'parent_original_coordinate_modulus':sizes[p],
                      'actual_blocked_parent_words':[x for x,value in enumerate(weights) if not value],
                      'actual_blocked_parent_Haar':F(sum(value==0 for value in weights),sizes[p]),
                      'legal_child_joint_tuple_counts_by_parent_word':tuple_counts,
                      'full_descendant_extension_counts_by_parent_word':weights,
                      'uniform_child_domain_product_size':prod(len(domains[q]) for q in children)})

    visit_vertex(root, None)
    assert set(counts) == set(primes) and len(block_parent) == len(blocks)
    period = prod(sizes.values())
    full_count = sum(counts[root])
    assert full_count > 0
    chosen = {}

    def choose(p, x):
        chosen[p] = x
        for i in node_child_blocks[p]:
            words = block_first_extension[i][x]
            for q, word in zip(block_child_vertices[i], words):
                choose(q, word)

    choose(root, domains[root][0])
    witness = crt((chosen[p], sizes[p]) for p in primes)
    assert all(witness % d != a for d, a in family.items())
    enumerations = []

    def brute_conditional(prime_set, parent, exclude_parent_pure):
        local_period = prod(sizes[p] for p in prime_set)
        labels = tuple(sorted(d for d in family if supports[d].keys() <= prime_set
                              and not (exclude_parent_pure and set(supports[d]) == {parent})))
        values = [0]*sizes[parent]
        for x in range(local_period):
            if all(x % d != family[d] for d in labels):
                values[x % sizes[parent]] += 1
        enumerations.append({'parent':parent,'subtree_primes':sorted(prime_set),
                             'parent_pure_excluded':exclude_parent_pure,
                             'original_period':local_period,'original_labels':labels,
                             'exact_conditional_extension_counts':values})
        return tuple(values)

    for p in primes:
        assert brute_conditional(subtree_primes[p], p, False) == counts[p]
    for i in range(len(blocks)):
        assert brute_conditional(block_subtree_primes[i], block_parent[i], True) == messages[i]
    assert sum(brute_conditional(set(primes), root, False)) == full_count
    return {'name':name,'original_labels':[{'modulus':d,'residue':family[d]} for d in sorted(family)],
            'original_period':period,'prime_heights':heights,'root':root,
            'block_cut_blocks':blocks,
            'vertex_subtree_data':[{'prime':p,'parent_block':node_parent_block[p],
                                    'full_original_coordinate_modulus':sizes[p],
                                    'pure_original_labels':sorted(pure[p]),
                                    'feasible_words':domains[p],
                                    'feasible_Haar':F(len(domains[p]),sizes[p]),
                                    'exact_extension_counts_by_word':counts[p]} for p in primes],
            'full_original_Haar_survivor_count':full_count,
            'full_original_Haar_survival_probability':F(full_count,period),
            'actual_original_uncovered_residue':witness,
            'all_block_and_vertex_conditional_counts_checked_against_CRT':True,
            'complete_CRT_conditional_checks':enumerations,
            'sum_of_enumerated_original_periods':sum(row['original_period'] for row in enumerations)}


def serializable(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):serializable(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [serializable(v) for v in value]
    return value


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    models = [
        ('two_triangles_share_root_three_with_higher_original_heights', {
            3:0,9:2,5:0,7:0,11:0,13:0,15:1,21:2,35:3,33:4,39:5,143:6,
            45:17,63:11,105:11,315:98,429:17,1287:509}),
        ('root_three_hangs_from_five_shared_by_two_triangles', {
            3:0,5:0,7:0,11:0,13:0,17:0,15:1,35:2,55:3,77:4,
            65:6,85:7,221:8,385:19,1105:31}),
        ('root_three_five_intermediate_path_to_triangle', {
            3:0,5:0,7:0,11:0,13:0,15:1,35:2,77:3,91:4,143:5,1001:17}),
    ]
    results = [control(name,family) for name,family in models]
    assert [r['original_period'] for r in results] == [45045,255255,15015]
    assert sum(b['kind']=='cycle' for b in results[0]['block_cut_blocks']) == 2
    assert sum(b['kind']=='cycle' for b in results[1]['block_cut_blocks']) == 2
    assert [b['parent'] for b in results[1]['block_cut_blocks'] if b['kind']=='cycle'] == [5,5]
    assert any(b['kind']=='bridge' and b['parent']==5 for b in results[2]['block_cut_blocks'])
    data={'scope':'Exact literal cactus AP examples, not a proof for arbitrary cactus palettes.',
          'probability_convention':'Full original Haar. Node domains are existential; '
                                   'message weights count actual simultaneous extensions.',
          'controls':results}
    output=Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(serializable(data),indent=2)+'\n')
    print(json.dumps(serializable([{'name':r['name'],'period':r['original_period'],
                                   'uncovered':r['full_original_Haar_survivor_count'],
                                   'Haar':r['full_original_Haar_survival_probability'],
                                   'enumerated_period_sum':r['sum_of_enumerated_original_periods']}
                                  for r in results]),indent=2))


if __name__=='__main__':
    main()
