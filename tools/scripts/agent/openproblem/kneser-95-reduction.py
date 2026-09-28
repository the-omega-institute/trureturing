#!/usr/bin/env python3
"""Rebuild and audit the exact (9,5) projection and six-set clauses."""

from collections import Counter, defaultdict
from itertools import combinations, permutations


def mask(member):
    return sum(1 << (p - 1) for p in member)


def main():
    vertices = list(combinations(range(1, 10), 5))
    assert len(vertices) == 126
    vertex_ids = {member: i for i, member in enumerate(vertices)}
    masks = [mask(member) for member in vertices]
    edge_ids = {pair: i for i, pair in enumerate(combinations(range(126), 2), 1)}
    edge_size = {index: bin(masks[a] & masks[b]).count("1")
                 for (a,b), index in edge_ids.items()}
    assert Counter(edge_size.values()) == {1:315,2:2520,3:3780,4:1260}
    triangles_by_type = Counter()
    occurrences = defaultdict(list)
    near_owners = Counter()
    original_222 = []
    for a,b,c in combinations(range(126), 3):
        if masks[a] & masks[b] & masks[c]:
            continue
        edges = (edge_ids[(a,b)],edge_ids[(a,c)],edge_ids[(b,c)])
        sizes = tuple(sorted(edge_size[e] for e in edges))
        triangles_by_type[sizes] += 1
        if sizes == (1,1,4):
            near_owners[next(e for e in edges if edge_size[e] == 4)] += 1
        elif 3 in sizes:
            middle = next(e for e in edges if edge_size[e] == 3)
            occurrences[middle].append(tuple(e for e in edges if e != middle))
        else:
            assert sizes == (2,2,2)
            original_222.extend((frozenset(edges),frozenset(-e for e in edges)))
    assert triangles_by_type == {(1,1,4):1260,(1,2,3):15120,
                                 (2,2,2):7560,(2,2,3):7560}
    assert len(near_owners) == 1260 and set(near_owners.values()) == {1}
    assert len(occurrences) == 3780 and all(len(v) == 6 for v in occurrences.values())
    projected = set(original_222)
    projected_counts = Counter({0:len(original_222)})
    for partners in occurrences.values():
        for left, right in permutations(partners, 2):
            clause = frozenset((*left, *(-e for e in right)))
            assert len(clause) == 4 and not any(-e in clause for e in clause)
            projected.add(clause)
            ones = [lit for lit in clause if edge_size[abs(lit)] == 1]
            assert len(ones) <= 2 and (len(ones) != 2 or ones[0] * ones[1] < 0)
            projected_counts[len(ones)] += 1
    assert projected_counts == {0:22680,1:60480,2:45360}
    assert len(projected) == 128520
    assert sum(triangles_by_type.values()) == 31500
    print("V(9,5): 126 vertices, 7875 edges, 31500 triangles; types "
          "114=1260, 123=15120, 222=7560, 223=7560")
    print("near edges: 1260 independently eliminated; size-3 edges: 3780 "
          "independently eliminated")
    print("projection: 2835 variables, 128520 distinct clauses; "
          "master=22680, one size-1=60480, two size-1=45360; Horn 2-SAT checked")

    A,C,B,D,E,F = [tuple(int(ch) for ch in word) for word in
                   ("12345","16789","23467","15679","23568","14689")]
    base = (A,C,B,D,E,F)
    names = dict(zip("ACBDEF", base))
    def edge(x,y, mapping):
        u,v = sorted((vertex_ids[mapping[x]],vertex_ids[mapping[y]]))
        return edge_ids[(u,v)]
    local_triangles = []
    for a,b,c in combinations(range(6), 3):
        if not mask(base[a]) & mask(base[b]) & mask(base[c]):
            local_triangles.append("".join("ACBDEF"[i] for i in (a,b,c)))
    assert set(local_triangles) == {"ACB", "ABD", "ACE", "AEF"}
    orbit = set()
    for perm in permutations(range(1,10)):
        mapping = {name: tuple(sorted(perm[p-1] for p in member))
                   for name, member in names.items()}
        ac,bc,ad,bd,ce,af,ef = (edge(*pair, mapping) for pair in
                               ("AC","BC","AD","BD","CE","AF","EF"))
        first = frozenset((bc,ac,-ad,-bd))
        second = frozenset((-ac,-ce,af,ef))
        assert first in projected and second in projected
        cut = frozenset((bc,-ad,-bd,-ce,af,ef))
        orbit.add(cut)
        orbit.add(frozenset(-lit for lit in cut))
    assert len(orbit) == 181440
    assert all(all(edge_size[abs(lit)] == 2 for lit in clause) for clause in orbit)
    print("six-set clause: four local forbidden triangles; 181440 distinct "
          "colour-symmetric master clauses, each checked via two projected clauses")
    print("(9,5) remains open: no full master search or full colouring is asserted")


if __name__ == "__main__":
    main()
