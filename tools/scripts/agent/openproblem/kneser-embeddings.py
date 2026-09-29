#!/usr/bin/env python3
"""Check the two F32 embeddings and the even-line propagation through k=200."""

from itertools import combinations
from pathlib import Path
import runpy


F32 = runpy.run_path(str(Path(__file__).with_name("kneser-certificates.py")))["F32"]

MAP6 = [
    (1,2,3,4,5,6),(1,2,4,6,10,11),(1,2,4,6,7,9),(1,2,3,5,10,11),
    (1,2,3,5,7,9),(1,2,7,9,10,11),(3,4,5,6,10,11),(3,4,5,6,7,9),
    (4,6,7,9,10,11),(3,5,7,9,10,11),(1,2,4,6,8,12),(1,2,3,5,8,12),
    (1,2,8,10,11,12),(1,2,7,8,9,12),(3,4,5,6,8,12),(4,6,8,10,11,12),
    (4,6,7,8,9,12),(3,5,8,10,11,12),(3,5,7,8,9,12),(7,8,9,10,11,12),
    (2,3,5,7,8,9),(4,5,6,7,8,9),(2,3,4,5,6,12),(1,2,4,6,10,12),
    (2,4,6,7,9,12),(3,4,5,10,11,12),(4,5,6,7,9,12),(4,6,7,10,11,12),
    (1,2,3,4,10,11),(1,2,4,6,9,11),(1,2,5,9,10,11),(3,4,5,9,10,11),
]

MAP7 = [
    (1,2,3,4,5,6,7),(2,3,5,6,7,8,9),(2,3,5,6,7,10,13),
    (1,2,3,4,7,8,9),(1,2,3,4,7,10,13),(2,3,7,8,9,10,13),
    (1,2,4,5,6,8,9),(1,2,4,5,6,10,13),(2,5,6,8,9,10,13),
    (1,2,4,8,9,10,13),(3,5,6,7,11,12,14),(1,3,4,7,11,12,14),
    (3,7,8,9,11,12,14),(3,7,10,11,12,13,14),(1,4,5,6,11,12,14),
    (5,6,8,9,11,12,14),(5,6,10,11,12,13,14),(1,4,8,9,11,12,14),
    (1,4,10,11,12,13,14),(8,9,10,11,12,13,14),(1,3,4,7,10,11,13),
    (1,4,5,6,10,11,13),(1,3,4,5,6,7,14),(3,5,6,7,8,9,12),
    (3,5,6,7,10,12,13),(1,4,5,6,8,9,12),(1,4,5,6,10,12,13),
    (5,8,9,10,12,13,14),(1,3,4,5,6,8,9),(3,5,6,7,8,10,13),
    (1,3,4,7,8,9,10),(1,4,6,8,9,10,13),
]


def masks(family):
    return [sum(1 << (x - 1) for x in member) for member in family]


def check_map(source, images, n, k):
    assert len(source) == len(images) == 32
    assert len(set(images)) == 32
    assert all(len(image) == k and len(set(image)) == k and
               all(1 <= x <= n for x in image) for image in images)
    source_masks, image_masks = masks(source), masks(images)
    required = 0
    for a, b, c in combinations(range(32), 3):
        if source_masks[a] & source_masks[b] & source_masks[c] == 0:
            required += 1
            assert image_masks[a] & image_masks[b] & image_masks[c] == 0
    assert required == 1211
    print(f"F32 -> V({n},{k}): 32 distinct images, {required} triangles preserved")


def main():
    assert len(F32) == len(set(F32)) == 32
    check_map(F32, MAP6, 12, 6)
    check_map(F32, MAP7, 14, 7)
    reachable = {0: ()}
    for k in range(1, 201):
        for g in (4, 6, 7):
            if k - g in reachable:
                reachable[k] = reachable[k - g] + (g,)
                break
    assert all(k in reachable for k in (4,6,7,8))
    assert all(k in reachable for k in range(10,201))
    assert {k for k in range(3,201) if k not in reachable} == {3,5,9}
    v63 = list(combinations(range(1,7), 3))
    cloned = [tuple((p - 1) * 3 + j for p in member for j in (1,2,3)) for member in v63]
    assert len(set(cloned)) == 20 and all(len(x) == 9 for x in cloned)
    for a,b,c in combinations(range(20), 3):
        if not set(v63[a]) & set(v63[b]) & set(v63[c]):
            assert not set(cloned[a]) & set(cloned[b]) & set(cloned[c])
    assert {3,5,9} | set(reachable).intersection(range(3,201)) == set(range(3,201))
    print("semigroup <4,6,7> plus direct 3,5 and cloned 9 covers 3 <= k <= 200")


if __name__ == "__main__":
    main()
