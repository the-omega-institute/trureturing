from pathlib import Path
from itertools import combinations
from math import comb, prod, isqrt
from fractions import Fraction
import hashlib
import json

path = Path("docs/reports/prime-slab-corner-order-0909.json")
raw = path.read_bytes()
sha = hashlib.sha256(raw).hexdigest()
assert len(raw) == 6741
assert sha == "9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672"
data = json.loads(raw)
primes = [2, 3, 5, 7, 11, 13, 17, 19]
assert data["schema_version"] == 1
assert data["kind"] == "constant-prime-corner-order-input"
assert data["primes"] == primes
assert data["search_executed"] is False
assert data["exponent_boxes_generated"] == 0
assert data["triple_order"] == "lexicographic increasing prime-list index triples"
assert data["mask_convention"] == (
    "bit i selects prime at coordinate i; bit 0 is the least significant bit"
)
assert all(p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))
           for p in primes)
triples = list(combinations(primes, 3))
assert len(data["rows"]) == len(triples) == comb(8, 3) == 56
for index, (row, triple) in enumerate(zip(data["rows"], triples)):
    assert row["triple_index"] == index
    assert row["primes"] == list(triple)
    products = [prod(triple[i] for i in range(3) if mask & (1 << i))
                for mask in range(8)]
    masks = sorted(range(8), key=products.__getitem__)
    p0, p1, p2 = triple
    assert p2 != p0 * p1
    expected = ([0, 1, 2, 4, 3, 5, 6, 7] if p2 < p0 * p1
                else [0, 1, 2, 3, 4, 5, 6, 7])
    assert row["sorted_masks"] == masks == expected
    assert sorted(masks) == list(range(8))
    ordered = [products[m] for m in masks]
    assert row["subset_products"] == ordered
    assert all(a < b for a, b in zip(ordered, ordered[1:]))

assert [slot + 1 for slot in range(7)] == list(range(1, 8))
reflected = [(1 + (slot - 7) // 3, (slot - 7) % 3)
             for slot in range(7, 25)]
assert reflected == [(j, i) for j in range(1, 7) for i in range(3)]
boxes = comb(8, 3) * 16**3
slots = 7 + 6 * 3
assert boxes == 229376 and slots == 25
assert 4096 * 55 + 256 * 15 + 16 * 15 + 15 == boxes - 1
assert (boxes * 7, boxes * 18, boxes * slots) == (
    1605632, 4128768, 5734400
)
assert 25 * (boxes - 1) + 24 == 5734399
assert 3 * 34 == 102 and 3 * (2 * 15 + 3) == 99
assert 19**102 < 2**510 < 256**64 == 2**512
assert (19**102).bit_length() == 434
carry_max = 255 * 19 + 18
assert carry_max == 4863 and carry_max // 256 == 18
tail = Fraction(6, 25 * 2**23)
assert tail == Fraction(3, 104857600)
print(json.dumps({
    "certificate_bytes": len(raw), "certificate_sha256": sha,
    "constant_rows_checked": 56, "subset_products_checked": 448,
    "prospective_boxes": boxes, "raw_slots": boxes * slots,
    "guard_bound_bit_length": 434, "limbs": 64,
    "carry_max": carry_max, "tail_exact": str(tail),
    "exponent_boxes_generated": 0, "analytic_rows_executed": 0
}, sort_keys=True))
