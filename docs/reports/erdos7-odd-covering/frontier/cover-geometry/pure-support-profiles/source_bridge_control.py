"""Three prescribed CRT witnesses; no search or parameter sweep."""
import argparse
import hashlib
import json
from math import prod
from pathlib import Path

checks = 0


def require(condition):
    global checks
    if not condition:
        raise ValueError(f'prescribed source-bridge control failed at check {checks + 1}')
    checks += 1


def crt(coordinates):
    modulus = prod(coordinates)
    value = sum(a * (modulus // p) * pow(modulus // p, -1, p)
                for p, a in coordinates.items()) % modulus
    require(all(value % p == a % p for p, a in coordinates.items()))
    return modulus, value


def depth_one_family(rows, masks, private):
    originals = {3: 0}

    def add(coordinates):
        modulus, residue = crt(coordinates)
        require(modulus not in originals)
        originals[modulus] = residue

    for p in [5, 7] + private:
        add({p: p - 1 if p in (5, 7) else 0})
        add({3: 1 if p == 5 else 2, p: 0 if p in (5, 7) else 1})
    for index, (q, row) in enumerate(zip(private, rows)):
        add({5: row[0], q: 2})
        add({7: row[2], q: 3})
        add({3: 1 if (masks[0] >> index) & 1 else 2, 5: row[1], q: 4})
        add({3: 1 if (masks[1] >> index) & 1 else 2, 7: row[3], q: 5})
    require(len(originals) == 59)
    return originals


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--first-source', required=True, type=Path)
parser.add_argument('--second-source', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()

results = {}
for label, source_path, rowkey, maskkey in [
    ('FC110', args.first_source, 'common_rows', 'masks'),
    ('FC131', args.second_source, 'final_rows', 'final_masks'),
]:
    source_bytes = source_path.read_bytes()
    source = json.loads(source_bytes)
    private = source['private_primes']
    require(private == [11, 13, 17, 19, 23, 29, 31, 37, 41])
    require(source[rowkey][0] == [2, 0, 3, 3])
    canonical = depth_one_family(source[rowkey], source[maskkey], private)
    require(canonical[55] == 2 and canonical[77] == 3)
    changed = dict(canonical)
    changed[55] = 47
    require(set(changed) == set(canonical))
    require(47 % 5 == 2 and 47 % 11 == 3)
    require(canonical[55] % 11 != canonical[77] % 11)
    require(changed[55] % 11 == changed[77] % 11)
    _, intersection = crt({5: 2, 7: 3, 11: 3})
    require(intersection % 55 == 47 and intersection % 77 == 3)
    witnesses = []
    for digit, canonical_hits, changed_hits in [(3, [], [55]), (2, [55], []), (7, [], [])]:
        coordinates = {3: 1, 5: 2, 7: 2, **{q: 7 for q in private}}
        coordinates[11] = digit
        modulus, value = crt(coordinates)
        hits_a = [m for m, a in canonical.items() if value % m == a]
        hits_b = [m for m, a in changed.items() if value % m == a]
        require(hits_a == canonical_hits)
        require(hits_b == changed_hits)
        # Every higher private cylinder starts in root6. Every higher head
        # pure/star cylinder starts in roots p-2 or1. These same three
        # first-digit witnesses therefore avoid them at every finite N.
        require(all(coordinates[q] != 6 for q in private))
        require(all(coordinates[p] not in (p - 2, 1) for p in (5, 7)))
        # Added completion labels occupy pure first-root holes and are avoided.
        require(all(coordinates[p] != (p - 1 if p in (5, 7) else 0)
                  for p in (5, 7, *private)))
        witnesses.append({'private11_digit': digit, 'period': modulus, 'residue': value,
                          'canonical_hits': hits_a, 'changed_hits': hits_b})
    results[label] = {'source': str(source_path),
                      'source_sha256': hashlib.sha256(source_bytes).hexdigest(),
                      'source_hash_role': 'provenance only; no hash admission condition',
                      'actual_rows': source[rowkey], 'actual_masks': source[maskkey],
                      'private_primes': private, 'witnesses': witnesses,
                      'pair_intersection_mod385': intersection}

args.output.write_text(json.dumps({'scope': 'Two fixed skeletons; exactly three prescribed witnesses each. '
                                  'Depth-one originals checked explicitly; higher-depth avoidance uses first-root guards.',
                           'checks': checks, 'results': results}, indent=2) + '\n')
print(json.dumps({'checks': checks, 'output': str(args.output)}, indent=2))
