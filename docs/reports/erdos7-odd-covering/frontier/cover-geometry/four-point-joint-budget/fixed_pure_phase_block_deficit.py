"""Exact finite data for report510's fixed-pure, all-height phase-block proof.

The quantified upper bound uses the ordinary cell-count proof in the report.
No solver, floating-point result, or finite sweep substitutes for that proof.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from math import prod, gcd
import argparse
import hashlib
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def crt(residues, moduli):
    x, carrier = 0, 1
    for a, modulus in zip(residues, moduli):
        if modulus == 1:
            continue
        need(gcd(carrier, modulus) == 1, 'coprime CRT coordinates')
        x += carrier * ((a - x) * pow(carrier, -1, modulus) % modulus)
        carrier *= modulus
        x %= carrier
    return x, carrier


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--certificate', type=Path)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
root = args.input_dir
certificate = json.loads((args.certificate or root / 'fixed_pure_phase_block_deficit_certificate.json').read_text())
raw = (root / 'integer_selector_tail_interface_certificate.json').read_bytes()
source_sha = hashlib.sha256(raw).hexdigest()
need(source_sha == '66f155d2d9f65b044017e0c033c1d3e8f9999cea100eabce1b8aa049810ecb5a', 'fixed report503 pure boundary')
need(certificate['source_sha256'] == source_sha, 'certificate source binding')
source = json.loads(raw)
case = source['cases'][0]
primes = tuple(source['old_primes'])
profiles = tuple(map(tuple, case['profiles']))
weight = (17, 16, 13)
need(primes == (3, 5, 7, 11, 13, 17, 19), 'old prime coordinates')
need(profiles == ((4, 2, -4, 1, 2, 1, 1), (5, -2, 4, 1, 1, 1, 1), (-5, -3, -2, 1, 1, 1, 1)), 'fixed three-point interface')

boxes = []
for profile in profiles:
    boxes.append(tuple(set(product(*(range(n) for n in sizes))) for sizes in (
        tuple(max(1, f) for f in profile[:3]) + profile[3:],
        tuple(max(1, -f) for f in profile[:3]) + profile[3:])))
exponents = set().union(*(a | b for a, b in boxes))
old_powers = tuple(p ** max(max(1, abs(s[i])) for s in profiles) for i, p in enumerate(primes))
old_carrier = prod(old_powers)
centres = (0, crt((1, 1, 1, 0, 0, 0, 0), old_powers)[0])
points = []
for profile in profiles:
    coordinates = [(2 if f == 0 else (0 if f > 0 else 1) + p ** (abs(f) - 1))
                   if i < 3 else p ** (f - 1) for i, (p, f) in enumerate(zip(primes, profile))]
    points.append(crt(coordinates, old_powers)[0])
labels = {}
for e in sorted(exponents):
    d = prod(p ** j for p, j in zip(primes, e))
    masks = tuple(tuple(int(e in pair[s]) for pair in boxes) for s in (0, 1))
    actual_masks = tuple(tuple(int((x - centre) % d == 0) for x in points) for centre in centres)
    need(actual_masks == masks, 'common literal old CRT realization')
    scores = tuple(dot(weight, mask) for mask in masks)
    maximum = max(scores)
    best = tuple(s for s in (0, 1) if scores[s] == maximum)
    labels[d] = {'d': d, 'exponents': e, 'masks': masks, 'scores': scores,
                 'maximum': maximum, 'maximizing_selectors': best}
need(len(labels) == 51 and sum(r['maximum'] for r in labels.values()) == 892, 'full old inventory')
block = sorted(d for d, row in labels.items() if all(row['masks'][s][1] for s in row['maximizing_selectors']))
need(block == certificate['block_labels'] and len(block) == 18, 'complete eighteen-label block')
need(sum(labels[d]['maximum'] for d in block) == 382, 'independent block capacity')
positive_gaps = [labels[d]['maximum'] - score for d in block for score in labels[d]['scores'] if score < labels[d]['maximum']]
need(min(positive_gaps) == 3, 'minimum positive selector loss')

pure = []
axes = {}
need([axis['prime'] for axis in case['axes']] == [23, 29], 'new prime axes')
for axis in case['axes']:
    p = axis['prime']
    seen = set()
    used = [set() for _ in points]
    activation = [0, 0, 0]
    for row in axis['labels']:
        e = tuple(row['exponents'])
        d = prod(q ** j for q, j in zip(primes, e))
        need(d in labels and e == labels[d]['exponents'] and d not in seen, 'one pure entry per numerical old label')
        seen.add(d)
        need(row['selector'] in ('A', 'B') and type(row['digit']) is int and 1 <= row['digit'] < p, 'valid pure selector and digit')
        side = int(row['selector'] == 'B')
        mask = labels[d]['masks'][side]
        for i, active in enumerate(mask):
            if active:
                need(row['digit'] not in used[i], 'distinct active pure digits')
                used[i].add(row['digit'])
                activation[i] += 1
        for height in (1, 2):
            phase = row['digit'] * p ** (height - 1)
            residue, modulus = crt((centres[side] % d, phase), (d, p ** height))
            need(modulus == d * p ** height and residue % d == centres[side] % d and residue % p ** height == phase, 'literal pure residue')
            pure.append({'old_label': d, 'selector': row['selector'], 'prime': p, 'height': height,
                         'phase': phase, 'modulus': modulus, 'residue': residue})
    need(seen == set(labels) and activation == axis['activation'], 'full fixed pure inventory')
    root_counts = []
    for i, point in enumerate(points):
        active_classes = [r for r in pure if r['prime'] == p and (point - r['residue']) % r['old_label'] == 0]
        counts = [0] * p
        for z in range(p * p):
            if all(z % (p ** r['height']) != r['phase'] for r in active_classes):
                counts[z % p] += 1
        expected = [p - activation[i] if r == 0 else (0 if r in used[i] else p) for r in range(p)]
        need(counts == expected, 'literal height-two root distribution')
        root_counts.append(counts)
    axes[p] = {'activation': activation, 'used_digits': [sorted(u) for u in used], 'root_counts': root_counts}
need(axes[23]['activation'] == [18, 21, 18] and axes[29]['activation'] == [21, 13, 24], 'fixed pure axis losses')
need(axes[23]['used_digits'][1] == list(range(1, 22)) and axes[29]['used_digits'][1] == list(range(1, 14)), 'point2 literal first cells')
relative = {(a, b): F(axes[23]['root_counts'][1][a] * axes[29]['root_counts'][1][b], 667)
            for a, b in product(range(23), range(29))}
full_cells = sorted(cell for cell, mass in relative.items() if mass == 1)
need(full_cells == list(product((22,), range(14, 29))), 'exactly fifteen full cells')
need(max(mass for mass in relative.values() if mass < 1) == F(16, 29), 'largest partial cell')

option_checks = 0
individual = []
for d in block:
    row = labels[d]
    best_numerator = -1
    best_count = 0
    for side, a, b in product((0, 1), range(23), range(29)):
        numerator = sum(weight[i] * row['masks'][side][i] * axes[23]['root_counts'][i][a] * axes[29]['root_counts'][i][b] for i in range(3))
        if numerator > best_numerator:
            best_numerator, best_count = numerator, 1
        elif numerator == best_numerator:
            best_count += 1
        option_checks += 1
    need(best_numerator == 667 * row['maximum'], 'each individual maximum is attained')
    individual.append({'old_label': d, 'masks': row['masks'], 'scores': row['scores'],
                       'maximum': str(F(row['maximum'], 667)), 'maximizing_phase_options': best_count})
losses = [F(3 * c) + F(208, 29) * max(3 - c, 0) for c in range(19)]
need(min(losses) == 9 and losses.index(9) == 3, 'all selector-count branches imply the block deficit')

witness = certificate['witness']
need([r['old_label'] for r in witness] == block, 'one common witness entry per complete block label')
mixed = []
selected = []
for row in witness:
    d = row['old_label']
    need(row['selector'] in ('A', 'B'), 'mixed selector')
    side = int(row['selector'] == 'B')
    a, b = row['phase']
    need(type(a) is int and type(b) is int and 1 <= a < 23 and 1 <= b < 29, 'nonzero mixed first phases')
    mask = labels[d]['masks'][side]
    residue, modulus = crt((centres[side] % d, a, b), (d, 23, 29))
    need(residue % d == centres[side] % d and residue % 23 == a and residue % 29 == b and modulus == 667 * d, 'literal mixed residue')
    need(tuple(int((point - residue) % d == 0) for point in points) == mask, 'one mixed selector across all points')
    for i, active in enumerate(mask):
        if active:
            need(axes[23]['root_counts'][i][a] == 23 and axes[29]['root_counts'][i][b] == 29, 'mixed cell fully survives pure classes')
    selected.append(mask)
    mixed.append({'old_label': d, 'selector': row['selector'], 'mask': mask, 'phase': (a, b), 'modulus': modulus, 'residue': residue})
family = pure + mixed
need(len(family) == 222 and len({r['modulus'] for r in family}) == 222, '222 distinct original numerical moduli')
need(all(r['modulus'] > 1 and r['modulus'] % 2 == 1 and 0 <= r['residue'] < r['modulus'] for r in family), 'legal odd classes')
comparisons = 0
for r in mixed:
    for i, active in enumerate(r['mask']):
        if active:
            for q in pure:
                if (points[i] - q['residue']) % q['old_label'] == 0:
                    need((r['residue'] - q['residue']) % gcd(r['modulus'], q['modulus']) != 0, 'literal mixed/pure incompatibility')
                    comparisons += 1
for r, q in combinations(mixed, 2):
    if any(a and b for a, b in zip(r['mask'], q['mask'])):
        need((r['residue'] - q['residue']) % gcd(r['modulus'], q['modulus']) != 0, 'literal mixed/mixed incompatibility')
        comparisons += 1
activation = tuple(sum(mask[i] for mask in selected) for i in range(3))
need(activation == (4, 15, 5) and dot(weight, activation) == 373, 'sharp simultaneous block deletion')

relaxed_masks = []
for d in block:
    side = labels[d]['maximizing_selectors'][0]
    if d in (21, 63):
        side = 1 - side
    relaxed_masks.append(labels[d]['masks'][side])
relaxed_activation = tuple(sum(mask[i] for mask in relaxed_masks) for i in range(3))
limiting_areas = tuple(F((22 - a) * (28 - b), 616) for a, b in zip(axes[23]['activation'], axes[29]['activation']))
need(relaxed_activation == (4, 16, 4) and dot(weight, relaxed_activation) == 376, 'area-only selector witness')
need(all(F(n, 667) < area for n, area in zip(relaxed_activation, limiting_areas)), 'independent deletions fit smaller limiting areas')
need(limiting_areas[1] - F(16, 667) == F(149, 410872), 'strict marginal-area slack')

out = {'source_sha256': source_sha, 'old_carrier': old_carrier, 'old_centres': centres, 'old_points': points,
       'profiles': profiles, 'weight': weight, 'block_labels': block, 'individual_label_checks': individual,
       'single_label_option_checks': option_checks, 'pure_axis_checks': axes, 'point2_full_cells': full_cells,
       'point2_largest_partial_cell_fraction_at_height2': '16/29', 'selector_count_loss_numerators': list(map(str, losses)),
       'independent_block_capacity': '382/667', 'sharp_block_deletion': '373/667', 'sharp_deficit': '9/667',
       'sharp_activation': activation, 'literal_family_at_height2': family, 'congruence_incompatibility_checks': comparisons,
       'area_only_relaxed_activation': relaxed_activation, 'area_only_relaxed_deletion': '376/667',
       'limiting_pure_survivor_areas': list(map(str, limiting_areas)), 'point2_relaxed_area_slack': '149/410872',
       'scope': 'Fixed report503 pure phases and selectors, both heights at least two; same eighteen original first-mixed labels. All-height upper and stability use the ordinary report proof. No global source-mass improvement or Lean verification.'}
out = json.loads(json.dumps(out))
if args.output:
    args.output.write_text(json.dumps(out, indent=2) + '\n')
else:
    need(out == json.loads(Path(__file__).with_suffix('.json').read_text()), 'retained result differs')
print(json.dumps({key: out[key] for key in ('single_label_option_checks', 'sharp_block_deletion', 'sharp_deficit', 'sharp_activation', 'congruence_incompatibility_checks', 'area_only_relaxed_deletion')}, indent=2))
