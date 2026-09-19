#!/usr/bin/env python3
"""Exact actual BB kernels refuting a uniformly larger killed-square floor."""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
from math import gcd


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def crt(a, m, b, p):
    return a + m * (((b - a) * pow(m, -1, p)) % p)


def fixture(p):
    q = 315
    ds = [d for d in range(1, q + 1) if q % d == 0]
    nonunit = ds[1:]
    old_forbidden = [(d, 0) for d in nonunit]
    old = [x for x in range(q) if all(x % d != r for d, r in old_forbidden)]
    check(len(old) == 144 and old == [x for x in range(q) if gcd(x, q) == 1], 'old survivors')
    delta = F(7, p - 2)
    mixed = [(d * p, crt(1, d, i + 1, p)) for i, d in enumerate(nonunit)]
    forbidden = old_forbidden + [(p, 0)] + mixed
    tests = [(d, 2 % d) for d in ds] + [(d * p, crt(2 % d, d, p - 1, p)) for d in ds]
    check(len(set(d for d, _ in forbidden)) == 23, 'distinct original forbidden labels')
    check(sorted(d for d, _ in tests) == [d for d in range(1, q * p + 1) if q * p % d == 0], 'complete original tests')
    physical = killed = charge = loss = F(0)
    joint_alpha = cap_deficit = cap_covariance = weighted_cap = F(0)
    charged_old_rows = []
    for x in old:
        bad = set()
        for y in range(1, p):
            z = crt(x, q, y, p)
            if any(z % d == r for d, r in mixed):
                bad.add(y)
        alpha = F(len(bad), p - 1)
        old_load = sum(x % d == 2 % d for d in ds)
        old_forbidden_load = sum(x % d == 1 % d for d in ds)
        check(alpha == F(old_forbidden_load - 1, p - 1), 'literal union has distinct current roots')
        joint_alpha += F(old_load**2, 144) * alpha
        sh_cap = F(p - 1, p - 2) / (1 - min(alpha, delta))
        cap = F(p - 1, p - 9)
        cap_deficit += (cap - sh_cap) / 144
        cap_covariance += (cap - sh_cap) * (old_load**2 - 1) / 144
        weighted_cap += sh_cap * old_load**2 / 144
        if alpha > delta:
            charged_old_rows.append(x)
        row_total = F(0)
        for y in range(1, p):
            z = crt(x, q, y, p)
            if y in bad:
                density = max(alpha - delta, F(0)) / (alpha * (1 - delta)) if alpha else F(0)
            else:
                density = 1 / (1 - min(alpha, delta))
            row_probability = density / (p - 1)
            row_total += row_probability
            probability = row_probability / len(old)
            load = sum(z % d == r for d, r in tests)
            physical += probability * load**2
            actual_bad = any(z % d == r for d, r in forbidden)
            check(actual_bad == (y in bad), 'physical original bad union')
            if actual_bad:
                charge += probability
                loss += probability * load**2
                if probability:
                    check(load == 1, 'strictly charged full test load is one')
            else:
                killed += probability * load**2
        check(row_total == 1, 'normalized genuine BB row')
    check(charged_old_rows == [1], 'only row one charged')
    expected_charge = (F(11, p - 1) - delta) / (1 - delta) / 144
    check(charge == expected_charge > 0, 'exact positive charge')
    check(loss == charge and physical - killed == charge, 'sharp killed unit floor')
    a = [sum(x % d == 2 % d for d in ds) for x in old]
    c = [sum(x % d == 1 % d for d in ds) for x in old]
    joint = sum((F(u*u*(v-1), 144) for u,v in zip(a,c)), F(0))
    old_square = sum((F(u*u, 144) for u in a), F(0))
    check(old_square == F(35, 4), 'coherent old square')
    check(joint == F(55, 12) and joint_alpha == joint / (p - 1), 'exact independent-layout joint energy')
    sh_relaxation = F(p - 1, p - 9) * old_square - cap_deficit
    check(sh_relaxation - weighted_cap == cap_covariance > 0, 'strict testwise SH26 covariance correction')
    histogram = {}
    for u, v in zip(a, c):
        histogram[u, v] = histogram.get((u, v), 0) + 1
    return dict(prime=p, delta=str(delta), actual_old_survivor_count=len(old),
                original_forbidden_classes=forbidden, original_test_classes=tests,
                charged_old_rows=charged_old_rows, charge=str(charge),
                physical_test_square=str(physical), killed_test_square=str(killed),
                lost_test_square=str(loss), old_cross_energy=str(joint),
                old_square=str(old_square), joint_test_square_alpha=str(joint_alpha),
                SH26_testwise_relaxation=str(sh_relaxation), weighted_actual_SH_cap=str(weighted_cap),
                positive_testwise_cap_covariance_saving=str(cap_covariance),
                old_joint_histogram=[dict(test_load=u, forbidden_load=v, count=n)
                                     for (u,v),n in sorted(histogram.items())],
                positive_mass_bad_excess_square='0',
                supported_test_square=str(killed / (1 - charge)),
                maximizing_test_claim=False)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        check(key not in result, 'duplicate certificate key')
        result[key] = value
    return result


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('certificate', nargs='?', type=Path,
                    default=(Path(__file__).resolve().parent / 'certificates/killed_unit_floor_certificate.json'))
parser.add_argument('--write', action='store_true')
args = parser.parse_args()
data = dict(schema='actual-bbmst-killed-unit-floor-v1',
            scope='Ordinary exact original-label verification; the complete current test witnesses need not maximize Gamma.',
            old_period=315, sharp_floor_fixtures=[fixture(17), fixture(19)])
output = args.certificate
if args.write:
    write_certificate_text(output, json.dumps(data, indent=2)+'\n')
else:
    saved = json.loads(read_artifact_text(output), object_pairs_hook=unique_object)
    check(json.dumps(saved, sort_keys=True) == json.dumps(data, sort_keys=True), 'certificate differs from exact reconstruction')
print('PASS: genuine BB17/19, all 23 forbidden and 24 complete CRT test labels, positive charge, exact killed unit floor, and joint-energy values')
