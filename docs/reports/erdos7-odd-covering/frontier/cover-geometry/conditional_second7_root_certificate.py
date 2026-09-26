#!/usr/bin/env python3
"""Exact full-cost gate for a second7-root on a fixed ternary leaf set.

All64 masks and all11400 literal pure-source corners are accounted for.
Identical complete selector descriptors share their exact arithmetic value.
This certifies the theta=1 envelope, not unrestricted noncoverage or a maximum
over thinnings. The ordinary same-source proof supplies all-height scope.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
from hashlib import sha256
from math import prod
import argparse
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-certificate', type=Path, default=Path(__file__).with_name('remaining33_global_root_exclusion_certificate.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    raw = args.source_certificate.read_bytes()
    source = json.loads(raw)
    co = list(map(F, source['combined512_coefficients']))
    h = list(map(F, source['all32_outside_responses']))
    g, alpha = (F(source['constants'][k]) for k in ('g', 'alpha'))
    checks = Counter()
    def ck(name, predicate):
        if not predicate:
            raise ArithmeticError(name)
        checks[name] += 1
    ck('complete512_nonnegative_costs', len(co) == 512 and min(co) >= 0)
    primes = (7,11,13,17,19)
    for support in range(32):
        ck('outside_factors_from_actual_root_mass', h[support] == prod(F(q-2,q-1) for i,q in enumerate(primes) if not support >> i & 1))
    ck('second7_root_ratio', F(4,6)/F(5,6) == F(4,5))
    fees = [[sum((co[32*m+T]*h[T] for T in range(32) if (T&1) == has7), F()) for m in range(16)] for has7 in (0,1)]
    for mode in range(16):
        ck('all_support_fees_retained', fees[0][mode]+fees[1][mode] == sum((co[32*mode+T]*h[T] for T in range(32)),F()))

    def axis(n, root_size, null, weak, regular_mass, weak_mass, deep, patch):
        weights = [0 if i == null else weak_mass if i == weak else regular_mass for i in range(n)]
        vectors = [[weights],
                   [[weights[i] if i//root_size == r else 0 for i in range(n)] for r in range(n//root_size)],
                   [[weights[i] if i == j else 0 for i in range(n)] for j in range(n) if weights[j]],
                   [[deep if i == j else 0 for i in range(n)] for j in range(n) if weights[j]]]
        # Retain precisely the four sums used by both response matrices.
        return tuple(tuple(sorted(set((sum(x),sum(x[:root_size]),sum(x[i] for i in patch),sum(x[i] for i in patch if i < root_size)) for x in menu))) for menu in vectors)

    ys = [(z,w,axis(20,5,z,w,4,3,60,())) for z,w in product(range(20),repeat=2) if z != w]
    cache, records, profiles = {}, [], {}
    corner_count = 0
    for mask in range(64):
        patch = [l for l in range(6) if mask >> l & 1]
        xs = [(z,w,axis(6,3,z,w,2,1,9,patch)) for z,w in product(range(6),repeat=2) if z != w]
        minimum, witness, ties, counted = None, None, 0, 0
        for z,w,ax in xs:
            for zz,ww,ay in ys:
                counted += 1
                key = (ax,ay)
                if key not in cache:
                    original, modified = [], []
                    for e3,e5 in product(range(4),repeat=2):
                        forms = [(x[0]*y[0]-x[1]*y[1], x[2]*y[0]-x[3]*y[1]) for x in ax[e3] for y in ay[e5]]
                        ck('nonnegative_actual_patch_forms', all(0 <= penalty <= value for value,penalty in forms))
                        original.append(max(value for value,penalty in forms))
                        modified.append(max(5*value-penalty for value,penalty in forms))
                    cache[key] = g*h[0]*F(modified[0],3375) - sum((fees[0][m]*F(modified[m],3375)+fees[1][m]*F(original[m],675) for m in range(16)),F())
                value = cache[key]
                if minimum is None or value < minimum:
                    minimum, witness, ties = value, [z,w,zz,ww], 1
                elif value == minimum:
                    ties += 1
        ck('literal11400_corners_per_mask', counted == 11400)
        corner_count += counted
        ck('strict_gate_sign', minimum != 0)
        profile = (sum(l < 3 for l in patch),sum(l >= 3 for l in patch))
        expected_positive = profile[0] == 0 or profile[0] == 1 and profile[1] <= 1 or profile == (2,0)
        ck('complete_positive_region', (minimum > 0) == expected_positive)
        record = dict(mask=mask, leaves=patch, profile=list(profile), minimum=str(minimum), haar=str(alpha*minimum), witness=witness, minimizing_corner_count=ties)
        records.append(record)
        if profile in profiles:
            ck('direct_cardinality_profile_agreement', profiles[profile]['minimum'] == record['minimum'])
            profiles[profile]['mask_count'] += 1
        else:
            profiles[profile] = dict(profile=list(profile), minimum=record['minimum'], haar=record['haar'], representative_mask=mask, witness=witness, mask_count=1)
    ck('all_masks_and_corners_accounted', corner_count == 64*11400 and len(records) == 64 and len(profiles) == 16)
    ck('base640_recovered', F(records[0]['minimum']) == F(23282735008494655373261,638394875922057408000000))
    ck('global_two_root642_recovered', F(records[63]['minimum']) == F(-203208177531255678309923,20428636029505837056000000))
    positives = [r for r in records if F(r['minimum']) > 0]
    ck('23_positive_masks', len(positives) == 23)
    worst = min(F(r['minimum']) for r in positives)
    ck('minimum_positive_gate', worst == F(41908790232778304321,59732853887443968000000))
    tail = F(19740202146111572828188083,495176015714152109959649689600)
    ck('uniform_head_haar_bound', alpha*worst > F(1,60000))
    ck('uniform_large_owner_haar_bound', alpha*(worst-tail) > F(1,65000))
    full_fee = F(1411,100000)+F(1,65536)+tail
    network_rows = []
    for profile,r in sorted(profiles.items()):
        margin = alpha*(F(r['minimum'])-full_fee)
        if margin > 0:
            network_rows.append(dict(profile=list(profile), projected_margin=str(margin)))
    ck('complete_network_positive_profiles', [r['profile'] for r in network_rows] == [[0,0],[1,0]])
    ck('one_root0_leaf_network_bound', F(network_rows[1]['projected_margin']) > F(1,4250))
    out = dict(schema='conditional-second7-root-full-gate-v1', scope=__doc__,
               source_certificate_sha256=sha256(raw).hexdigest(),
               outside_primes=list(primes), constants=dict(g=str(g),alpha=str(alpha)),
               unqueried7_fees=list(map(str,fees[0])),queried7_fees=list(map(str,fees[1])),
               source_corner_pairs_accounted=corner_count, distinct_complete_menu_pairs=len(cache),
               positive_mask_count=len(positives), mask_records=records,
               cardinality_profiles=[v for k,v in sorted(profiles.items())],
               minimum_positive_gate=str(worst),uniform_head_haar=str(alpha*worst),
               uniform_large_owner_projected_haar=str(alpha*(worst-tail)),
               complete_network_positive_profiles=network_rows,
               check_count=sum(checks.values()),checks=dict(checks),new_lean_verification=False)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ('source_corner_pairs_accounted','distinct_complete_menu_pairs','positive_mask_count','minimum_positive_gate','uniform_head_haar','uniform_large_owner_projected_haar','complete_network_positive_profiles','check_count')},indent=2))


if __name__ == '__main__':
    main()
