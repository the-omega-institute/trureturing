#!/usr/bin/env python3
"""Exact nonuniform survivor-law certificate for a fixed rectangular family.

Python3.9+ standard library only. The accompanying proof establishes the
all-height residue geometry and product-cylinder transfer. This checks the
uniform-in-height rational constants and all primes through73.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from math import isqrt, prod
from pathlib import Path
import json


def require(condition,message):
    if not condition:
        raise ValueError(message)


def compute_certificate():
    primes=tuple(p for p in range(7,74) if all(p%d for d in range(2,isqrt(p)+1)))
    require(primes==(7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73),
            'prime interval mismatch')
    w_min=3*sum(F(1,3**e) for e in range(2,6))
    w_sup=F(1,2)
    h,k=F(1),F(4,3)
    require(w_min==F(40,81),'ternary width at H=5 mismatch')
    endpoint_caps=[]
    for w in (w_min,w_sup):
        caps=(2,1+F(2,3)*k,k*(w+1),k*w+F(2,3))
        require(all(value<=2 for value in caps),'weighted-root moment cap failed')
        endpoint_caps.append(list(map(str,caps)))
    # Every cap is affine in w, so the endpoint check covers the full interval.
    require(F(2,3)*max(h,k)<=2,'zero-root test branch failed')
    raw_mass_lower=(1+k*w_min)/3
    require(raw_mass_lower==F(403,729)>0,'raw-law mass lower bound failed')
    gamma_3=1+2/raw_mass_lower
    require(gamma_3==F(1861,403),'ternary Gamma mismatch')
    remaining_5_density_lower=F(1,2)
    point_cap_5=1/remaining_5_density_lower
    lcm_weight_5=F(3*5-1,(5-1)**2)
    transfer_5=1+point_cap_5*lcm_weight_5
    require(transfer_5==F(11,4),'quinary cylinder transfer mismatch')
    gamma_35=gamma_3*transfer_5
    require(gamma_35==F(20471,1612),'two-prime Gamma mismatch')
    rows=[]
    for p in primes:
        survivor_density_lower=F(p-2,p-1)
        point_cap=1/survivor_density_lower
        lcm_weight=F(3*p-1,(p-1)**2)
        transfer=1+point_cap*lcm_weight
        require(transfer==F(p*p+1,(p-1)*(p-2)),
                'pure-prime cylinder transfer identity failed')
        rows.append({'prime':p,'survivor_density_lower':str(survivor_density_lower),
                     'point_cap':str(point_cap),'transfer_factor':str(transfer)})
    tail=prod(F(row['transfer_factor']) for row in rows)
    total=gamma_35*tail
    threshold=F(138877,1000)
    require(total==F(64245900555623296761826781321804225,
                    479017695593451697408733725605888),'full head constant mismatch')
    require(total<F(134121,1000)<threshold,'continuation threshold comparison failed')
    return {'schema':'rectangular-family-nonuniform-v1','common_height_minimum':5,
            'scope':'specified forbidden family; existence of a supported nonuniform law',
            'ternary_raw_root_multipliers':[str(h),str(k)],
            'ternary_second_root_width_interval':[str(w_min),str(w_sup)],
            'ternary_width_upper_endpoint_is_limit':True,
            'weighted_root_cap_endpoint_values':endpoint_caps,
            'ternary_raw_mass_lower':str(raw_mass_lower),
            'Gamma_3_bound':str(gamma_3),
            'quinary_remaining_density_lower':str(remaining_5_density_lower),
            'quinary_transfer_factor':str(transfer_5),'Gamma_35_bound':str(gamma_35),
            'remaining_prime_transfers':rows,'remaining_prime_product':str(tail),
            'Gamma_73_bound':str(total),'decimal_upper_bound':'134121/1000',
            'continuation_threshold':str(threshold),'threshold_margin':str(threshold-total)}


def main():
    path=(Path(__file__).resolve().parents[1] / 'certificates/rectangular_family_nonuniform_certificate.json')
    data=json.loads(read_artifact_text(path))
    expected=compute_certificate()
    require(data==expected,'fixed certificate differs from exact recomputation')
    print('Verified the specified family for every common height H>=5: '
          'Gamma <= '+expected['Gamma_73_bound']+' <134.121<138.877.')
    print('All raw-law normalizers are positive; the proof supplies actual survivor support.')


if __name__=='__main__':
    main()
