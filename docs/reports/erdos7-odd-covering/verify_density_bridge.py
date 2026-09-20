#!/usr/bin/env python3
"""Exact arithmetic consumer for DV -> actual AP killed-law domination.

The mathematical restriction is original 357 part dividing 315. Original
11/13/17/19 cofactors and finite heights remain arbitrary. This program
checks the pinned DV inputs and rational consequences, not the ordinary
measure-domination proof and not the upstream 161375-vector enumeration.
Use the existing verify_actual_deletion_profile.py for that reconstruction.
Only the Python standard library is needed here; -I -O is supported.
"""
from __future__ import annotations

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path


DV_SHA256 = "809cb45859825890c3f90b1f6e4821086ffcc9f01e91e0ea08e56a10e44a90ac"
UPSTREAM_SHA256 = "43ee37b084b09a9574b5e53a2ae5c0d79180202c453ce991e3838c5457662c13"


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def canonical_digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def verify(source_path, upstream_path):
    raw = read_artifact_bytes(source_path)
    require(sha256(raw).hexdigest() == DV_SHA256, "exact DV source certificate SHA-256")
    source = json.loads(raw, object_pairs_hook=unique)
    upstream = json.loads(read_artifact_text(upstream_path), object_pairs_hook=unique)
    selected = {key: upstream[key] for key in source["source_certificate_sections"]}
    require(canonical_digest(selected) == source["source_sections_sha256"] == UPSTREAM_SHA256,
            "exact original DV upstream sections")
    require(source["all_optional_deletion_vectors"] == 161375, "DV geometry inventory")
    require(source["old_test_layouts"] == 27720, "DV old test inventory")
    require(min(row["N_range"][0] for row in source["cases"]) == 74, "pruned carrier lower count")
    G = F(source["Gamma_upper"]["bound"])
    M = F(source["mean_upper"]["bound"])
    ell = F(source["reference_fraction_lower"]["bound"])
    require(G == F(591122424341, 16497075000), "DV same-law square input")
    require(M == F(1175795, 219961), "DV same-law mean input")
    require(ell == F(108683, 204000), "DV same-law reference fraction input")
    hinges = {row["threshold"]: F(row["bound"])
              for row in source["full_hinge_upper_at_4_through_12"]}
    require(sorted(hinges) == list(range(4, 13)), "complete DV hinge inputs")

    reference_density = F(315, 74) * F(11, 10) * F(13, 12)
    D = reference_density / ell
    require(D == F(38288250, 4021271), "common-carrier density domination")
    charge_bounds = {}
    for p, input_square in ((17, G), (19, F(89, 64)*G)):
        delta = F(7, p-2)
        pure_lower = F(p-2, p-1)
        cap = 1/(pure_lower*(1-delta))
        bound = (input_square-1)/((p-2)**2*4*delta*(1-delta))
        require(bound == (input_square-1)/(28*(p-9)), "full-height square charge algebra")
        charge_bounds[str(p)] = {"delta": str(delta), "pure_mass_lower": str(pure_lower),
                                 "physical_Haar_cap": str(cap), "input_square_upper": str(input_square),
                                 "charge_upper": str(bound)}
    cap17 = F(charge_bounds["17"]["physical_Haar_cap"])
    # sum_{m>=1}(2m+1)z^m = 2z/(1-z)^2 + z/(1-z).
    z = F(1, 17)
    factor17 = 1+cap17*(2*z/(1-z)**2+z/(1-z))
    require(cap17 == 2 and factor17 == F(89, 64), "original-depth pair transfer")
    b17 = F(charge_bounds["17"]["charge_upper"])
    b19 = F(charge_bounds["19"]["charge_upper"])
    b = b17+b19
    require(b == F(97524110913629, 295627584000000), "two-stage lost mass")
    require(0 < b < 1, "positive auxiliary survival")

    bands = []
    for h in range(1, 13):
        candidates = {"total_mass": F(1), "mean_floor": (M-1)/h,
                      "square_floor": (G-1)/((h+1)**2-1)}
        candidates.update({f"hinge_{t}": v/(h+1-t) for t,v in hinges.items() if t<=h})
        choice = min(candidates, key=candidates.get)
        tail = candidates[choice]
        auxiliary = max(F(0), 1-tail-b)
        mass = auxiliary/D
        row = {"h": h, "tail_candidates": {k:str(v) for k,v in candidates.items()},
               "selected_tail_bound": choice, "auxiliary_tail_upper": str(tail),
               "auxiliary_killed_band_lower": str(auxiliary), "actual_killed_band_lower": str(mass),
               "mean_only_actual_lower": str(max(F(0), 1-(M-1)/h-b)/D)}
        row["CT_band_deficits"] = {str(tau): str((tau-h*h)*mass)
                                  for tau in (81, 121) if h*h<tau}
        bands.append(row)
    require(F(bands[7]["actual_killed_band_lower"]) ==
            F(95114429591641272698674519, 2214676516815754992000000000), "band8 fraction")
    require(F(bands[9]["actual_killed_band_lower"]) ==
            F(54305460404654859422887321, 1006671144007161360000000000), "band10 fraction")
    require(bands[7]["selected_tail_bound"] == "hinge_6", "band8 same-law hinge")
    require(bands[9]["selected_tail_bound"] == "hinge_7", "band10 same-law hinge")

    direct = {}
    for tau in (64, 81, 100, 121, 484):
        numerator = max(F(0), tau-G-(tau-1)*b)
        direct[str(tau)] = {"auxiliary_lower": str(numerator), "actual_deficit_lower": str(numerator/D)}
    require(F(direct["81"]["actual_deficit_lower"]) ==
            F(93008506203820579159, 47162761846200000000), "direct CT81")
    require(F(direct["121"]["actual_deficit_lower"]) ==
            F(20841212131452733423, 4353485708880000000), "direct CT121")
    return {
        "schema": "erdos7-dv-actual-density-bridge-v1",
        "scope": "original357 part divides315; actual AP11/T4 AP13/T6 source; arbitrary original11/13/17/19 cofactors and finite heights; same actual killed17/T8 killed19/T8 kernels; ordinary proof plus rational arithmetic, not Lean or unrestricted continuation",
        "verification_boundary": "consumer checks source hashes and rational consequences; upstream DV geometry and ordinary universal measure proof remain separate inputs",
        "source_sha256": DV_SHA256, "upstream_sections_sha256": UPSTREAM_SHA256,
        "inputs": {"G": str(G), "M": str(M), "ell": str(ell),
                   "hinges": {str(k):str(v) for k,v in hinges.items()}},
        "reference_Haar_density_upper": str(reference_density), "density_domination_D": str(D),
        "physical17_square_factor": str(factor17), "charges": charge_bounds,
        "two_stage_loss_upper": str(b), "bands": bands, "direct_CT_deficits": direct}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-certificate", type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/actual_deletion_profile_certificate.json'))
    parser.add_argument("--upstream-profile", type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/marked_head_profile_certificate.json'))
    parser.add_argument("--write", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = verify(args.source_certificate, args.upstream_profile)
    if args.check:
        require(result == json.loads(read_artifact_text(args.check), object_pairs_hook=unique), "saved density-bridge result matches reconstruction")
    if args.write:
        write_certificate_text(args.write, json.dumps(result, indent=2)+"\n")
    print(json.dumps({"density_domination_D": result["density_domination_D"],
                      "band8": result["bands"][7]["actual_killed_band_lower"],
                      "band10": result["bands"][9]["actual_killed_band_lower"],
                      "direct_CT_deficits": result["direct_CT_deficits"]}, separators=(",", ":")))


if __name__ == "__main__":
    main()
