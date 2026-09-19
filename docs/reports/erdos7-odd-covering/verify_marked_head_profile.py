#!/usr/bin/env python3
"""Verify the complete 315 marked-head convex profile using exact arithmetic.

The adjacent fixed certificate contains finite results, not executable input.
Every old-head layout histogram, ordered histogram pair, integer survivor
count and integer threshold is checked.  Only the Python standard library is
used.  The universal pruning and convex-rearrangement argument is stated in
marked_head_profile.md; this program verifies its finite calculation.
"""

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

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


MODULI = (3, 5, 9, 15, 45)
CATEGORIES = ("same_other_column", "other_same_column", "other_other_column")
THRESHOLDS = range(13)



# The entrypoint source pin transitively binds every split arithmetic module.
_SPLIT_SOURCE_SHA256 = {'head_profile/base.py': '5652bb18628e5d61fae8d6a2fb2b2c0ef760ee09d90f8bfa9872809052949fe1',
 'head_profile/hinges.py': '9adf17496d7370495b18b2cc22735ba9cad881d3005888450b52003c97928c04',
 'head_profile/holes.py': '5c2c1c012822a50cfc9ffde804f0d67746a243e29c9f98fbb5b2a573fdf08f0a',
 'head_profile/moments.py': 'c34893473b505bbf791af642e54fccb97a08a6e95bbdbff4bb4f80f690778321',
 'head_profile/rectangles.py': '00d8e072df53621141389f9b307ea0338fac7ed26692f12038dc46b030e7ce96',
 'head_profile/source.py': '808c5925e070e3d990558ec8efad4354c1ba7ae11331ac5adca4ca8c7c40fa67'}
for _relative, _pin in _SPLIT_SOURCE_SHA256.items():
    if _certificate_sha256((_certificate_root / _relative).read_bytes()).hexdigest() != _pin:
        raise ValueError("split arithmetic source SHA-256 mismatch: " + _relative)

from head_profile.base import *
from head_profile.source import *
from head_profile.moments import *
from head_profile.holes import *
from head_profile.rectangles import *
from head_profile.hinges import *

def verify(expected):
    cases = []
    old_cases = []
    for root, category in product((1, 2), CATEGORIES):
        points, histograms, layouts, maxima = old_head(root, category)
        old_cases.append((f"root{root}_{category}", points, histograms, layouts))
        n = len(points)
        minimum = 6 * n - sum(maxima)
        profile, checked = complete_profile(n, histograms, minimum)
        require(checked == len(histograms) ** 2 * (6 * n - minimum + 1),
                "all ordered histogram pairs and integer survivor counts checked")
        cases.append({
            "shape": f"root{root}_{category}",
            "old_survivors": n,
            "test_layouts": layouts,
            "distinct_histograms": len(histograms),
            "old_cylinder_maxima_in_modulus_order": maxima,
            "survivor_count_range_inclusive": [minimum, 6 * n],
            "ordered_histogram_pair_count_cases": checked,
            "integer_hinge_cases": 13 * checked,
            "profile": list(map(str, profile)),
        })
    theta = [max(Fraction(row["profile"][t]) for row in cases) for t in THRESHOLDS]
    atoms = {k: theta[k - 1] - 2 * theta[k] + (theta[k + 1] if k < 12 else 0)
             for k in range(1, 13)}
    require(all(p >= 0 for p in atoms.values()) and sum(atoms.values()) == 1,
            "auxiliary atoms form a probability law")
    for t in THRESHOLDS:
        require(sum(p * max(k - t, 0) for k, p in atoms.items()) == theta[t],
                "auxiliary law has the entire universal hinge profile")
    deletion_result = deletion_weighted_comparison(old_cases, theta)
    signed_result = signed_deletion_square_comparison(old_cases, deletion_result)
    lift_result = matching_height_lift()
    variable_head = varying_hole_head(deletion_result, signed_result)
    shared_head = shared_count_clipped_head(old_cases, deletion_result, signed_result)
    rectangle_moments = common_rectangle_moment_bounds(
        shared_head, expected['common_rectangle_moment_bounds']['diagonal_witness'])
    hinge_profile = actual_rectangle_hinge_profile(
        expected["actual_rectangle_hinge_profile"]["witnesses"], shared_head, deletion_result, cases)
    fixed_hinge = fixed_count_hinge_refinement(
        fixed_count_joint_cost_comparison(old_cases), shared_head, deletion_result, hinge_profile)
    joint_hinge = joint_cost_hinge_refinement(
        old_cases, shared_head, deletion_result, hinge_profile, fixed_hinge)
    result = {
        "common_rectangle_moment_bounds": rectangle_moments,
        "joint_cost_branch_tail17": joint_cost_branch_tail17(shared_head, deletion_result, joint_hinge),
        "joint_cost_hinge_refinement": joint_hinge,
        "fixed_count_hinge_refinement": fixed_hinge,
        "actual_rectangle_hinge_profile": hinge_profile,
        "rectangle_hinge_observation_gap": rectangle_hinge_observation_gap(),
        "shared_count_clipped_head": shared_head,
        "variable_axis_clipping": variable_axis_clipped_head(expected["variable_axis_clipping"]["witnesses"], deletion_result, signed_result),
        "signed_conditioning_obstruction": signed_conditioning_obstruction(),
        "schema": "marked-head-profile-v1",
        "head_modulus": 315,
        "old_moduli_order": list(MODULI),
        "thresholds": list(THRESHOLDS),
        "cases": cases,
        "universal_profile": list(map(str, theta)),
        "auxiliary_atoms": {str(k): str(p) for k, p in atoms.items() if p},
        "mean": str(sum(k * p for k, p in atoms.items())),
        "second_moment": str(sum(k * k * p for k, p in atoms.items())),
        "sharp_example": sharp_example(theta),
        "elementary_comparison": elementary_comparison(old_cases, theta),
        "fixed_marginal_obstruction": fixed_marginal_obstruction(),
        "deletion_weighted_comparison": deletion_result,
        "conditioned_3465_comparison": conditioned_3465_comparison(deletion_result, signed_result),
        "signed_deletion_square_comparison": signed_result,
        "uniform315_energy_rebate_obstruction": uniform315_energy_rebate_obstruction(signed_result),
        "two_prime_block_grid_comparison": two_prime_block_grid_comparison(),
        "two_prime_block_gap": two_prime_block_gap_regression(),
        "punctured_grid_nonuniform_transfer": punctured_grid_nonuniform_transfer(signed_result),
        "matching_hole_common_lambda": matching_hole_common_lambda(),
        "matching_height_lift": lift_result,
        "arbitrary_hole_degree_symbolic": arbitrary_hole_degree_symbolic(),
        "varying_hole_head": variable_head,
        "arbitrary_holes12_tail17": arbitrary_holes12_tail17(variable_head["rows"][-1]),
        "matching_height_tail17": matching_height_tail17(deletion_result, lift_result),
        "uniform315_mean_sharpness": uniform315_mean_sharpness(),
        "residual_prefix_depletion_obstruction": residual_prefix_depletion_obstruction(),
        "prime11_residual_geometry": prime11_residual_geometry(),
        "residual_mass_next_label_obstruction": residual_mass_next_label_obstruction(),
    }
    require(result == expected, "computed exact result differs from the fixed certificate")
    print(json.dumps({"verified": True, "old_test_layouts": sum(r["test_layouts"] for r in cases),
                      "integer_hinge_cases": sum(r["integer_hinge_cases"] for r in cases),
                      "mean": result["mean"], "second_moment": result["second_moment"],
                      "deletion_weighted_inequalities": result["deletion_weighted_comparison"]["integer_cap_inequalities"],
                      "deletion_weighted_mean": result["deletion_weighted_comparison"]["mean"],
                      "deletion_weighted_actual_second": result["deletion_weighted_comparison"]["actual_second_moment_upper"],
                      "sharp_actual_second": signed_result["actual_second_moment_upper"],
                      "block_gap_regressions": result["two_prime_block_gap"]["grid_coefficient_cases"],
                      "nonuniform_block_factor": result["punctured_grid_nonuniform_transfer"]["Gamma_and_tensorization_constant"],
                      "matching_hole_symbolic_identities": len(result["matching_hole_common_lambda"]["symbolic_identities"]),
                      "matching_height_tail17_Gamma": result["matching_height_tail17"]["Gamma_upper"],
                      "arbitrary_holes12_tail17_Gamma": result["arbitrary_holes12_tail17"]["Gamma_upper"],
                      "common_rectangle_Gamma": rectangle_moments["Gamma_upper"],
                      "common_rectangle_first": rectangle_moments["same_law_first_upper"],
                      "shared_count_clipped_Gamma": result["shared_count_clipped_head"]["actual_rectangle_refinement"]["Gamma_upper"],
                      "shared_count_branches": result["shared_count_clipped_head"]["shared_branches_verified"],
                      "full_fibre_branch_tail17_Gamma": result["joint_cost_branch_tail17"]["Gamma_upper"],
                      "joint_cost_full_hinge6": result["joint_cost_hinge_refinement"]["universal_full_hinge_upper_at_4_through_12"][2],
                      "fixed_count_full_hinge6": result["fixed_count_hinge_refinement"]["universal_full_hinge6_upper"],
                      "actual_rectangle_hinge6": result["actual_rectangle_hinge_profile"]["universal_full_hinge_upper_at_4_through_12"][2],
                      "conditioned_3465_actual_second": result["conditioned_3465_comparison"]["actual_second_moment_upper"]}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/marked_head_profile_certificate.json'))
    args = parser.parse_args()
    verify(json.loads(read_artifact_text(args.certificate)))


if __name__ == "__main__":
    main()
