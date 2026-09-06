"""Interval transport of the existing c=3 candidate to normalized Fourier readouts.

This does NOT rerun or validate the upstream spectral enclosure. Its exact
energy numbers are explicit premises. The Fourier basis is V_n(t)=(-1)^n
exp(2*pi*i*n*t/L)/sqrt(L), L=log(3), t in [-L/2,L/2]. Dropping (-1)^n changes
the candidate. Analytic Fourier/Riesz and actual operator-domain bridges
remain mathematical premises, not facts inferred from a JSON success label.

Run beside the unchanged certify_prime3_refined.py and the separately
produced prime3_neumann_weighted_certificate.json. The source is parsed as
AST data; none of its code, eigensolvers, or zeta-zero routines is executed.
Every acceptance comparison uses mpmath directed intervals or Fraction.
"""
from __future__ import annotations

import argparse
import ast
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any

import mpmath
from mpmath import iv

SOURCE_BLOB = "a8690fc54e79d1a80b12aeca2ce4837bb9e585af"
CERTIFICATE_BLOB = "bee31b4b002be2c1cff78a53689232a5d87662b5"
POINTS = (("1", "0"), ("1", "1/4"), ("4", "1/4"),
          ("8", "1/4"), ("14", "0"), ("14", "1/4"), ("20", "1/4"))


def require(condition: Any, message: str) -> None:
    if not bool(condition):
        raise ArithmeticError(message)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def Q(value: str | int | Fraction) -> Any:
    value = Fraction(value)
    return iv.mpf(value.numerator) / value.denominator


def norm_sq(z: Any) -> Any:
    return z.real**2 + z.imag**2


def conj(z: Any) -> Any:
    return iv.mpc(z.real, -z.imag)


def display(z: Any) -> Any:
    """Intervals are retained as strings. Displays never feed acceptance."""
    if hasattr(z, "imag") and not bool(z.imag == 0):
        return {"real": str(z.real), "imag": str(z.imag)}
    return str(z.real if hasattr(z, "real") else z)


def read_inputs(source: Path, certificate: Path) -> tuple[tuple[int, ...], Fraction, dict[str, str]]:
    source_bytes = source.read_bytes()
    certificate_bytes = certificate.read_bytes()
    require(git_blob(source_bytes) == SOURCE_BLOB, "Candidate source differs from the reviewed blob")
    require(git_blob(certificate_bytes) == CERTIFICATE_BLOB, "Spectral premise differs from the reviewed blob")
    candidates = []
    for node in ast.parse(source_bytes.decode("utf-8")).body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "CANDIDATE" for t in node.targets):
            candidates.append(ast.literal_eval(node.value))
    require(len(candidates) == 1, "CANDIDATE must have one literal owner")
    coefficients = tuple(candidates[0])
    require(len(coefficients) == 129 and all(type(x) is int for x in coefficients), "Expected 129 integer coefficients")
    require(coefficients == coefficients[::-1], "Candidate is not even")
    require(sum(x*x for x in coefficients) > 0, "Zero candidate")
    data = json.loads(certificate_bytes)
    require(data["N"] == 64 and data["scale"] == "a=log(3)/2", "Incompatible scale")
    ell, upper, threshold = (Fraction(data[k]) for k in ("ground_lower", "candidate_upper", "orthogonal_threshold"))
    require(ell < upper < threshold, "Invalid energy ordering")
    error = (upper - ell) / (threshold - ell)
    require(error == Fraction(data["projective_distance_sq_upper"]), "Projective ratio does not match energy data")
    require(error == Fraction(44669457, 489267186193) and error < Fraction(1, 10000), "Unexpected error premise")
    return coefficients, error, {"candidate_git_blob": git_blob(source_bytes),
                                "energy_premise_git_blob": git_blob(certificate_bytes)}


def certify(source: Path, certificate: Path, digits: int = 70) -> dict[str, Any]:
    require(digits >= 40, "Insufficient interval precision")
    iv.dps = digits
    coeff, error, hashes = read_inputs(source, certificate)
    length = iv.ln(3)
    half = length / 2
    integer_energy = sum(x*x for x in coeff)
    scale = iv.sqrt(iv.mpf(integer_energy))
    k = [iv.mpf(x) / scale for x in coeff]
    e = Q(error)
    d = iv.mpc(iv.sqrt(length) * k[64], 0)
    U = length - norm_sq(d)
    D = norm_sq(d) - e * U
    require(U > 0 and D > Q("647/1000"), "Anchor square margin failed")
    anchor_floor = abs(d) - iv.sqrt(e * U)
    require(anchor_floor > Q("797/1000"), "Anchor modulus lower bound failed")

    points = []
    for real, imaginary in POINTS:
        x, y = Q(real), Q(imaginary)
        z = iv.mpc(x, y)
        # The translated-basis phase cancels the integer sine sign exactly.
        # All chosen points are away from the removable sinc poles.
        partial = iv.mpc(0)
        for n in range(-64, 65):
            denom = z - 2 * iv.pi * n / length
            require(norm_sq(denom) > 0, "Unresolved Fourier denominator")
            partial += k[n + 64] / denom
        A = 2 * iv.sin(half * z) / iv.sqrt(length) * partial
        full_C = 2 * iv.sin(half * z) / z
        if Fraction(imaginary) == 0:
            hyperbolic = half
        else:
            # iv.sinh is not exposed by every mpmath interval version.
            hyperbolic = (iv.exp(length*y) - iv.exp(-length*y)) / (4*y)
        full_V = hyperbolic + iv.sin(length*x) / (2*x)
        V = full_V - norm_sq(A)
        C = full_C - A * conj(d)
        require(V > 0, "Numerator residual energy not certified positive")
        determinant = U*V - norm_sq(C)
        require(determinant > 0, "Projected readout Gram determinant failed")
        B = A*conj(d) - e*C
        numerator = norm_sq(B) - D*(norm_sq(A) - e*V)
        # A separately expanded formula detects sign/conjugation mistakes.
        numerator_expanded = e*(norm_sq(d)*V + norm_sq(A)*U
            - 2*(d*conj(A)*C).real - e*determinant)
        require(numerator > 0 and numerator_expanded > 0, "Disk square radius failed")
        require(not bool(numerator.a > numerator_expanded.b) and
                not bool(numerator_expanded.a > numerator.b), "Disk expansions are disjoint")
        center = B/D
        radius = iv.sqrt(numerator)/D
        reference = A/d
        joint_error = abs(center-reference) + radius
        separate_budget = iv.sqrt(e)*(iv.sqrt(V) + abs(reference)*iv.sqrt(U))/anchor_floor
        if (real, imaginary) == ("1", "1/4"):
            require(joint_error < Q("3/4000"), "Main normalized transform certificate failed")
            require(separate_budget > Q("3/200"), "Budget-comparison lower bound failed")
        points.append({"z": [real, imaginary], "candidate_ratio": display(reference),
                       "disk_center": display(center), "disk_radius": display(radius),
                       "error_from_candidate_upper_interval": display(joint_error),
                       "independent_triangle_budget_interval": display(separate_budget),
                       "projected_gram_determinant": display(determinant),
                       "zero_status": ("excluded" if bool(abs(center) > radius)
                                       else "contained" if bool(abs(center) < radius)
                                       else "undetermined")})

    return {"status": "all directed-interval transport comparisons passed",
            "scale": "a=log(3)/2", "interval_decimal_precision": digits,
            "mpmath": mpmath.__version__, "input_hashes": hashes,
            "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "candidate_integer_energy": str(integer_energy), "projective_error_square_premise": str(error),
            "anchor_D": display(D), "anchor_modulus_floor": display(anchor_floor),
            "certified_anchor_modulus_lower": "797/1000",
            "main_point": ["1", "1/4"], "main_error_upper": "3/4000",
            "independent_budget_lower_at_main_point": "3/200",
            "anchor_query": {"z": ["0", "0"], "ratio": "1", "radius": "0", "reason": "identical numerator and denominator"},
            "points": points,
            "premises": ["Upstream energy inequalities and actual form/operator identification, not replayed here",
                         "The normalized finite vector belongs to the translated V_n basis from arXiv:2511.22755v1",
                         "Even L2 Fourier/Riesz identification and the certified projective error bound"],
            "not_claimed": ["Lean kernel acceptance", "a new spectral enclosure", "uniform-in-frequency coverage from these seven points",
                            "a zero-free disk around every sampled point", "an unbounded-scale Xi limit", "Riemann hypothesis"]}


def main() -> None:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=root/"certify_prime3_refined.py")
    parser.add_argument("--certificate", type=Path, default=root/"prime3_neumann_weighted_certificate.json")
    parser.add_argument("--output", type=Path, default=root/"prime3_normalized_readout_certificate.json")
    parser.add_argument("--digits", type=int, default=70)
    args = parser.parse_args()
    result = certify(args.source, args.certificate, args.digits)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("status", "candidate_integer_energy", "main_error_upper",
        "certified_anchor_modulus_lower", "input_hashes")}, indent=2))


if __name__ == "__main__":
    main()
