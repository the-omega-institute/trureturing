# FiveRowP2Nineteen

## Abstract

The dimension-nineteen estimate holds throughout the real concentration interval. Three quartic certificates and the scalar constraints control the low and middle parameter regions.

The dimension-nineteen estimate holds throughout the real concentration interval. Three quartic certificates and the scalar constraints control the low and middle parameter regions.

**Theorem 1.1 (concentrated nineteen).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Nineteen.concentrated_nineteen`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Nineteen.concentrated_nineteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_nineteen (r H D a q s j : ℝ) (h : Hyp r H D a q s) (hj : 10 ≤ j) (hj' : j ≤ 80) : energy 95 j r H D a q ≤ (5/456)*(mass 95 j r H D)^2

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Nineteen.concentrated_nineteen`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates](FiveRowP2Certificates.md)
