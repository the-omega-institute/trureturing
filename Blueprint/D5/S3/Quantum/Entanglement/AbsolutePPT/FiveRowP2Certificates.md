# FiveRowP2Certificates

## Abstract

Exact rational polynomial identities certify the upper and small-tail branches of the five-row scalar relaxation. Every coefficient and inequality is a real algebraic statement.

Exact rational polynomial identities certify the upper and small-tail branches of the five-row scalar relaxation. Every coefficient and inequality is a real algebraic statement.

**Theorem 1.1 (upper certificate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.upper_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.upper_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem upper_certificate {r H D a q s : ℝ} (h : Hyp r H D a q s) (hr : 1/5 ≤ r) : W r H D a q ≤ B r

**Theorem 1.2 (smallq certificate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.smallq_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.smallq_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem smallq_certificate {r H D a q s : ℝ} (h : Hyp r H D a q s) (hr : 1/12 ≤ r) (hr' : r ≤ 1/5) (hq : q ≤ 1) : W r H D a q ≤ B r

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.smallq_certificate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.upper_certificate`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar](FiveRowP2Scalar.md)
