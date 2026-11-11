# SixRowHeadCertificate

## Abstract

A binary midpoint partition covers the complete scalar box, including every boundary face. Its 119 positive leaves use exact homogeneous Bernstein identities. Its 99 excluded leaves have a strictly negative upper bound for the feasibility polynomial. The polynomial is therefore nonnegative at every feasible point.

A binary midpoint partition covers the complete scalar box, including every boundary face. Its 119 positive leaves use exact homogeneous Bernstein identities. Its 99 excluded leaves have a strictly negative upper bound for the feasibility polynomial. The polynomial is therefore nonnegative at every feasible point.

**Theorem 1.1 (polynomial nonneg).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem polynomial_nonneg (z k h : ℝ) (hz : 0 ≤ z) (hZ : z ≤ 3/4) (hk : 0 ≤ k) (hK : k ≤ 1) (hh : 0 ≤ h) (hH : h ≤ 3/2) (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain03](SixRowHeadCertificate/Domain03.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain04](SixRowHeadCertificate/Domain04.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain05](SixRowHeadCertificate/Domain05.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain06](SixRowHeadCertificate/Domain06.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01](SixRowHeadCertificate/Part01.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part10](SixRowHeadCertificate/Part10.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part11](SixRowHeadCertificate/Part11.md)
