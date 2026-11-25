# Positive reference replacement

## Abstract

The exact loss of replacing a scalar coordinate with its normalized positive reference.

**Theorem 1.1 (Exact loss and quadratic Klein remainder).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveReferenceReplacement.positive_reference_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PositiveReferenceReplacement.positive_reference_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The mathlib community (2026). *Schur complements of finite matrices*. URL: <https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean#L369-L373>.

*Commentary.*

Let C be positive definite on a nonempty finite coordinate space. Suppose λ, u and a are positive and F ≥ uC in Löwner order. Write b = Re Tr C, c = b + λ, τ = C/b, F′ = F + aτ, C′ = cτ and t = Re Tr F + a. Here D(X∥Y) is the actual trace-log pairing Re Tr X(log X − log Y).

The loss D(F∥C) + a log(a/λ) − D(F′∥C′) equals a[log(a/(λu)) − 1] + t log(c/b) − K − aE, where K = D(F′∥F) − a and E = Re Tr τ[log F − log(uC)]. The theorem proves E ≥ 0 and K ≥ Re Tr[(aτ)* (aτ)]/(2t), where * denotes the adjoint. The resulting bound subtracts this quadratic term from the manuscript bound.

Positive scaling gives log C′ = log C + log(c/b)I and log(uC) = log C + log(u)I. The trace-one identity for τ then gives the exact formula. Operator monotonicity and the positive trace pairing give E ≥ 0. Both F and F′ are bounded by tI, so the spectral-ceiling strong Klein inequality gives the quadratic remainder.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/PositiveReferenceReplacement.positive_reference_replacement`
- Dependency: [D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy](SpectralCeilingRelativeEntropy.md)
