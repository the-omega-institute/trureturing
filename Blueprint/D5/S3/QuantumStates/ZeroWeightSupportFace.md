# Zero-Weight Support Face

## Abstract

Zero projection weight confines a positive matrix to the complementary support.

**Theorem 1.1 (Zero projection weight exposes a support face).**

$$\operatorname{PosSemidef}(\rho) \land P^{*} = P \land P^{2} = P \land \operatorname{Tr}(\rho\,P) = 0 \Rightarrow (P\,\rho = 0 \land \rho\,P = 0) \land \rho = (I - P)\,\rho\,(I - P).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/ZeroWeightSupportFace.zero_weight_support_face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a positive semidefinite complex matrix and P a self-adjoint idempotent matrix. If the trace weight Tr(rho P) vanishes, then both one-sided products P rho and rho P vanish.

The proof first compresses rho by P. The compression is positive semidefinite and has zero trace, so Mathlib's trace-zero theorem makes it zero. A positive factorization of rho then turns this into the two one-sided annihilations.

Expanding the complementary compression and using those annihilations gives rho = (I-P) rho (I-P). No trace-one normalization or finite-rank restriction on the projection is required.

## References

- Truth anchor: `D5/S3/QuantumStates/ZeroWeightSupportFace.zero_weight_support_face`
