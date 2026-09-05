# Finite Prony Shifted Hankel Transport

## Abstract

Every shifted finite Prony Hankel section uses one fixed Vandermonde observation map while elapsed time acts on diagonal modal weights.

**Theorem 1.1 (Every shifted Prony Hankel section has a Vandermonde factorization).**

$$H_{s}(c) = \operatorname{V}(x)\cdot\operatorname{D}(w_{s})\cdot\operatorname{V}(x)^{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport.finite_prony_shifted_hankel_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite exponential moment sequence, the Hankel section beginning at any observation-time shift factors through the same rectangular Vandermonde matrix on both sides.

The shift appears only in the diagonal entries m_j q_j^shift. This extends the source's unshifted factorization (1295.6) to a complete finite family of shifted Hankel sections.

The statement is exact and finite-dimensional. It supplies no noisy singular-value bound or infinite-delay convergence theorem.

**Theorem 1.2 (One time step multiplies each hidden modal weight by its node).**

$$H_{s+1}(c) = \operatorname{V}(x)\cdot\operatorname{D}(w_{s}\cdot x)\cdot\operatorname{V}(x)^{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport.finite_prony_shifted_hankel_succ_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Advancing the Hankel origin by one sample retains the observation map and multiplies the hidden weight of mode j by q_j.

This is the exact diagonal transport interface used by matrix-pencil identification and finite Koopman spectral models. Eigenvalue recovery requires additional invertibility and separation results.

**Theorem 1.3 (Modal observation-time shifts compose multiplicatively).**

$$w_{a+b}(j) = w_{a}(j)\cdot x_{j}^{b}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport.finite_prony_shifted_weights_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding two observation-time shifts multiplies the current hidden modal weight by the corresponding power of its transport node. The identity isolates the semigroup law on each finite spectral fiber.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport.finite_prony_shifted_hankel_factorization`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport.finite_prony_shifted_hankel_succ_transport`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport.finite_prony_shifted_weights_add`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](FinitePronyHankelReconstruction.md)
