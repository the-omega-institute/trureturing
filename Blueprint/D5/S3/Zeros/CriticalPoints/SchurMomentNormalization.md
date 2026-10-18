# Spectral moment normalization and transfer

## Abstract

Normalization of nonzero spectral data and exact transfer between Schur diagonals and reciprocal critical points.

**Theorem 1.1 (Positive normalized spectral weights).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.normalized_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.normalized_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite family of nonzero complex mu_k and p>0, there exist N>0, positive rho_k and unit phases v_k with mu_k=v_k N rho_k, sum_k rho_k^p=1, N^p=sum_k norm(mu_k)^p, and sum_k conj(v_k) rho_k^(p−1) mu_k=N. Thus the same normalized data serve both the left boundary and interpolation center.

**Theorem 1.2 (The diagonal moment in a unitary Schur basis).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.schur_roots_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.schur_roots_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Q is unitary and Q* A Q is upper triangular, the sum of norm-to-p over every characteristic root of A, counted with multiplicity, equals the sum of norm-to-p over the diagonal entries of Q* A Q. The identity holds for every real p.

**Theorem 1.3 (The reciprocal critical-point moment).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.reciprocal_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.reciprocal_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite family of nonzero complex z_j and every real p, the sum of norm(w)^(−p) over the derivative roots of the reused polynomial P is exactly the p-th norm moment of the characteristic roots of D(I+J), where D has diagonal entries 1/z_j. This directly reuses the multiplicity-preserving reciprocal-root identity.

**Theorem 1.4 (The characteristic polynomial of the Hermitian sandwich).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.A_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.A_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>0 and arbitrary complex diagonal b, define A=H(n,1/2) diag(b) H(n,1/2). Its characteristic polynomial equals that of diag(b)(I+J). If all b_j are nonzero, A is invertible; consequently every diagonal entry in a unitary upper-triangular Schur form is nonzero.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.A_charpoly`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.normalized_weights`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.reciprocal_moment`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.schur_roots_moment`
- Dependency: [D5/S3/Zeros/CriticalPoints/RankOneComplexPowers](RankOneComplexPowers.md)
