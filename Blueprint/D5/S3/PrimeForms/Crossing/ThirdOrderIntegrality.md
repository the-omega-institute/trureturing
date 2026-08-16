# The Third-Order Integrality Criterion

## Abstract

The rational K-conjugate of an integer matrix is integral exactly on one mod-three class.

**Theorem 1.1 (K-conjugation is integral exactly on one congruence class).**

$$\forall \gamma \in M_2(\mathbb{Z}),\\(\forall i,j, 3 \mid (K\gamma\operatorname{adj} K)_{ij}) \iff 3 \mid (\gamma_{00}+2\gamma_{01}+\gamma_{10}+2\gamma_{11})$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/ThirdOrderIntegrality.k_conjugate_integral_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K = [[1,-2],[2,-1]], whose determinant is 3. For an integer 2x2 matrix gamma, the adjugate formula writes the rational inverse of K as one third of adj(K). Thus K*gamma*adj(K) is the numerator of the rational conjugate K*gamma*K^{-1}, and that conjugate has integer entries exactly when all four numerator entries are divisible by 3.

Expanding those four entries modulo 3 gives respectively the negative or positive of the single linear form g00 + 2*g01 + g10 + 2*g11. Hence all four divisibility conditions are equivalent to one congruence. The Lean proof reads the forward implication from entry (0,0), constructs a quotient for each entry in the reverse implication, and reuses the preceding module's K.

Repository search found no equivalent D5 declaration. Pinned-mathlib and Loogle searches found Matrix.adjugate_fin_two and Matrix.inv_def as the exact library support, but no theorem for this specific K-congruence. This closes only clause (i), the K-integrality characterization, of residual E.73. It does not claim K-normalization, conjugacy with Gamma_0(3), the (2,6,infinity) group identification, or the later crossing-class corollary.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/ThirdOrderIntegrality.k_conjugate_integral_iff`
- Dependency: [D5/S3/PrimeForms/Crossing/ThirdOrderReciprocity](ThirdOrderReciprocity.md)
