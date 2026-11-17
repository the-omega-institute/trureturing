# Jacobi Sums under Finite-Field Norm Lift

## Abstract

Negative Jacobi sums lift through finite-field norm and trace pullback.

**Theorem 1.1 (Negative Jacobi norm lift).**

Lean statement: `D5/S3/CharacterSums/Fermat/JacobiNormLift.neg_jacobiSum_norm_lift`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/JacobiNormLift.neg_jacobiSum_norm_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite fields k and K with an algebra structure k → K, complex multiplicative characters chi and phi on k, and a complex additive character psi on k, assume psi is nontrivial and chi * phi is nontrivial. Writing N for the finite-field norm, Tr for the finite-field trace, and r = Module.finrank k K, the checked theorem states -J_K(chi ∘ N, phi ∘ N) = (-J_k(chi, phi))^r.

The proof combines the existing Langlands-normalized Hasse–Davenport lift with the Jacobi–Gauss quotient identity. Norm pullback preserves the product-character nontriviality hypothesis. The minus sign records the ordinary Jacobi-sum parity factor and gives a formula uniform in the extension degree.

This is the extension-compatibility interface for the existing single-field Fermat point-count development. The extension-field point-count family and its zeta factorization remain subsequent targets.

## References

- Truth anchor: `D5/S3/CharacterSums/Fermat/JacobiNormLift.neg_jacobiSum_norm_lift`
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift](../../Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.md)
