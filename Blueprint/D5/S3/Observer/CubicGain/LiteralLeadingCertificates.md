# Four nonsingular integer matrices

## Abstract

Integer leading matrices of the original elimination determinants

topR1 and topR2 are thirty by thirty integer matrices. topA and topC are twenty-eight by twenty-eight integer matrices. Their entries are fixed exactly by the integer arrays in the Lean definitions. LiteralSylvesterBounds identifies them with the weighted leading matrices of the original fixed resultants and linear minors, with every row and column in the source order.

Each matrix M has an explicit integer matrix T and an upper triangular integer matrix U. The entire entrywise identity T M=U is checked over the integers, together with upper triangularity and all nonzero diagonal entries of U. Determinant multiplicativity implies det(M) is nonzero. This argument makes no pivot choice and assumes no division or nonzero intermediate pivot.

**Theorem 1.1 (The four integer determinants are nonzero).**

$$\operatorname{det}(topR_{1})\neq 0\land \operatorname{det}(topR_{2})\neq 0\land \operatorname{det}(topA)\neq 0\land \operatorname{det}(topC)\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralLeadingCertificates.leading_determinants_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinants of topR1, topR2, topA and topC are all nonzero integers. Their role is to establish exact polynomial degrees after the weighted leading-coefficient identities; they are not samples of an asserted resultant factorization.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/LiteralLeadingCertificates.leading_determinants_ne_zero`
