# Sextic Gauss Sum Norm

## Abstract

Primitive order-six Gauss sums have the finite-field norm required for normalized phase questions.

For a finite field F, an order-six multiplicative character chi, and a primitive complex additive character psi, the squared complex modulus of the Gauss sum is the cardinality of F. Consequently the square divided by that cardinality lies on the unit circle. These are pointwise algebraic constraints; the family-level equidistribution conjecture remains open.

**Theorem 1.1 (Finite-field norm of a sextic Gauss sum).**

Lean statement: `D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_normSq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof combines Mathlib's primitive Gauss product with conjugation of both characters, then identifies the resulting complex product with Complex.normSq.

**Theorem 1.2 (Normalized square lies on the unit circle).**

Lean statement: `D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_square_div_card_normSq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_square_div_card_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise norm identity is transported through Complex.normSq of a square and a quotient, producing the exact unit-circle constraint used by later phase-moment and Weyl-criterion work.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_normSq`
- Truth anchor: `D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_square_div_card_normSq`
