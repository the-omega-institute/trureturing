# MUB Completion Gluing

## Abstract

One relative Gram matrix determines fixed-edge double completions.

**Theorem 1.1 (Nonzero norm determines the partner).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.partner_eq_star_of_normSq_and_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.partner_eq_star_of_normSq_and_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex z and w and a nonzero real r, if the squared norm of z is r and z times w is r, then w is the complex conjugate of z.

**Theorem 1.2 (Conjugate relative Gram partner).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.relativeGram_partner_eq_entrywiseConj`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.relativeGram_partner_eq_entrywiseConj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite coordinate type, suppose X and X-prime are Hadamard unbiased and the entrywise product of their relative Gram with that of Y and Y-prime is the dimension constant. Then the latter relative Gram is the entrywise conjugate of the former.

**Theorem 1.3 (Scaled recovery from a relative Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.left_mul_relativeGram_eq_card_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.left_mul_relativeGram_eq_card_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If X times its adjoint is the dimension times the identity, multiplying the relative Gram X-adjoint times X-prime on the left by X gives the dimension times X-prime.

**Theorem 1.4 (Recovery by inverse dimension).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.invCard_smul_left_mul_relativeGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.invCard_smul_left_mul_relativeGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite coordinate type, the row Gram law for X makes inverse-dimension scaling of X times its relative Gram with X-prime equal to X-prime.

**Theorem 1.5 (Fixed-edge double completion).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.second_completion_determined_by_one_relativeGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.second_completion_determined_by_one_relativeGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be entrywise unit and X and Y be complex Hadamards on a nonempty finite coordinate type. Suppose X and X-prime are Hadamard unbiased and the two factorized cube completions have constant cross-Gram equal to the dimension. The relative Gram of Y and Y-prime is then the entrywise conjugate of that of X and X-prime. Multiplication by X or Y and inverse-dimension scaling recover X-prime and Y-prime from those two relative Grams.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.invCard_smul_left_mul_relativeGram`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.left_mul_relativeGram_eq_card_smul`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.partner_eq_star_of_normSq_and_product`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.relativeGram_partner_eq_entrywiseConj`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing.second_completion_determined_by_one_relativeGram`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility](MUBCubeCompatibility.md)
