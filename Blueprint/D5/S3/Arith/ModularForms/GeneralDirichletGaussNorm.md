# General primitive Dirichlet Gauss norm

## Abstract

Finite Fourier inversion extends the primitive Dirichlet Gauss norm identity from prime moduli to every nonzero modulus.

**Theorem 1.1 (Primitive Gauss product by finite Fourier inversion).**

Lean statement: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_gauss_product_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_gauss_product_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a primitive complex Dirichlet character modulo any nonzero modulus, the product of its standard Gauss sum with the opposite-character, inverse-additive-character Gauss sum equals the modulus. The proof uses the discrete Fourier inversion identity on ZMod N at the negative unit and the primitive-character Fourier transform law.

**Theorem 1.2 (General primitive Dirichlet Gauss norm).**

Lean statement: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_dirichlet_gauss_normSq_general`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_dirichlet_gauss_normSq_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the complex conjugate form of the product identity gives squared complex modulus exactly equal to N. This covers composite moduli and provides the normalization input for general primitive twists.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_dirichlet_gauss_normSq_general`
- Truth anchor: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_gauss_product_fourier`
