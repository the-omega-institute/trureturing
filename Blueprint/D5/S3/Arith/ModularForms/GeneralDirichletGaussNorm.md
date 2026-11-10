# GeneralDirichletGaussNorm

## Abstract

Finite Fourier inversion extends the primitive Dirichlet Gauss norm identity from prime moduli to every nonzero modulus.

**Theorem 1.1 (Primitive Gauss product by finite Fourier inversion).**

Lean statement: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_gauss_product_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_gauss_product_fourier` (`✓ std3`). ∎

**Theorem 1.2 (General primitive Dirichlet Gauss norm).**

Lean statement: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_dirichlet_gauss_normSq_general`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_dirichlet_gauss_normSq_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero modulus N and every primitive complex Dirichlet character χ modulo N, the standard Gauss sum has squared complex modulus N. The product identity is obtained from the discrete Fourier inversion formula on ZMod N, evaluated at −1, together with the primitive-character Fourier transform formula. This avoids the finite-field-only Gauss product theorem and supplies the finite normalization needed by general primitive twists.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_gauss_product_fourier`
- Truth anchor: `D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_dirichlet_gauss_normSq_general`
