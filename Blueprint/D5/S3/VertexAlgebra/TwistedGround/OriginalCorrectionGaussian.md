# Actual neutral correction and native Gaussian coefficients

## Abstract

Exact finite Gaussian coefficients of the actual neutral lattice correction

Let D be lattice data of arbitrary finite rank, with its symmetric integral Gram matrix. Its oscillator index is Fin(D.rank) times the natural numbers. The shift parameter z is any complex number. Every source polynomial and every chosen complex linear form has finite support. Rank zero, degenerate Gram matrices, zero forms, dependent forms and an empty finite family are included.

**Definition 1.1 (Actual vacuum readout).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the original neutral Corr(D,0) to the source polynomial. Sum z^s times the oscillator constant coefficient of its shift-s component. This is a finite linear functional; it is not asserted to preserve products.

**Definition 1.2 (Evaluated pair covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.covariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.covariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For indices a and b, the covariance is pairScalar(a.2+1,b.2+1) times D.G(a.1,b.1) times z^((a.2+1)+(b.2+1)). It is complex bilinear, without conjugation.

**Definition 1.3 (Arbitrary finite linear form).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.linearForm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.linearForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finitely supported coefficient family c gives the actual oscillator polynomial sum_a c(a) X_a.

**Definition 1.4 (Covariance under finite linear substitution).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.covarianceMatrix`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.covarianceMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite family c_i, A_ij is the finite sum of c_i(a)c_j(b) times the evaluated pair covariance. The symmetry of pairScalar and the Gram matrix makes A symmetric. No positivity or nondegeneracy is required.

**Theorem 1.5 (Finite reconstruction of the actual Corr readout).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum_eq_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum_eq_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite shift sum equals evaluation of correctionLift(D,0,p), with its none variable assigned z and every some oscillator variable assigned zero. The proof passes through optionEquivLeft and reconstructs the finite polynomial from its coefficients.

**Theorem 1.6 (All occupations with their exact factorials).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum_linearForms`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum_linearForms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every occupation d on the finite family, sourceVacuum(product_i v_i^(d_i)) equals weight(d) times gaussianCoefficient(A,d). Here weight(d) is the product of the occupation factorials, and gaussianCoefficient is the coefficient of Q_A^(degree(d)/2)/(degree(d)/2)!, with Q_A one half of sum_ij A_ij X_i X_j. The Gaussian expression is the existing native polynomial coefficient, rather than a definition of the source functional.

Actual insertion and its source partial derivative identity yield the Stein recurrence. Finite derivation reconstruction and the substitution chain rule retain all repeated and mixed occurrences. The native recurrence follows from gaussianPiece_coefficient_step. Multiplying it by the factorial weight uses weight(r+e_i)=(r_i+1)weight(r) and weight(r)=r_j weight(r-e_j) when r_j is positive. Zero multiplicities contribute zero. Both sides are one at the empty occupation and vanish at odd total degree; strong induction compares predecessors of degree two less. Recurrence multiplicities belong to r after extracting the first occurrence.

This is a finite algebraic identity for arbitrary complex z. It assumes no Wick identity, summability, Hilbert norm bound, convergence radius, representer, independence or injectivity. It makes no assertion of a full vertex operator algebra, conformal field theory, an entire corrected field, string dynamics, AdS/CFT or a physical realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.covarianceMatrix`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.linearForm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum_eq_evaluation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.sourceVacuum_linearForms`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection](../LatticeHalfFockCurrentCorrection.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate](FactorialFockQuadraticEstimate.md)
