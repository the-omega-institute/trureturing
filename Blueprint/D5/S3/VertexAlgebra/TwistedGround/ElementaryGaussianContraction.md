# Elementary factorial Gaussian contraction

## Abstract

Finite native Gaussian contraction with zero shared diagonal

Let I, J and E be arbitrary finite mode types, including empty types. The external occupations d and e and shared occupation n are finitely supported natural families. P on I and Q on E are arbitrary complex symmetric matrices. R from I to J and S from J to E are arbitrary complex matrices. All products are bilinear; transpose has no complex conjugation.

The factorial normalization is classical symmetric/Bargmann Fock normalization, and the Gaussian pairing is classical Wick calculus. No literature novelty or exact external theorem attribution is claimed. AssessedProvenance.FromRepo records reuse of FactorialFockMetric and FactorialFockQuadraticEstimate, together with the unchanged nativeMoment and nativeMoment_step suppliers in NativeGaussianMoment. The retained inference is the native finite contraction, with a proved support bound and exact factorial reindexing.

**Definition 1.1 (First block kernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.leftKernel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.leftKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The blocks are P, R, transpose(R), and zero on J. Its shared diagonal vanishes.

**Definition 1.2 (Second block kernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.rightKernel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.rightKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The blocks are zero on J, S, transpose(S), and Q. Its shared diagonal vanishes.

**Definition 1.3 (Bilinear effective kernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.effectiveKernel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.effectiveKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The blocks are P, R S, transpose(R S), and Q. Matrix multiplication sums exactly over the finite shared mode type.

**Theorem 1.4 (Native finite coefficient identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.coefficient_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.coefficient_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum weight(n) times gaussianCoefficient(leftKernel, d.sumElim(n)) times gaussianCoefficient(rightKernel, n.sumElim(e)) over all n of degree at most min(degree(d),degree(e)). The sum is exactly gaussianCoefficient(effectiveKernel,d.sumElim(e)). The weight is the existing FactorialFockMetric.weight, the product of occupation factorials.

The proof directly reuses NativeGaussianMoment.nativeMoment and nativeMoment_step. Shared insertion has no shared/shared contribution, so each shared occurrence consumes an external occurrence. Induction proves vanishing when shared degree exceeds external degree on either side. Bounded-degree occupations form a finite set. In the contraction recurrence, n_a/weight(n) is reindexed by n=m+e_a and becomes 1/weight(m), using weight(m+e_a)=(m_a+1)weight(m). The second shared insertion supplies the cross block R S. A boundary comparison and induction on the first external degree identify the contracted moments with the effective native moment. External factorials cancel, leaving the ordinary coefficient identity.

There is no convergence or positivity hypothesis. The vacuum scalar is one. This proves no nontrivial determinant sewing invariant. Nonzero shared squeezing, countable limits, full corrected-field coefficients, Gram transformation, physical unitarity, VOA/CFT axioms, fusion, anomalies, string dynamics and AdS/CFT remain outside the result.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.coefficient_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.effectiveKernel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.leftKernel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.rightKernel`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment](NativeGaussianMoment.md)
