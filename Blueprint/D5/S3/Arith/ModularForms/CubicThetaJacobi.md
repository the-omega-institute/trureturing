# Actual finite Jacobi products and their Laurent columns

## Abstract

Actual finite Jacobi products and their Laurent columns

The existing InversionSeq207 Euler and Durfee triple-product proof supplies the algebraic coefficients. This module proves finite-product stabilization and justifies the special evaluations coefficientwise; it assumes no cubic theta identity.

**Definition 1.1 (finiteEulerPolynomial).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerPolynomial`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Actual finite Euler polynomial in a separate polynomial variable.

**Theorem 1.2 (euler_coefficient_finite).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.euler_coefficient_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobi.euler_coefficient_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Every coefficient of the supplied Euler construction agrees with every sufficiently long actual finite product.

**Definition 1.3 (finiteEulerEvaluation).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerEvaluation`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

A polynomial evaluation at a Laurent coefficient times a nonnegative power of X.

**Theorem 1.4 (finiteEulerEvaluation_eq_prod).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerEvaluation_eq_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerEvaluation_eq_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The finite polynomial evaluation is exactly its finite product of linear factors.

**Definition 1.5 (eulerEvaluation).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.eulerEvaluation`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaJacobi.eulerEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The coefficientwise stabilized Euler evaluation.

**Theorem 1.6 (tendsto_finiteEulerEvaluation).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.tendsto_finiteEulerEvaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobi.tendsto_finiteEulerEvaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The genuine finite products converge to the evaluation at every nonnegative shift.

**Theorem 1.7 (formalTheta_eq_eulerEvaluations).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.formalTheta_eq_eulerEvaluations`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobi.formalTheta_eq_eulerEvaluations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The supplied Laurent product is the product of the two separately justified evaluations.

**Definition 1.8 (jacobiSeries).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.jacobiSeries`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaJacobi.jacobiSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The supplied formalTheta normalized by the actual pentagonal Euler series.

**Theorem 1.9 (tendsto_finite_jacobi).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.tendsto_finite_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobi.tendsto_finite_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The actual three Jacobi product factors converge to jacobiSeries.

**Theorem 1.10 (jacobiSeries_column).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobi.jacobiSeries_column`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobi.jacobiSeries_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Every integer Laurent column is the exact signed triangular Jacobi monomial, by the repository supplier.

This is classical intermediate mathematics. The product-to-core lattice identity and the complete original k6 sign theorem are separate remaining obligations; no original-problem completion or novelty credit is asserted.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.eulerEvaluation`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.euler_coefficient_finite`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerEvaluation`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerEvaluation_eq_prod`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.finiteEulerPolynomial`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.formalTheta_eq_eulerEvaluations`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.jacobiSeries`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.jacobiSeries_column`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.tendsto_finiteEulerEvaluation`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobi.tendsto_finite_jacobi`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct](../../Combinatorics/InversionSeq/InversionSeq207TripleProduct.md)
