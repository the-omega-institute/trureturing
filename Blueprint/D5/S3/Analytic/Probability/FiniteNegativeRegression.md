# Negative association below rectangular size 81

## Abstract

Full negative regression implies negative association below rectangular size 81.

**Definition 1.1 (Full negative regression).**

Lean statement: `D5/S3/Analytic/Probability/FiniteNegativeRegression.FullNRD`

*Formalization.* `D5/S3/Analytic/Probability/FiniteNegativeRegression.FullNRD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

For disjoint response and conditioning blocks, the conditional mean of every increasing real response test decreases between coordinatewise comparable conditioning tuples of positive mass. The comparison includes pairs separated by zero-mass fibers.

**Definition 1.2 (Negative association).**

Lean statement: `D5/S3/Analytic/Probability/FiniteNegativeRegression.NA`

*Formalization.* `D5/S3/Analytic/Probability/FiniteNegativeRegression.NA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

The covariance of every pair of increasing real tests on disjoint blocks is nonpositive.

**Definition 1.3 (Actual marginal-support product).**

Lean statement: `D5/S3/Analytic/Probability/FiniteNegativeRegression.marginalProduct`

*Formalization.* `D5/S3/Analytic/Probability/FiniteNegativeRegression.marginalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

Take the product of the sizes of the supports of the one-coordinate marginal probability mass functions.

**Theorem 1.4 (Upper events suffice for full negative regression).**

$$\forall p, \operatorname{UpperNRD}(p) \Rightarrow \operatorname{FullNRD}(p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteNegativeRegression.fullNRD_of_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

UpperNRD restricts the response tests to upper-set indicators. Normalize each positive conditioning fiber and project its law onto the response block. Finite Strassen gives a coupling from the law at the larger conditioning tuple to the law at the smaller one, supported on ordered response pairs. An increasing test is ordered on each supported pair, and the coupling marginals give the two conditional means.

**Theorem 1.5 (The lower bound for arbitrary finite products).**

$$\forall p, \operatorname{FullNRD}(p) \land \operatorname{marginalProduct}(p) < 81 \Rightarrow \operatorname{NA}(p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteNegativeRegression.na_of_fullNRD_of_marginalProduct_lt_81` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

Restrict to the coordinate supports and omit singleton factors in each observed block. For disjoint blocks, the product of their sizes is below 81, so at least one has size at most eight. The nonconstant possibilities are a chain, a binary factor times a chain, and three binary factors. Conditional means under the actual marginal retain all subblock comparisons by the finite tower identity. The binary-by-chain proof compares the upper row tail and the corresponding marginal tail. The cube case uses the upper-event sign on the three-bit cube. Decomposing increasing real tests into upper-level indicators gives the covariance sign.

## References

- Truth anchor: `D5/S3/Analytic/Probability/FiniteNegativeRegression.FullNRD`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteNegativeRegression.NA`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteNegativeRegression.fullNRD_of_upper`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteNegativeRegression.marginalProduct`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteNegativeRegression.na_of_fullNRD_of_marginalProduct_lt_81`
- Dependency: [D5/S3/Analytic/Probability/FiniteOrderedStrassen](FiniteOrderedStrassen.md)
- Dependency: [D5/S3/Analytic/Probability/ThreeBitCubeConditionalMeans](ThreeBitCubeConditionalMeans.md)
