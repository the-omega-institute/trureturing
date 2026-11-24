# Su and Hu Table 4.1

## Abstract

Exact negative dependence calculations for the Su and Hu four-coordinate law.

**Definition 1.1 (The published probability law).**

Lean statement: `D5/S3/Analytic/Probability/SuHuTable41.tablePMF`

*Formalization.* `D5/S3/Analytic/Probability/SuHuTable41.tablePMF` (`✓ std3`).

*Citation.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

Both pairs of ternary coordinates use lexicographic order. The displayed integer weights sum to 99,999, and each weight is divided by that total.

**Theorem 1.2 (Exact positive covariance).**

$$(\forall x, \operatorname{tablePMF}\left(x\right) > 0) \land \exists I, J, f, g, \operatorname{Disjoint}\left(I, J\right) \land \operatorname{Monotone}\left(f\right) \land \operatorname{Monotone}\left(g\right) \land \operatorname{cov}\left(tablePMF, f \circ \operatorname{project}\left(I\right), g \circ \operatorname{project}\left(J\right)\right) = \frac{1141067}{9999800001} > 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SuHuTable41.table_positive_covariance` (`✓ std3`). ∎

*Citation.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

Every table entry has positive mass. The two increasing tests indicate that both coordinates in the corresponding pair are at least one. Each event has weight 39,649, and their intersection has weight 15,732. Their covariance is 1,141,067 divided by 9,999,800,001.

**Theorem 1.3 (Attainment at 81).**

$$(\forall x, \operatorname{tablePMF}\left(x\right) > 0) \land \operatorname{marginalProduct}\left(tablePMF\right) = 81 \land \operatorname{FullNRD}\left(tablePMF\right) \land \neg\operatorname{NA}\left(tablePMF\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SuHuTable41.table_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuting Su and Taizhong Hu (2026). *Full negative regression dependence: counterexamples for tail dependence and negative association*. URL: <https://arxiv.org/abs/2609.23313v1>.

*Commentary.*

For each conditioning block, enumerate comparable tuples and upper sets on the complementary block. Each upper set on a disjoint response block pulls back to one of these upper sets. Compare integer fiber weights by cross multiplication and lift the upper-event inequalities to increasing real tests. Strict positivity gives four marginal supports of size three. The exact positive covariance violates negative association.

## References

- Truth anchor: `D5/S3/Analytic/Probability/SuHuTable41.tablePMF`
- Truth anchor: `D5/S3/Analytic/Probability/SuHuTable41.table_attainment`
- Truth anchor: `D5/S3/Analytic/Probability/SuHuTable41.table_positive_covariance`
- Dependency: [D5/S3/Analytic/Probability/FiniteNegativeRegression](FiniteNegativeRegression.md)
