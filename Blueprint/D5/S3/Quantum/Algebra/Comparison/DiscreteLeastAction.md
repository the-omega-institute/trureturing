# Discrete least action on a finite simplex

## Abstract

The least cosine action for nonnegative steps of fixed total at most pi.

**Theorem 1.1 (Equal angles minimize the action).**

$$\forall \iota : Type, [Fintype \iota] \forall t \in \iota \to \mathbb{R},\; \forall \theta : \mathbb{R}, \left(\left(\forall i \in \iota,\; 0 \le \operatorname{t}\left(i\right)\right) \land \left(\sum_{i \in \iota} \operatorname{t}\left(i\right) = \theta \land \theta \le \pi\right)\right) \Rightarrow \left(\left|\iota\right| \cdot (1 - \operatorname{cos}(\frac{\theta}{\left|\iota\right|})) \le \sum_{i \in \iota} (1 - \operatorname{cos}(\operatorname{t}\left(i\right))) \land \left(\sum_{i \in \iota} (1 - \operatorname{cos}(\operatorname{t}\left(i\right))) = \left|\iota\right| \cdot (1 - \operatorname{cos}(\frac{\theta}{\left|\iota\right|})) \Leftrightarrow \left(\left(\forall i \in \iota,\; \operatorname{t}\left(i\right) = \frac{\theta}{\left|\iota\right|}\right) \lor \left(\left|\iota\right| = 2 \land \theta = \pi\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/DiscreteLeastAction.sum_one_sub_cos_least_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The manuscript Ternions and minimal arcs states the strict total-angle case as F5 for a positive number of steps. The action adds one minus the cosine of each step. On an empty family the total is zero and Lean's real quotient by zero is zero. The cardinality factor vanishes, both actions are zero, and the equality condition is vacuous.

Cosine is strictly concave between zero and pi over two, where finite Jensen's inequality gives the bound and its equality condition. A single step already equals the total. If a larger family has a step above pi over two, averaging it with any other step preserves the total and brings all steps into that interval. The cosine sum cannot decrease under this averaging, and it increases strictly if the two steps differ and their sum is less than pi. Equality for a pair containing a large step therefore requires that the pair already sum to pi. Jensen equality would then force every remaining step to be pi over two, so the pair must exhaust the index type. At total pi the two cosines cancel for every split.

For two unequal, nonnegative steps whose total is just above pi, the cosine of their mean is negative. The two-angle cosine formula then gives a smaller action than that of the equal split. Allowing negative steps also invalidates the bound. With steps zero and minus twice pi, the action is zero and the uniform action is four. The sum premise ties the proposed total to the actual steps. With a single zero step but prescribed total pi over two, the proposed lower bound would be one while the action is zero. These examples follow from the two-angle formula and direct substitution and were checked by hand.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/DiscreteLeastAction.sum_one_sub_cos_least_action`
