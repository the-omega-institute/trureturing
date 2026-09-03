# Discounted Prime-Time Ultrametric

## Abstract

The discounted finite-family prime-time distance obeys the strong triangle law.

**Definition 1.1 (Discounted prime-time distance).**

$$\forall x, y\in X,\\d_{J,gamma}^F(x, y) = \operatorname{sup}_{i\in J, n\in \mathbb{N}} \operatorname{w}\left(i\right) gamma^n \operatorname{discreteOutputDistance}\left(\operatorname{q}\left(i, \operatorname{iterate}\left(F, n, x\right)\right), \operatorname{q}\left(i, \operatorname{iterate}\left(F, n, y\right)\right)\right).$$

*Formalization.* `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discountedPrimeTimeDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite observer budget J, take the real supremum over each selected index i and each nonnegative time n. The summand is the coordinate weight times gamma to the nth power times the zero-or-one discrepancy between the two readouts after n updates.

**Theorem 1.2 (Prime-time prediction distance obeys the strong triangle inequality).**

$$\forall I \in \operatorname{Type}, X \in \operatorname{Type}, O \in I \to \operatorname{Type}, J \in \operatorname{Finset}\left(I\right), w \in I \to \mathbb{R}, q \in \forall i: I, X \to \operatorname{O}\left(i\right), F \in X \to X, gamma \in \mathbb{R},\; {\forall i\in J, 0 < \operatorname{w}\left(i\right)} \Rightarrow\\gamma\in (0, 1] \Rightarrow\\\forall x, y, z\in X,\\d_{J,gamma}^F(x, z) \leq \max(d_{J,gamma}^F(x, y), d_{J,gamma}^F(y, z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discounted_prime_time_distance_strong_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every selected weight is strictly positive and gamma belongs to (0,1]. These are exactly the standing hypotheses preceding Definition 33.1 in the source.

The finite budget, the bounded discount powers, and the zero-or-one coordinate discrepancy bound every supremum by the sum of the selected weights. The existing weighted joint strong triangle theorem supplies the pointwise law, and ciSup_sup_eq moves the maximum through the prime-time supremum.

## References

- Truth anchor: `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discountedPrimeTimeDistance`
- Truth anchor: `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discounted_prime_time_distance_strong_triangle`
- Dependency: [D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric](../MetricGeometryLaws/WeightedJointUltrapseudometric.md)
