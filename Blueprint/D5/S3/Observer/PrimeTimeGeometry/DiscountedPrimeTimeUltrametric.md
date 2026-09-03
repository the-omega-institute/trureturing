# Discounted Prime-Time Ultrametric

## Abstract

The discounted finite-family prime-time distance obeys the strong triangle law.

**Definition 1.1 (Discounted prime-time distance).**

$$\forall x, y\in X,\\d_{J,gamma}^F(x, y) = \operatorname{sup}_{i\in J, n\in \mathbb{N}} \operatorname{w}\left(i\right) gamma^n \operatorname{discreteOutputDistance}\left(\operatorname{q}\left(i, \operatorname{iterate}\left(F, n, x\right)\right), \operatorname{q}\left(i, \operatorname{iterate}\left(F, n, y\right)\right)\right).$$

*Formalization.* `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discountedPrimeTimeDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite observer budget J, take the real supremum over each selected index i and each nonnegative time n. The summand is the coordinate weight times gamma to the nth power times the zero-or-one discrepancy between the two readouts after n updates.

Source-boundary open: the source does not define a real supremum for the empty coordinate family J = emptyset. The Lean iSup expression has a totalized empty-budget behavior supplied by its ambient order structure; that behavior is formalization-specific, not a source convention, and remains open pending an authoritative source clause.

**Theorem 1.2 (Prime-time prediction distance obeys the strong triangle inequality).**

$$\forall I \in \operatorname{Type}, X \in \operatorname{Type}, O \in I \to \operatorname{Type}, J \in \operatorname{Finset}\left(I\right), w \in I \to \mathbb{R}, q \in \forall i: I, X \to \operatorname{O}\left(i\right), F \in X \to X, gamma \in \mathbb{R},\; {\forall i: I, 0 < \operatorname{w}\left(i\right)} \Rightarrow\\gamma\in (0, 1] \Rightarrow\\\forall x, y, z\in X,\\d_{J,gamma}^F(x, z) \leq \max(d_{J,gamma}^F(x, y), d_{J,gamma}^F(y, z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discounted_prime_time_distance_strong_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source standing carrier clause requires strictly positive weight on every coordinate i in I, while gamma belongs to (0,1]. Both are section-level clauses of the source volume, cited here so the claim can be checked against the source rather than taken on this document's word. Source line 2016, immediately before Definition 33.1, specifies a positive weight w_i for every coordinate; the section 33 heading, standing before both Definition 33.1 and Theorem 33.1, sets 0 < gamma <= 1; and source line 2083 restates both together as the hypothesis that all weights are positive and gamma > 0. The source states these in LaTeX; they are transcribed to plain text here because Scribe text runs carry no raw LaTeX delimiters, and the verbatim quotations are kept in the Lean docstring instead. They are therefore not premises introduced here; the atom for Theorem 33.1 is a slice that does not carry them. The proof only invokes that positivity on the selected finite budget J, but the public theorem preserves the source's global premise.

The source is silent on the empty-budget supremum (J = emptyset), so that case is an open source boundary rather than an added premise or an assigned source value.

The finite budget, the bounded discount powers, and the zero-or-one coordinate discrepancy bound every supremum by the sum of the selected weights. The existing weighted joint strong triangle theorem supplies the pointwise law, and ciSup_sup_eq moves the maximum through the prime-time supremum.

## References

- Truth anchor: `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discountedPrimeTimeDistance`
- Truth anchor: `D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.discounted_prime_time_distance_strong_triangle`
- Dependency: [D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric](../MetricGeometryLaws/WeightedJointUltrapseudometric.md)
