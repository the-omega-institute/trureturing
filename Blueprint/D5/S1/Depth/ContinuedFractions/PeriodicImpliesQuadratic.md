# Periodic Continued Fractions Are Quadratic

## Abstract

Eventually periodic continued fractions yield nondegenerate quadratic equations through integer Mobius transfers.

**Lemma 1.1 (Cross-multiplied transfers compose).**

$$\forall M, N \in \operatorname{MobiusInt}, x, y, z \in \mathbb{R},\ (\operatorname{Rel}\left(M, x, z\right) \land \operatorname{Rel}\left(N, z, y\right)) \Rightarrow \operatorname{Rel}\left(\operatorname{comp}\left(M, N\right), x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.rel_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If one integer linear-fractional transfer relates x to an intermediate value z and a second relates z to y, their matrix product relates x directly to y. The relation is cross-multiplied, so composition uses no division and assumes no denominator is nonzero.

**Lemma 1.2 (A segment relates its endpoint complete quotients).**

$$\forall x \in \mathbb{R}, h: \operatorname{EventuallyPeriodicCF}\left(x\right), first, length \in \mathbb{N},\ \operatorname{Rel}\left(\operatorname{segment}\left(\operatorname{coefficient}\left(h\right), first, length\right), \operatorname{completeQuotient}\left(h, first\right), \operatorname{completeQuotient}\left(h, first + length\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_rel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of any consecutive block of inverse continued-fraction steps relates the complete quotient at the start of the block to the complete quotient at its end. This packages repeated inverse-step recurrence into one integer transfer matrix.

**Lemma 1.3 (The transfer determinant is multiplicative).**

$$\forall M, N \in \operatorname{MobiusInt},\ \operatorname{det}\left(\operatorname{comp}\left(M, N\right)\right) = \operatorname{det}\left(M\right) \cdot \operatorname{det}\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.det_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the product transfer is the product of the two integer determinants. This is the usual two-by-two determinant identity written for the four-entry transfer representation.

**Lemma 1.4 (A segment has alternating determinant).**

$$\forall coefficient: \mathbb{N} \to \mathbb{Z}, first, length \in \mathbb{N},\ \operatorname{det}\left(\operatorname{segment}\left(coefficient, first, length\right)\right) = (-1)^{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each inverse continued-fraction step has determinant minus one. Therefore a segment of the given length has determinant minus one to that length, and in particular every segment transfer is nondegenerate.

**Lemma 1.5 (Nonnegative coefficients give nonnegative segment entries).**

$$\forall coefficient: \mathbb{N} \to \mathbb{Z}, first, length \in \mathbb{N},\ [\forall k \in \mathbb{N}, k < length \Rightarrow 0 \leq \operatorname{coefficient}\left(first + k\right)] \Rightarrow 0 \leq \operatorname{a}\left(\operatorname{segment}\left(coefficient, first, length\right)\right) \land 0 \leq \operatorname{b}\left(\operatorname{segment}\left(coefficient, first, length\right)\right) \land 0 \leq \operatorname{c}\left(\operatorname{segment}\left(coefficient, first, length\right)\right) \land 0 \leq \operatorname{d}\left(\operatorname{segment}\left(coefficient, first, length\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_entries_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every coefficient in a finite block is nonnegative, all four entries of its transfer matrix are nonnegative. The property is preserved as each inverse-step matrix is multiplied onto the remaining segment.

**Lemma 1.6 (Positive coefficients make the upper-right entry positive).**

$$\forall coefficient: \mathbb{N} \to \mathbb{Z}, first, length \in \mathbb{N},\ (0 < length \land [\forall k \in \mathbb{N}, k < length \Rightarrow 0 < \operatorname{coefficient}\left(first + k\right)]) \Rightarrow 0 < \operatorname{b}\left(\operatorname{segment}\left(coefficient, first, length\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_b_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonempty segment whose coefficients are all positive has a strictly positive upper-right matrix entry. Positivity propagates from the first step, while nonnegativity of the other tail entries prevents cancellation.

**Lemma 1.7 (A periodic block has positive upper-right entry).**

$$\forall x \in \mathbb{R}, h: \operatorname{EventuallyPeriodicCF}\left(x\right),\ 0 < \operatorname{b}\left(\operatorname{segment}\left(\operatorname{coefficient}\left(h\right), \operatorname{start}\left(h\right), \operatorname{period}\left(h\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.period_segment_b_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certified period has positive length, and every coefficient from the period start onward is positive. Applying the finite-segment positivity result makes the upper-right entry of the period transfer strictly positive.

**Lemma 1.8 (The computed infinite continued fraction is irrational).**

$$\forall x \in \mathbb{R}, h: \operatorname{EventuallyPeriodicCF}\left(x\right),\ \operatorname{Irrational}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.computed_cf_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certified coefficient is present at every position of the computed continued fraction. A rational real would instead have a terminating regular continued fraction, so the two properties are incompatible and the represented value must be irrational.

**Lemma 1.9 (Quadratic equations transfer across nondegenerate segments).**

$$\forall x, y \in \mathbb{R}, M \in \operatorname{MobiusInt}, u, v, w \in \mathbb{Z},\ (\operatorname{det}\left(M\right) \neq 0 \land \operatorname{Rel}\left(M, x, y\right) \land (u \neq 0 \lor v \neq 0 \lor w \neq 0) \land u \cdot y^{2} + v \cdot y + w = 0) \Rightarrow \exists a, b, c \in \mathbb{Z},\ (a \neq 0 \lor b \neq 0 \lor c \neq 0) \land a \cdot x^{2} + b \cdot x + c = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.quadratic_transfers_across_segment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a nondegenerate integer transfer relates x to y and y satisfies a nonzero integer quadratic equation. Clearing the linear-fractional relation produces an integer quadratic equation for x. The nonzero determinant ensures that its three transformed coefficients cannot all vanish.

**Theorem 1.10 (Eventual periodicity forces quadratic irrationality).**

$$\forall x \in \mathbb{R},\ \operatorname{EventuallyPeriodicCF}\left(x\right) \Rightarrow (\operatorname{Irrational}\left(x\right) \land \exists a, b, c \in \mathbb{Z},\ (a \neq 0 \lor b \neq 0 \lor c \neq 0) \land a \cdot x^{2} + b \cdot x + c = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.eventually_periodic_cf_implies_quadratic_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repeating the complete quotient makes the period transfer fix the periodic tail. Cross-multiplication gives that tail a nonzero integer quadratic equation, with nonvanishing certified by the positive upper-right entry.

The prefix transfer has determinant plus or minus one, so the quadratic equation pulls back from the periodic tail to the original value. The infinite computed coefficient stream separately proves irrationality, giving Lagrange direction A.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.computed_cf_irrational`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.det_comp`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.eventually_periodic_cf_implies_quadratic_irrational`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.period_segment_b_pos`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.quadratic_transfers_across_segment`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.rel_comp`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_b_pos`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_det`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_entries_nonneg`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic.segment_rel`
- Dependency: [D5/S1/Depth/GoldenContinuedFraction](../GoldenContinuedFraction.md)
