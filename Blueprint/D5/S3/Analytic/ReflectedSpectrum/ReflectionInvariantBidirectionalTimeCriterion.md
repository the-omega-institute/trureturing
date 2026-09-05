# Reflection-Invariant Bidirectional Time Criterion

## Abstract

A reflected two-branch Gramian is finite at every proper discount exactly at zero transverse displacement.

**Definition 1.1 (The complete future-past Gramian term).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectionalGramianTerm`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectionalGramianTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The term is the sum of the two geometric powers obtained from both coordinates of the frozen reflected pair after a doubled observation period. It carries the future and past branches without selecting an orientation.

**Definition 1.2 (The first bidirectional singular radius).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectionalConvergenceRadius`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectionalConvergenceRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius is exp(-2 P |delta|), the smaller of the reciprocal branch radii. It is invariant under changing the sign of delta.

**Theorem 1.3 (Both geometric ratios control bidirectional summability).**

$$\forall delta \in \mathbb{R}, P \in \mathbb{R}, beta \in \mathbb{R},\; 0 \le \mathit{beta} \Rightarrow \left(\operatorname{Summable}\left((n \mapsto \operatorname{bidirectionalGramianTerm}\left(delta, P, \mathit{beta}, n\right))\right) \Leftrightarrow \left(\left\lVert \mathit{beta} \cdot \operatorname{fst}\left(\operatorname{reflectedGrowthPair}\left(delta, 2 \cdot P\right)\right) \right\rVert < 1 \land \left\lVert \mathit{beta} \cdot \operatorname{snd}\left(\operatorname{reflectedGrowthPair}\left(delta, 2 \cdot P\right)\right) \right\rVert < 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectional_gramian_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative discount, comparison with the nonnegative combined series recovers summability of each branch. The pinned geometric-series criterion then identifies the two strict ratio bounds, and their sum proves the converse.

**Theorem 1.4 (Zero displacement is exactly complete discounted finiteness).**

$$\forall delta \in \mathbb{R}, P \in \mathbb{R},\; 0 < P \Rightarrow \left(\left(delta = 0 \Leftrightarrow \left(\forall beta \in \mathbb{R},\; \left(0 \le \mathit{beta} \land \mathit{beta} < 1\right) \Rightarrow \operatorname{Summable}\left((n \mapsto \operatorname{bidirectionalGramianTerm}\left(delta, P, \mathit{beta}, n\right))\right)\right)\right) \land \left(\left(\forall beta \in \mathbb{R}, n \in \mathbb{N},\; \operatorname{bidirectionalGramianTerm}\left(-delta, P, \mathit{beta}, n\right) = \operatorname{bidirectionalGramianTerm}\left(delta, P, \mathit{beta}, n\right)\right) \land \left(\left|delta\right| = -\frac{1}{2 \cdot P} \cdot \operatorname{log}\left(\operatorname{bidirectionalConvergenceRadius}\left(delta, P\right)\right) \land \left(\left(\neg delta = 0\right) \Leftrightarrow \operatorname{bidirectionalConvergenceRadius}\left(delta, P\right) < 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.reflection_invariant_bidirectional_time_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a positive observation period, zero displacement is equivalent to summability of the complete future-past series for every discount between zero and one.

Changing the sign of delta exchanges the two summands and leaves their sum fixed. The common first radius still recovers |delta| exactly; a nonzero displacement is equivalent to that radius being below one.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectionalConvergenceRadius`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectionalGramianTerm`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.bidirectional_gramian_summable_iff`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion.reflection_invariant_bidirectional_time_criterion`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare](../Adelic/ReflectedGrowthPairNegativeSquare.md)
