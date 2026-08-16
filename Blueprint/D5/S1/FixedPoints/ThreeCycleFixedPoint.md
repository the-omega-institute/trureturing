# A Fixed Point Forced by Three-Cycle Counting

## Abstract

An order-three permutation on a finite set of size one modulo three has a fixed point.

**Theorem 1.1 (Three-cycle cardinality forces a fixed point).**

$$\forall X, sigma,\ sigma^{3}=id \land \operatorname{card}(X) \bmod 3=1 \Rightarrow \exists x\in X,\ sigma(x)=x.$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/ThreeCycleFixedPoint.three_cycle_action_has_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let sigma be a permutation of a finite set X. If sigma cubed is the identity, every nontrivial orbit has three elements. Consequently, card(X) congruent to one modulo three forces a singleton orbit and therefore a fixed point.

The Lean proof specializes the pinned Mathlib theorem Equiv.Perm.exists_fixed_point_of_prime at the prime three. The only local step converts card(X) modulo three equal to one into the theorem's nondivisibility hypothesis.

This closes only the fixed-point consequence in the P3 clause of source remark 27.583. It does not assert the constant-law identities, the P1 or P2 predictions, the numerical search outcome, or the engineering postmortem elsewhere in the atom.

## References

- Truth anchor: `D5/S1/FixedPoints/ThreeCycleFixedPoint.three_cycle_action_has_fixed_point`
