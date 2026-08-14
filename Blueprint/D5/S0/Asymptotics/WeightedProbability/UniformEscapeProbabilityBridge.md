# Uniform Escape Probability Bridge

## Abstract

Uniform cell weights identify weighted escape probability with the frozen counting probability.

**Theorem 1.1 (Uniform weighted escape is counting escape).**

$$\forall f: Y \to Y,\ \operatorname{escapeProbability}_{weighted}(((b, y) \mapsto \frac{1}{\lvert Y\rvert}), f) = \operatorname{escapeProbability}_{counting}(f).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/UniformEscapeProbabilityBridge.uniform_escapeProbability_eq_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and Y be finite types, let A have decidable equality, and let f map Y to Y. The weighted escape probability uses the constant marginal 1/card(Y) in every cell. The counting escape probability is the frozen ratio of escaped matrices to all matrices.

The public listingEquiv reassembles a diagonal and all off-row coordinates into a matrix. Restricting that equivalence with no_capture_iff_isEscaped identifies the two event subtypes. The uniform sample weight is independently proved to be the reciprocal of the matrix-space cardinality.

No Nonempty instance for A or Y, no DecidableEq instance for Y, and no LinearOrder instance for A is required. The exponent calculation also covers empty types, so the theorem states the exact finite hypotheses used by the two definitions.

Repository search found the coordinate equivalence only in two private frozen declarations and found no probability bridge. Pinned Mathlib supplies subtype-equivalence, cardinal-congruence, function-cardinality, and finite sum/product lemmas, which are reused here.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/UniformEscapeProbabilityBridge.uniform_escapeProbability_eq_counting`
- Dependency: [D5/S0/Asymptotics/FixedPointFreeEscapeProbability](../FixedPointFreeEscapeProbability.md)
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni](FiniteBonferroni.md)
