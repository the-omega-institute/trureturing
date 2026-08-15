# Finite Product Set Capture Law

## Abstract

Every prescribed finite set of captured addresses has an exact all-orders weighted intersection mass.

**Theorem 1.1 (Exact prescribed-set capture probability).**

$$\operatorname{setCaptureProbability}\left(q, f, T\right) = \prod_{b\in T} \operatorname{fixedPowerMass}\left(q, f, b, \lvert T \rvert\right) \prod_{b\in {A\setminus T}} \operatorname{collisionPowerMass}\left(q, f, b, \lvert T \rvert\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture.set_capture_probability_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditioning on the listing diagonal lets constrainedRows_weight_sum integrate out every free row and retain precisely the rows indexed by T.

Finite sum-product factorization then separates columns: selected columns contribute fixedPowerMass and unselected columns contribute collisionPowerMass, both at exponent |T|.

**Theorem 1.2 (Singleton consistency).**

$$\operatorname{setFormula}\left(q, f, \{, a, \}\right) = \operatorname{oneRowFormula}\left(q, f, a\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture.singleton_set_formula_eq_capture_probability_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof applies the all-orders theorem and the frozen capture_probability_exact theorem to the same singleton event.

**Theorem 1.3 (Distinct-pair consistency).**

$$a\neq a' \Rightarrow \operatorname{setFormula}\left(q, f, \{, a, ,,  , a', \}\right) = \operatorname{pairFormula}\left(q, f, a, a'\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture.pair_set_formula_eq_pair_capture_probability_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct addresses, the proof applies the all-orders theorem and the frozen pair_capture_probability_exact theorem to the same two-address event.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture.pair_set_formula_eq_pair_capture_probability_exact`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture.set_capture_probability_exact`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture.singleton_set_formula_eq_capture_probability_exact`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture](FiniteProductPairCapture.md)
