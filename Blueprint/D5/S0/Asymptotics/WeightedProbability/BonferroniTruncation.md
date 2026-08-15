# Arbitrary-Order Bonferroni Truncation

## Abstract

Every finite Bonferroni truncation bounds weighted escape in the direction determined by its parity.

**Theorem 1.1 (Alternating truncations bracket escape).**

$$(\forall b, y,\ 0\leq q_{b}(y)) \Rightarrow (\operatorname{Even}\left(m\right) \Rightarrow \operatorname{escapeProbability}\left(q, f\right) \leq \sum_{0\leq r\leq m} (-1)^r \sum_{T\subseteq A, \lvert T \rvert= r} \operatorname{setCaptureProbability}\left(q, f, T\right)) \land (\operatorname{Odd}\left(m\right) \Rightarrow \sum_{0\leq r\leq m} (-1)^r \sum_{T\subseteq A, \lvert T \rvert= r} \operatorname{setCaptureProbability}\left(q, f, T\right) \leq \operatorname{escapeProbability}\left(q, f\right)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/BonferroniTruncation.escape_bonferroni_truncation` (`✓ std3`). ∎

*Citation.* Janos Galambos (1977). *Bonferroni Inequalities*. DOI: [10.1214/aop/1176995765](https://doi.org/10.1214/aop/1176995765).

*Commentary.*

For each sample, the capture count converts the cardinality-r intersection sum into a binomial coefficient. Mathlib's exact partial alternating-binomial identity leaves a nonnegative binomial coefficient with sign determined by m.

Nonnegative sample weights preserve the pointwise inequality. No marginal-normalisation hypothesis is needed, so the theorem also applies to nonnegative finite weights whose total mass is not one.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/BonferroniTruncation.escape_bonferroni_truncation`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity](BinomialMomentIdentity.md)
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni](FiniteBonferroni.md)
