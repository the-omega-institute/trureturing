# Benefit Probability Bounds

## Abstract

The two Boolean potential-outcome marginals give algebraic bounds on the benefit mass of every normalized nonnegative joint law.

**Theorem 1.1 (Potential-outcome marginals bound the benefit probability).**

$$\forall mass \in \operatorname{Prod}\left(Bool, Bool\right) \to Real,\; \left({\forall pair \in \operatorname{Prod}\left(Bool, Bool\right),\; 0 \le mass\left(pair\right)} \land mass\left(\operatorname{pair}\left(false, false\right)\right) + mass\left(\operatorname{pair}\left(false, true\right)\right) + mass\left(\operatorname{pair}\left(true, false\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right) = 1\right) \Rightarrow \left(\operatorname{max}\left(0, mass\left(\operatorname{pair}\left(false, true\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right) - \left(mass\left(\operatorname{pair}\left(true, false\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right)\right)\right) \le mass\left(\operatorname{pair}\left(false, true\right)\right) \land mass\left(\operatorname{pair}\left(false, true\right)\right) \le \operatorname{min}\left(mass\left(\operatorname{pair}\left(false, true\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right), 1 - \left(mass\left(\operatorname{pair}\left(true, false\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/BenefitProbabilityBounds.benefit_probability_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mass be a normalized nonnegative joint law of the Boolean pair of potential outcomes. The benefit probability is the mass of the false-true response type.

The treatment-one marginal is the sum of the false-true and true-true masses. The treatment-zero marginal is the sum of the true-false and true-true masses.

Nonnegativity of the true-false cell gives the lower marginal-difference bound. Nonnegativity of the true-true and false-false cells gives the two upper bounds.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/BenefitProbabilityBounds.benefit_probability_bounds`
- Dependency: [D5/S3/ConceptDynamics/Causal/PrincipalStrata](PrincipalStrata.md)
