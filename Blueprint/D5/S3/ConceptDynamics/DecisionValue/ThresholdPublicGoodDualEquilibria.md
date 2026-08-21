# Threshold Public-Good Dual Equilibria

## Abstract

An all-or-nothing public good has both unanimous contribution and unanimous noncontribution equilibria.

**Definition 1.1 (Unanimous contribution).**

Lean statement: `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.allContribute`

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.allContribute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public good succeeds exactly when every agent's Boolean action is contribution.

**Definition 1.2 (All-or-nothing public-good utility).**

Lean statement: `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.thresholdUtility`

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.thresholdUtility` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Success gives every agent the common benefit. A contributor pays the cost whether the public good succeeds or fails.

**Definition 1.3 (Unilateral stability).**

Lean statement: `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.nashStable`

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.nashStable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A profile is stable when every agent's utility at the profile is at least its utility after any unilateral Boolean action update.

**Theorem 1.4 (Both unanimous profiles are stable).**

$$\forall n\in \mathbb{N}, b, c\in \mathbb{R}, 2 \leq n \land 0 < c < b \Rightarrow\\{}\operatorname{nashStable}\left(b, c, 1^n\right) \land \operatorname{nashStable}\left(b, c, 0^n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.threshold_public_good_dual_equilibria` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source proof requires at least two agents: only then does one lone contributor fail to reach unanimity. This restriction is explicit in the theorem statement together with zero less than cost less than benefit.

At unanimous contribution, deviating destroys the benefit and changes payoff from benefit minus cost to zero. At unanimous noncontribution, deviating alone changes payoff from zero to negative cost.

The two equilibrium conclusions are separate public conjuncts over the same utility constructed from the all-or-nothing success rule.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.allContribute`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.nashStable`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.thresholdUtility`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.threshold_public_good_dual_equilibria`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold](ContributionIncentiveThreshold.md)
