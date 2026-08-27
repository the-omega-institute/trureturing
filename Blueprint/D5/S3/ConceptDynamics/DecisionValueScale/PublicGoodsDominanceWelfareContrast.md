# Public Goods Dominance-Welfare Contrast

## Abstract

Private noncontribution dominance contrasts with maximal unanimous-contribution welfare.

**Theorem 1.1 (Private incentives and social welfare point in opposite directions).**

$$\forall n \in Nat, b \in Real, c \in Real,\; \left(2 \le n \land \left(c < b \land \frac{b}{n} < c\right)\right) \Rightarrow \operatorname{let} \operatorname{u}\left(i, a\right) := \frac{b}{n} \times \operatorname{sum}\left(j, \operatorname{Fin}\left(n\right), \operatorname{level}\left(a_{j}\right)\right) - c \times \operatorname{level}\left(a_{i}\right); \operatorname{let} \operatorname{W}\left(a\right) := \operatorname{sum}\left(i, \operatorname{Fin}\left(n\right), \operatorname{u}\left(i, a\right)\right); \left(\forall i \in \operatorname{Fin}\left(n\right), a \in \operatorname{Fin}\left(n\right) \to Bool,\; \operatorname{u}\left(i, \operatorname{update}\left(a, i, 1\right)\right) < \operatorname{u}\left(i, \operatorname{update}\left(a, i, 0\right)\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(n\right) \to Bool,\; \operatorname{W}\left(a\right) = (b - c) \times \operatorname{sum}\left(j, \operatorname{Fin}\left(n\right), \operatorname{level}\left(a_{j}\right)\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(n\right) \to Bool,\; \operatorname{W}\left(a\right) \le \operatorname{W}\left(\operatorname{const}\left(1\right)\right)\right) \land \operatorname{W}\left(\operatorname{const}\left(0\right)\right) < \operatorname{W}\left(\operatorname{const}\left(1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/PublicGoodsDominanceWelfareContrast.public_goods_dominance_welfare_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported contribution level, aggregate, and zero-compensation utility construct the source payoff. Changing one agent's action to contribution changes that payoff by b/n-c, independently of the other actions.

Summing the same individual utilities counts every contribution benefit n times and its private cost once. The resulting welfare coefficient b-c is positive, so unanimous contribution is socially maximal even though noncontribution is privately strictly dominant.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/PublicGoodsDominanceWelfareContrast.public_goods_dominance_welfare_contrast`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold](../DecisionValue/ContributionIncentiveThreshold.md)
