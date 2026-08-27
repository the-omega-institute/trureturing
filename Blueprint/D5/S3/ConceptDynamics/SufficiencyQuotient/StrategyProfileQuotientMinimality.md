# Strategy Profile Quotient Minimality

## Abstract

Every strategy-sufficient history interface maps uniquely onto the complete strategy-profile quotient.

**Theorem 1.1 (The strategy-profile quotient is the coarsest sufficient history interface).**

$$\forall History \in \operatorname{Type}\left(\right), FutureWord \in \operatorname{Type}\left(\right), Action \in \operatorname{Type}\left(\right), Summary \in \operatorname{Type}\left(\right), strategyProfile \in History \to \left(FutureWord \to \operatorname{PMF}\left(Action\right)\right), summary \in History \to Summary, predictor \in Summary \to \left(FutureWord \to \operatorname{PMF}\left(Action\right)\right),\; strategyProfile = \operatorname{compose}\left(predictor, summary\right) \Rightarrow \exists! factor: \operatorname{range}\left(summary\right) \to \operatorname{Quotient}\left(\operatorname{ker}\left(strategyProfile\right)\right), \forall h \in History,\; \operatorname{quotientClass}\left(strategyProfile, h\right) = factor\left(\operatorname{rangeFactorization}\left(summary, h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SufficiencyQuotient/StrategyProfileQuotientMinimality.strategy_sufficient_self_universal_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Histories, future input words, actions, and summary values are arbitrary types. A complete strategy profile assigns a probability mass function on actions to each history and future word.

The public premise supplies a predictor through the summary. The target is the named quotient by equality of complete strategy profiles, not an independently declared image or self-state carrier.

The unique factor starts on the realized range of the summary and sends every represented history to its canonical quotient class. This equation states both representative independence and the required factorization on the effective interface.

The proof instantiates the frozen minimal prediction-quotient theorem with the canonical joint readout. Pinned-library range factorization surjectivity then proves uniqueness directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SufficiencyQuotient/StrategyProfileQuotientMinimality.strategy_sufficient_self_universal_minimality`
- Dependency: [D5/S3/ConceptDynamics/SufficiencyQuotient/MinimalPredictionBeliefState](MinimalPredictionBeliefState.md)
