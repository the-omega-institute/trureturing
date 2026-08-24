# Universal Sufficiency of the Posterior

## Abstract

Equal finite-state posteriors remain equal under a common observation update and give equal normalized one-step Bayes values for every action type and real loss.

**Lemma 1.1 (A posterior update depends only on the current posterior).**

$$\begin{gathered}\forall \theta, O, \operatorname{Finite}\left(\theta\right),\\{}L: \theta \times O \to \mathbb{R}_{\geq 0},\\{}p, pPrime: \theta \to \mathbb{R}_{\geq 0}, y: O,\\{}p = pPrime \Rightarrow \operatorname{posteriorUpdate}\left(L, p, y\right) =\\{}\operatorname{posteriorUpdate}\left(L, pPrime, y\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency.posterior_update_depends_only_on_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common observation likelihood updates a finite-state posterior by multiplying each state weight by its likelihood and normalizing the resulting weights.

If two current posteriors are the same function on the state space, then every updated numerator and the shared normalizing sum are the same for any observation. The updated posteriors therefore agree, including when the normalizer is zero because division is totalized.

**Theorem 1.2 (Equal posteriors have every conditional Bayes value in common).**

$$\begin{gathered}\forall \theta, H, \operatorname{Finite}\left(\theta\right),\\{}j: \theta \times H \to \mathbb{R}_{\geq 0}, h, hPrime: H,\\{}\operatorname{posterior}\left(j, h\right) = \operatorname{posterior}\left(j, hPrime\right) \Rightarrow\\{}\forall A, \ell: \theta \times A \to \mathbb{R},\\{}\operatorname{conditionalBayesValue}\left(j, h, \ell\right) =\\{}\operatorname{conditionalBayesValue}\left(j, hPrime, \ell\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency.posterior_universal_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A history determines a totalized posterior by normalizing its finite nonnegative state weights. A zero-mass history yields the zero posterior, so the statement covers zero-mass histories without a separate positivity assumption.

For any action type and real loss, equal posterior functions give the same expected loss at every action. Their sets of attainable conditional risks are therefore identical, and taking the real infimum gives equal conditional Bayes values.

The conclusion is universal over action types and one-step losses. It establishes posterior sufficiency for these normalized conditional values, but does not assert a result about arbitrary-horizon experiment policies.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency.posterior_universal_sufficiency`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency.posterior_update_depends_only_on_posterior`
