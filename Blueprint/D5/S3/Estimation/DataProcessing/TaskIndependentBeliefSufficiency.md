# Task-Independent Belief Sufficiency

## Abstract

A belief identifies Bayes value simultaneously for every future decision task.

**Theorem 1.1 (The belief quotient is sufficient for every Bayes decision problem).**

$$\begin{gathered}\forall X, H, P, F: Type,\\{}\operatorname{MeasurableSpace}(X), \operatorname{MeasurableSpace}(F),\\{}pi: H \to \operatorname{ProbabilityMeasure}(X),\\{}Q: P \to \{kappa: \operatorname{Kernel}(X, F) \mid \operatorname{IsMarkovKernel}(kappa)\},\\{}h, h': H,\\{}pi(h) = pi(h') \Rightarrow\\{}\forall p: P, A: Type,\\{}ell: X \to A \to ENNReal,\\{}\operatorname{inf}_{d: F \to A} \operatorname{lintegral}(x, \operatorname{lintegral}(f, ell(x)(d(f)), Q(p)(x)), pi(h)) = \operatorname{inf}_{d: F \to A} \operatorname{lintegral}(x, \operatorname{lintegral}(f, ell(x)(d(f)), Q(p)(x)), pi(h')).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/TaskIndependentBeliefSufficiency.task_independent_belief_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Histories map to probability measures on an arbitrary measurable hidden state. Each future policy supplies a Markov kernel from that state to a complete future transcript.

A terminal decision may depend on the entire future transcript. Its conditional loss is integrated first against the policy kernel and then against the current posterior; the infimum ranges over every such decision rule.

Equality of two history posteriors preserves this value for every policy, action carrier, and nonnegative extended-real loss simultaneously.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/TaskIndependentBeliefSufficiency.task_independent_belief_sufficiency`
