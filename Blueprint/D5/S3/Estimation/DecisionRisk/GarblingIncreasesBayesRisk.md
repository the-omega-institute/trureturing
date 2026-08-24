# Garbling Increases Bayes Risk

## Abstract

Blackwell dominance is reflexive and transitive, includes measurable deterministic post-processing, and its garblings cannot improve optimal Bayes risk.

**Lemma 1.1 (Blackwell dominance is reflexive).**

$$\forall P: \operatorname{Kernel}\left(\theta, X\right), \operatorname{BlackwellDominates}\left(P, P\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.blackwellDominates_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every experiment dominates itself because the identity kernel is a Markov kernel and garbling by that kernel leaves the experiment unchanged.

Thus the experiment itself is recovered by an admissible garbling, which supplies the witness required by Blackwell dominance.

**Lemma 1.2 (Blackwell dominance is transitive).**

$$\begin{gathered}\forall P: \operatorname{Kernel}\left(\theta, X\right), Q: \operatorname{Kernel}\left(\theta, X_{1}\right), R: \operatorname{Kernel}\left(\theta, X_{2}\right),\\{}\operatorname{BlackwellDominates}\left(P, Q\right) \land \operatorname{BlackwellDominates}\left(Q, R\right) \Rightarrow\\{}\operatorname{BlackwellDominates}\left(P, R\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.blackwellDominates_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose Q is obtained from P through one Markov garbling and R is obtained from Q through another. Composing the two garbling kernels gives a Markov kernel directly from the output of P to the output of R.

Associativity of kernel composition identifies this composite garbling with R, so P Blackwell-dominates R.

**Lemma 1.3 (Measurable maps are Blackwell garblings).**

$$\begin{gathered}\forall P: \operatorname{Kernel}\left(\theta, X\right), f: X \to X_{1},\\{}\operatorname{Measurable}\left(f\right) \Rightarrow\\{}\operatorname{BlackwellDominates}\left(P, \operatorname{map}\left(P, f\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.blackwellDominates_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A measurable transformation of the observation space determines a deterministic Markov kernel. Applying that kernel after an experiment is exactly the mapped experiment.

Consequently every measurable deterministic post-processing of an experiment is a Blackwell garbling of the original experiment.

**Theorem 1.4 (Garbling cannot decrease optimal Bayes risk).**

$$\begin{gathered}\forall P: \operatorname{Kernel}\left(\theta, X\right), Q: \operatorname{Kernel}\left(\theta, X_{1}\right),\\{}\operatorname{BlackwellDominates}\left(P, Q\right) \Rightarrow\\{}\forall \ell: \theta \to Y \to ENNReal, \pi: \operatorname{Measure}\left(\theta\right),\\{}\operatorname{bayesRisk}\left(\ell, P, \pi\right) \leq \operatorname{bayesRisk}\left(\ell, Q, \pi\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.bayesRisk_le_of_blackwellDominates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Q is obtained by applying a Markov garbling to P, then every decision procedure based on Q can also be run after observing P: first garble the observation and then apply that procedure.

Taking the infimum over all Markov decision rules therefore gives no larger Bayes risk for P than for Q. The comparison holds for every ENNReal-valued loss and every measure used as the prior.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.bayesRisk_le_of_blackwellDominates`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.blackwellDominates_map`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.blackwellDominates_refl`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.blackwellDominates_trans`
