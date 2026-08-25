# Prediction Closure Criterion

## Abstract

A deterministic finite interface is predictively closed exactly when past and future factor conditionally on every active interface value.

**Theorem 1.1 (Prediction closure is conditional factorization).**

$$\begin{gathered}\forall P, C, F,\\{}[\operatorname{Fintype}(P)] [\operatorname{Fintype}(C)] [\operatorname{Fintype}(F)],\\{}q: P \to C, p: C \times (P \times F) \to \mathbb{R},\\{}((\forall x, 0 \leq p(x)) \land \sum_{x} p(x) = 1 \land \forall c, u, v, p(c, (u, v)) \neq 0 \Rightarrow c = q(u)) \Rightarrow\\{}\operatorname{conditionalMutualInformation}(p) = 0 \iff \\{}\forall c, p_{C}(c) \neq 0 \Rightarrow \\{}\forall u, v, p_{PF \mid c}(u, v) = p_{P \mid c}(u) \cdot p_{F \mid c}(v).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/PredictionClosureCriterion.prediction_closure_iff_markov` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be the complete finite past, F the finite future, and C a finite current interface. The public graph-support hypothesis states that every nonzero cell has C equal to the supplied deterministic readout q of P. The joint mass function is nonnegative and normalized.

The predictive-closure defect is constructed as the repository conditional mutual information of the law on C times (P times F). It vanishes exactly when, for every C-value of nonzero marginal mass, the conditional joint law of P and F is the product of its own marginals. This is the finite Markov-chain condition from past through the current interface to future.

The proof directly applies the frozen zero conditional-mutual-information characterization. That imported result is stronger than needed because conditional factorization does not require the interface to be a deterministic readout, but the source restriction remains public.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/PredictionClosureCriterion.prediction_closure_iff_markov`
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](MarkovDataProcessing.md)
