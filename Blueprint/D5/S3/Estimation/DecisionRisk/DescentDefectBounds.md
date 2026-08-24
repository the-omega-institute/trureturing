# Bounds and Contraction for the Descent Defect

## Abstract

The optimal finite quotient-descent error is controlled by the same-fiber total-variation defect, and deterministic target postprocessing contracts that defect.

**Theorem 1.1 (Best descent error is at least half the fiber defect).**

$$\begin{gathered}\forall X, B, \operatorname{Fintype}\left(X\right), \operatorname{Nonempty}\left(X\right), \operatorname{Fintype}\left(B\right),\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}\operatorname{IsRowStochastic}\left(K\right) \Rightarrow\\{}\frac{1}{2} \operatorname{descentDefect}\left(q, K\right) \leq \operatorname{bestDescentError}\left(q, K\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/DescentDefectBounds.best_descent_error_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The descent defect is the largest total-variation distance between two rows of K whose source states have the same readout under q. The best descent error is the infimum, over row-stochastic kernels on B, of the largest distance from K at x to the candidate row at q(x).

For any candidate quotient kernel, the triangle inequality bounds every same-fiber row distance by the sum of two candidate errors, hence by twice the uniform error. Maximizing over the fiber pairs and then taking the infimum gives the factor-one-half lower bound. Row stochasticity of K also supplies a constant admissible candidate, so the infimum is taken over a nonempty family bounded below by zero.

**Lemma 1.2 (Fiber representatives bound the best descent error from above).**

$$\begin{gathered}\forall X, B, \operatorname{Fintype}\left(X\right), \operatorname{Nonempty}\left(X\right), \operatorname{Fintype}\left(B\right),\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}rep: B \to X,\\{}\operatorname{IsRowStochastic}\left(K\right) \land (\forall x: X, q(rep(q(x))) = q(x)) \Rightarrow\\{}\operatorname{bestDescentError}\left(q, K\right) \leq \operatorname{descentDefect}\left(q, K\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/DescentDefectBounds.best_descent_error_upper_bound_of_representatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A representative map chooses a source state for every readout value. The required compatibility says that, for every source state x, the representative selected at q(x) lies in the same q-fiber as x.

Using the row of K at each chosen representative defines a row-stochastic kernel on B. Its error at x is a same-fiber total-variation distance, so it is at most the descent defect. The infimum over all admissible kernels is therefore no larger than that defect.

**Lemma 1.3 (Deterministic postprocessing contracts the descent defect).**

$$\begin{gathered}\forall X, B, C, \operatorname{Fintype}\left(X\right), \operatorname{Nonempty}\left(X\right), \operatorname{Fintype}\left(B\right), \operatorname{Fintype}\left(C\right),\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}r: B \to C,\\{}\operatorname{postprocessedDescentDefect}\left(q, K, r\right) \leq \operatorname{descentDefect}\left(q, K\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/DescentDefectBounds.postprocessed_descent_defect_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A deterministic target map r induces the zero-one stochastic channel that sends each point of B to its image in C. Total variation cannot increase when the same channel is applied to both rows of a pair.

Applying this contraction to every pair of source states in the same q-fiber and then taking the finite maximum proves that the postprocessed defect is at most the original defect. No row-stochasticity assumption on K is needed for this comparison.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/DescentDefectBounds.best_descent_error_lower_bound`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/DescentDefectBounds.best_descent_error_upper_bound_of_representatives`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/DescentDefectBounds.postprocessed_descent_defect_le`
- Dependency: [D5/S3/TotalVariation/DataProcessing](../../TotalVariation/DataProcessing.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
