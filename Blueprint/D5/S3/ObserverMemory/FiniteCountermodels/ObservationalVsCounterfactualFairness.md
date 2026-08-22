# Observational Fairness Does Not Imply Counterfactual Fairness

## Abstract

Qualification factorization on admitted states need not survive a coupled intervention.

**Theorem 1.1 (Observational fairness need not be counterfactual fairness).**

$$\begin{gathered}Adm=\left\{(0, 0), (1, 1)\right\},\\\exists g: \left\{0, 1\right\} \to \left\{0, 1\right\}, \forall p, r, (p, r) \in Adm \Rightarrow J((p, r))=g(r),\\(0, 0) \in Adm \land (1, 1) \in Adm,\\J((0, 0))=0 \land J((1, 1))=1,\\I((0, 0))=(1, 1) \land J(I((0, 0)))=1,\\\neg {\forall p, r, (p, r) \in Adm \Rightarrow J(I((p, r)))=J((p, r))}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/ObservationalVsCounterfactualFairness.observational_fairness_does_not_imply_counterfactual_fairness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admitted population contains exactly the two diagonal Boolean states. Qualification and decision both read the second coordinate, so the decision factors through qualification via the identity Boolean map.

The intervention flips the protected bit and causally resets the qualification to that new bit. It therefore sends (0,0) to (1,1), changing the named decision from zero to one. This explicit witness refutes pointwise counterfactual invariance while preserving observational factorization.

Searches of D5 and pinned Mathlib found factorization machinery but no finite fairness predicate or theorem combining these admission and intervention clauses.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/ObservationalVsCounterfactualFairness.observational_fairness_does_not_imply_counterfactual_fairness`
