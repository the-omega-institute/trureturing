# Causal State Factorization

## Abstract

Predictively sufficient interfaces uniquely factor onto the causal-state image.

**Theorem 1.1 (Predictive sufficiency induces the unique causal-state factor).**

$$\begin{gathered}\forall P, R, L: \operatorname{Type},\\{}r: P \to R, K: P \to L, Kbar: R \to L,\\{}K = Kbar \circ r \Rightarrow\\{}(\exists! phi: \operatorname{range}\left(r\right) \to \operatorname{range}\left(K\right),\\{}\operatorname{rangeFactorization}\left(K\right) = phi \circ \operatorname{rangeFactorization}\left(r\right) \land\\{}\forall s: \operatorname{range}\left(r\right), \operatorname{val}\left(phi(s)\right) = Kbar(\operatorname{val}\left(s\right))) \land\\{}\forall p, p': P, K(p) \neq K(p') \Rightarrow r(p) \neq r(p').\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization.causal_state_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K assign a future law to each past and let r be an interface. Predictive sufficiency supplies a predictor Kbar on interface values such that K equals Kbar after r.

The canonical causal-state map is the range factorization of K. The theorem constructs its unique factor through the realized image of r and states publicly that this factor agrees with Kbar on every realized interface value.

Consequently two pasts with different future laws cannot have the same interface value. Using the realized image is essential: without surjectivity of r, Kbar may take additional values away from that image, so its whole image need not equal the image of K.

The proof directly applies the repository's exact inductive sufficiency criterion. Pinned Mathlib supplies rangeFactorization, its surjectivity theorem, and uniqueness after composition with a surjection.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization.causal_state_factorization`
- Dependency: [D5/S3/ConceptDynamics/Refinement/InductiveSufficiency](../../ConceptDynamics/Refinement/InductiveSufficiency.md)
