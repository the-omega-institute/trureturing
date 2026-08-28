# Positive-Prior Conditional Independence

## Abstract

For a finite state space with a pointwise positive prior, stochastic target sufficiency is equivalent to conditional independence given the concept.

**Theorem 1.1 (Stochastic sufficiency is conditional independence).**

$$\forall X \in Type, C \in Type, Y \in Type,\; \left(\operatorname{Fintype}\left(X\right) \land \operatorname{Fintype}\left(Y\right)\right) \Rightarrow \left(\forall mu \in \operatorname{PMF}\left(X\right), K \in X \to \operatorname{PMF}\left(Y\right), concept \in X \to C,\; \left(\forall x \in X,\; 0 < mu\left(x\right)\right) \Rightarrow \operatorname{let} jointLaw := (x,(c,y)) \mapsto \operatorname{ite}\left(c = concept\left(x\right), \operatorname{toReal}\left(mu\left(x\right)\right) \cdot \operatorname{toReal}\left(K\left(x\right)\left(y\right)\right), 0\right); \left(\exists Kbar \in C \to \operatorname{PMF}\left(Y\right),\; K = \operatorname{compose}\left(Kbar, concept\right)\right) \Leftrightarrow \left(\forall x \in X, c \in C, y \in Y,\; jointLaw\left(x, c, y\right) \cdot \operatorname{marginal}\left(\operatorname{yFirstLaw}\left(jointLaw\right), c\right) = \operatorname{xyProjection}\left(jointLaw, x, c\right) \cdot \operatorname{xzProjection}\left(\operatorname{yFirstLaw}\left(jointLaw\right), c, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/PositivePriorConditionalIndependence.positive_prior_sufficiency_iff_conditional_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite source state has a pointwise positive PMF prior and a PMF-valued target kernel. A deterministic concept readout and these two probability primitives construct the displayed joint law.

The kernel factors through the concept exactly when the target and source state satisfy the cross-multiplied conditional-product identity on every concept value.

Positivity is used in the reverse direction to cancel both the state mass and the mass of its concept fiber. This upgrades the usual almost-sure statement to full-domain stochastic factorization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/PositivePriorConditionalIndependence.positive_prior_sufficiency_iff_conditional_independence`
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](../../Entropy/Submodularity/MarkovDataProcessing.md)
