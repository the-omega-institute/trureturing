# Effective-Image Naturality

## Abstract

Transport factorization is natural on the effective image.

**Theorem 1.1 (Naturality on the effective image).**

$$\forall X, Xprime, Y, Yprime, W, Wprime: \operatorname{Type},\ C: \operatorname{Concept}(X, Y), Cprime: \operatorname{Concept}(Xprime, Yprime), T: \operatorname{Concept}(X, W), Tprime: \operatorname{Concept}(Xprime, Wprime), f: \operatorname{Concept}(Y, W), fprime: \operatorname{Concept}(Yprime, Wprime), Xmap: \operatorname{Concept}(X, Xprime), Bmap: \operatorname{Concept}(Y, Yprime), Ymap: \operatorname{Concept}(W, Wprime),\ Tprime \circ Xmap = Ymap \circ T \land Cprime \circ Xmap = Bmap \circ C \land T = f \circ C \land Tprime = fprime \circ Cprime \Rightarrow\ \forall y: W, y \in \operatorname{range}(C) \Rightarrow Ymap(f(y)) = fprime(Bmap(y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality.effective_image_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and target carriers are explicit concept readouts. The transport equation and the readout equation are both public, as are the two factorization equations for the current and transported maps.

For every value in the range of the first readout, transporting after applying its factor equals applying the transported factor after the readout transport. The proof evaluates the four public equations at a source point and uses equality congruence.

The canonical Concept carrier is imported from the existing family. Repository and pinned-library searches found no exact theorem packaging these two naturality clauses with the effective-image conclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality.effective_image_naturality`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
