# Context Extension Composition

## Abstract

Sequential context embeddings compose, and their new-region charges add.

**Proposition 1.1 (Composition transports q and splits the new region).**

$$ell[A] = k[j[A]] \land \left(R_{ell} = R_{k} \cup k[R_{j}] \land \left(\operatorname{Disjoint}\left(R_{k}, k[R_{j}]\right) \land \left(\operatorname{charge}\left(E, R_{ell}\right) = \operatorname{charge}\left(E, R_{k}\right) + \operatorname{charge}\left(D, R_{j}\right) \land \operatorname{q}\left(E, k[j[A]]\right) = \operatorname{q}\left(C, A\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComposition.context_extension_composition_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let j map the archive of C injectively into that of D, and k map the archive of D injectively into that of E. Each map preserves time, position, sign, and source tree, and preserves and reflects causality. Their full current-region guards are j(x) in OmegaD iff x in OmegaC, and k(y) in OmegaE iff y in OmegaD, for every archived x and y. Equivalently j[OmegaC] = intersection(OmegaD, range(j)), and k[OmegaD] = intersection(OmegaE, range(k)). The composite ell is defined pointwise by ell(x) = k(j(x)); it preserves this full guard, including no reactivation of old noncurrent events. Square brackets denote direct images. Put Rj = OmegaD minus j[OmegaC], Rk = OmegaE minus k[OmegaD], and Rell = OmegaE minus ell[OmegaC]. Let A be any selection contained in OmegaC.

The signed charge therefore adds across the two extension steps, while the selected q readout is transported unchanged through both maps. This composition API is a companion result; no separate source coverage is asserted for it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComposition.context_extension_composition_spec`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement](ContextExtensionComplement.md)
