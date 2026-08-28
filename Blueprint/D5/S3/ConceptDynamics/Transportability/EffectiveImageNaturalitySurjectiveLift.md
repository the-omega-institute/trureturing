# Effective-Image Naturality and Surjective Lift

## Abstract

Transport factorization is natural on the effective image and globally for a surjective readout.

**Theorem 1.1 (Image-local naturality extends across a surjective readout).**

$$\begin{gathered}\forall XE, XEPrime, YE, YEPrime, WE, WEPrime: \operatorname{Type},\\{}C: \operatorname{Concept}(XE, YE), CPrime: \operatorname{Concept}(XEPrime, YEPrime),\\{}T: \operatorname{Concept}(XE, WE), TPrime: \operatorname{Concept}(XEPrime, WEPrime),\\{}f: \operatorname{Concept}(YE, WE), fPrime: \operatorname{Concept}(YEPrime, WEPrime),\\{}Xmap: \operatorname{Concept}(XE, XEPrime), Bmap: \operatorname{Concept}(YE, YEPrime), Ymap: \operatorname{Concept}(WE, WEPrime),\\{}TPrime \circ Xmap = Ymap \circ T \land\\{}CPrime \circ Xmap = Bmap \circ C \land\\{}T = f \circ C \land\\{}TPrime = fPrime \circ CPrime \Rightarrow\\{}(\forall y: YE, y \in \operatorname{range}(C) \Rightarrow Ymap(f(y)) = fPrime(Bmap(y))) \land\\{}(\operatorname{Surjective}(C) \Rightarrow (\forall y: YE, Ymap(f(y)) = fPrime(Bmap(y)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift.effective_image_naturality_and_surjective_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transport square, readout square, and both target factorizations are public premises on their exact carriers.

The first conclusion states naturality on the range of the current readout. The second independently assumes that readout is surjective and states the equation on its full codomain.

The image-local clause is imported from the frozen family theorem; surjectivity supplies a source representative for the global clause.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift.effective_image_naturality_and_surjective_lift`
- Dependency: [D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality](../Transport/EffectiveImageNaturality.md)
