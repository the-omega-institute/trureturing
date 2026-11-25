# Effective-Image Naturality and Surjective Lift

## Abstract

Transport factorization is natural on the effective image and globally for a surjective readout.

**Theorem 1.1 (Image-local naturality extends across a surjective readout).**

$$\begin{gathered}\forall XE, XEPrime, YE, YEPrime, WE, WEPrime: \operatorname{Type},\\{}C: XE \to YE, CPrime: XEPrime \to YEPrime,\\{}T: XE \to WE, TPrime: XEPrime \to WEPrime,\\{}f: YE \to WE, fPrime: YEPrime \to WEPrime,\\{}Xmap: XE \to XEPrime, Bmap: YE \to YEPrime, Ymap: WE \to WEPrime,\\{}(\forall x, TPrime(Xmap(x)) = Ymap(T(x))) \land\\{}(\forall x, CPrime(Xmap(x)) = Bmap(C(x))) \land\\{}(\forall x, T(x) = f(C(x))) \land\\{}(\forall x, TPrime(x) = fPrime(CPrime(x))) \Rightarrow\\{}(\forall y: YE, y \in \operatorname{range}(C) \Rightarrow Ymap(f(y)) = fPrime(Bmap(y))) \land\\{}(\operatorname{Surjective}(C) \Rightarrow (\forall y: YE, Ymap(f(y)) = fPrime(Bmap(y)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift.effective_image_naturality_and_surjective_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transport square, readout square, and both target factorizations are public premises on their exact carriers.

The first conclusion states naturality on the range of the current readout. The second independently assumes that readout is surjective and states the equation on its full codomain.

The image-local clause is imported from the frozen family theorem; surjectivity supplies a source representative for the global clause.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift.effective_image_naturality_and_surjective_lift`
- Dependency: [D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality](../Transport/EffectiveImageNaturality.md)
