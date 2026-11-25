# Effective-Image Naturality

## Abstract

Transport factorization is natural on the effective image.

**Theorem 1.1 (Naturality on the effective image).**

$$\forall X, Xprime, Y, Yprime, W, Wprime: \operatorname{Type},\ C: X \to Y, Cprime: Xprime \to Yprime, T: X \to W, Tprime: Xprime \to Wprime, f: Y \to W, fprime: Yprime \to Wprime, Xmap: X \to Xprime, Bmap: Y \to Yprime, Ymap: W \to Wprime,\ (\forall x, Tprime(Xmap(x)) = Ymap(T(x))) \land (\forall x, Cprime(Xmap(x)) = Bmap(C(x))) \land (\forall x, T(x) = f(C(x))) \land (\forall x, Tprime(x) = fprime(Cprime(x))) \Rightarrow\ \forall y: Y, y \in \operatorname{range}(C) \Rightarrow Ymap(f(y)) = fprime(Bmap(y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality.effective_image_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and target carriers are explicit concept readouts. The transport equation and the readout equation are both public, as are the two factorization equations for the current and transported maps.

For every value in the range of the first readout, transporting after applying its factor equals applying the transported factor after the readout transport. A source point witnessing image membership supplies the four pointwise equations used in the proof.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality.effective_image_naturality`
