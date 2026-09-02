# Symmetric Off-Line Quartic

## Abstract

An entire function exists that obeys the reflection and conjugation functional equations, has a zero, and has every zero off the critical line.

**Theorem 1.1 (A fully symmetric off-line entire function exists).**

$$\exists F \in (\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)),\; \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), F\right) \land \left(\left(\exists s \in \operatorname{Complex}\left(\right),\; F\left(s\right) = 0\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; F\left(1 - s\right) = F\left(s\right)\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; F\left(\operatorname{conj}\left(s\right)\right) = \operatorname{conj}\left(F\left(s\right)\right)\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; F\left(s\right) = 0 \Rightarrow \operatorname{Re}\left(s\right) \ne \operatorname{criticalAbscissa}\left(\right)\right) \land \left(\neg \left(\forall G \in (\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)),\; \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), G\right) \Rightarrow \left(\left(\exists s \in \operatorname{Complex}\left(\right),\; G\left(s\right) = 0\right) \Rightarrow \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; G\left(1 - s\right) = G\left(s\right)\right) \Rightarrow \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; G\left(\operatorname{conj}\left(s\right)\right) = \operatorname{conj}\left(G\left(s\right)\right)\right) \Rightarrow \left(\forall s \in \operatorname{Complex}\left(\right),\; G\left(s\right) = 0 \Rightarrow \operatorname{Re}\left(s\right) = \operatorname{criticalAbscissa}\left(\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic.symmetric_off_line_entire_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness is the centered quartic from the family theorem at unit transverse and vertical displacements. It is complex differentiable everywhere and has an explicit zero.

The quartic obeys the reflection identity and conjugation covariance pointwise. Every zero has real part different from the critical abscissa; applying a hypothetical universal localization implication with the same functional equations gives the displayed contradiction.

## References

- Truth anchor: `D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic.symmetric_off_line_entire_exists`
