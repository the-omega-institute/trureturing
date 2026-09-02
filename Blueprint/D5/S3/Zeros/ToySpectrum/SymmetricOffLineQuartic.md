# Symmetric Off-Line Quartic

## Abstract

An entire function exists whose nonempty zero set has full reflection and conjugation symmetry while every zero remains off the critical line.

**Theorem 1.1 (A fully symmetric off-line entire function exists).**

$$\exists F \in (\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)),\; \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), F\right) \land \left(\left(\exists s \in \operatorname{Complex}\left(\right),\; F\left(s\right) = 0\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; F\left(s\right) = 0 \Rightarrow F\left(1 - s\right) = 0\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; F\left(s\right) = 0 \Rightarrow F\left(\operatorname{conj}\left(s\right)\right) = 0\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; F\left(s\right) = 0 \Rightarrow \operatorname{Re}\left(s\right) \ne \operatorname{criticalAbscissa}\left(\right)\right) \land \left(\neg \left(\forall G \in (\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)),\; \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), G\right) \Rightarrow \left(\left(\exists s \in \operatorname{Complex}\left(\right),\; G\left(s\right) = 0\right) \Rightarrow \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; G\left(s\right) = 0 \Rightarrow G\left(1 - s\right) = 0\right) \Rightarrow \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; G\left(s\right) = 0 \Rightarrow G\left(\operatorname{conj}\left(s\right)\right) = 0\right) \Rightarrow \left(\forall s \in \operatorname{Complex}\left(\right),\; G\left(s\right) = 0 \Rightarrow \operatorname{Re}\left(s\right) = \operatorname{criticalAbscissa}\left(\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic.symmetric_off_line_entire_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness is the centered quartic from the family theorem at unit transverse and vertical displacements. It is complex differentiable everywhere and has an explicit zero, so the zero-set clauses are not vacuous.

Reflection invariance and conjugation covariance of the quartic imply invariance of its zero set under both generators. Every zero has real part different from the critical abscissa; applying a hypothetical universal localization implication to the same nonempty zero set gives the displayed contradiction.

## References

- Truth anchor: `D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic.symmetric_off_line_entire_exists`
