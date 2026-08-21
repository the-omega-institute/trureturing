# Effective-Image Uniqueness

## Abstract

A descended process map is uniquely determined on the effective image of its concept readout, and globally unique when that readout is surjective.

**Theorem 1.1 (A descended map is unique exactly where the readout reaches).**

$$\forall X, Y, BC, BD: \operatorname{Type},\\qC: X \to BC, qD: Y \to BD, F: X \to Y,\\barF, barG: BC \to BD,\\(qD \circ F = barF \circ qC \land qD \circ F = barG \circ qC) \Rightarrow\\((\operatorname{Surjective}\left(qC\right) \Rightarrow barF = barG) \land\\(\neg \operatorname{Surjective}\left(qC\right) \Rightarrow (\forall x: X, barF(qC(x)) = barG(qC(x)) \land\\\forall H: BC \to BD, (qD \circ F = H \circ qC \iff \forall x: X, H(qC(x)) = barF(qC(x))) \land\\\exists b: BC, \neg \exists x: X, qC(x) = b))).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Quotients/EffectiveImageUniqueness.effective_image_uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two maps on the concept-value domain make the same process and future-readout square commute. They agree after composition with the current concept readout, hence agree at every value in its effective image.

When the current readout is surjective, agreement on its image is global agreement. When it is not surjective, a candidate makes the square commute exactly when it agrees with the first descended map on every reached value; at least one unreached value remains and its output requires an additional definition.

The proof directly applies Mathlib's Function.Surjective.injective_comp_right for global uniqueness and Set.eqOn_range for the exact effective-image restriction. Repository search found the adjacent DynamicsDescent theorem, but it treats surjective self-map descent rather than this general two-readout image statement. This closes atom generic-residual-26cd00f090db8b2a61150a3fef3a8d706caf0c313eb6cb6eae0fbb21bfbed4dc without asserting descent existence.

## References

- Truth anchor: `D5/S0/Rewriting/Quotients/EffectiveImageUniqueness.effective_image_uniqueness`
