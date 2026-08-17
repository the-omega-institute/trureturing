# Dynamics Descent

## Abstract

A self-map descends uniquely through a quotient exactly when it preserves fibers.

**Theorem 1.1 (Fiber preservation characterizes quotient descent).**

$$\forall X, B,\ \forall q: X \to B, F: X \to X,\ \operatorname{Surjective}\left(q\right) \Rightarrow \left(\exists! descended: B \to B,\ q \circ F = descended \circ q\right) \iff \left(\forall x, y,\ q(x) = q(y) \Rightarrow q(F(x)) = q(F(y))\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Quotients/DynamicsDescent.dynamics_descends_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a surjection from X onto B and let F be a self-map of X. There is a unique self-map of B making the quotient square commute if and only if F maps q-equivalent points to q-equivalent points.

For existence, choose one representative of every fiber and apply F before projecting again. Fiber preservation makes this choice independent on the image of q. Surjectivity then makes right composition by q injective, which proves uniqueness.

Pinned Mathlib and Loogle searches found no exact theorem combining both directions with uniqueness. The proof directly reuses Function.Surjective.injective_comp_right for the uniqueness step.

## References

- Truth anchor: `D5/S0/Rewriting/Quotients/DynamicsDescent.dynamics_descends_iff`
