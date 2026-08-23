# Side-Flip Positivity Rigidity

## Abstract

A side-flip-invariant nonnegative complex subspace is isotropic for the reflection form.

**Theorem 1.1 (A side-flip-invariant nonnegative subspace is isotropic).**

$$W \subseteq \mathbb{C}^{2},\ Z_\rho(W) \subseteq W,\ (\forall v \in W,\ q_J(v) \ge 0) \Rightarrow \forall v \in W,\ q_J(v) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/SideFlipPositivityRigidity.side_flip_positive_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the two complex evaluation coordinates, the side operator fixes the first coordinate and negates the second, while reflection exchanges the two coordinates. The associated real Hermitian quadratic form therefore changes sign under the side operator.

Let W be a complex linear subspace preserved by the side operator. If the reflection form is nonnegative on every vector in W, then applying nonnegativity both to v and to its side flip bounds the form by zero from both directions. Thus the form vanishes throughout W.

Repository and pinned-Mathlib searches found no exact theorem for this coordinate side-flip rigidity statement. The coordinate operators and reflection form are constructed directly, and the proof uses the explicit sign-flip computation.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/SideFlipPositivityRigidity.side_flip_positive_rigidity`
