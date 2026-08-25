# Visible Dynamics Descent Criterion

## Abstract

Visible bounded dynamics closes exactly when hidden-to-visible flow vanishes.

**Theorem 1.1 (Visible descent is equivalent to a zero cross block).**

$$\begin{gathered}\forall K, H, V, P, Q, T,\\{}\operatorname{HilbertSetup}(K, H, V, P, Q, T) \Rightarrow\\{}(\exists Tbar: V \to V, P \circ T = Tbar \circ P) \iff P \circ T \circ Q = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/VisibleDynamicsDescentCriterion.visible_dynamics_descends_iff_cross_block_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be orthogonal projection onto a visible subspace V of a Hilbert space, and let Q be projection onto its orthogonal complement.

A bounded linear flow T factors through P as a bounded evolution on V exactly when the hidden-to-visible block PTQ is zero.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/VisibleDynamicsDescentCriterion.visible_dynamics_descends_iff_cross_block_zero`
- Dependency: [D5/S3/Observer/VisibleDescent/LinearDescentCriterion](LinearDescentCriterion.md)
