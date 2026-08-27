# Permanent Stability of Sequential Visible Spaces

## Abstract

A stable sequential word-effect span remains stable at every later depth.

**Theorem 1.1 (One stable sequential stage is permanently stable).**

$$\begin{gathered}\forall d: Nat, A: \operatorname{Type},\\{}J: A \to \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianSpace}(d), \operatorname{HermitianSpace}(d)), n: Nat,\\{}\operatorname{span}(\mathbb{R}, \{\operatorname{sequentialWordEffect}(J, w) \mid w: \operatorname{List}(A), \operatorname{length}(w) \le n+1\}) = \operatorname{span}(\mathbb{R}, \{\operatorname{sequentialWordEffect}(J, w) \mid w: \operatorname{List}(A), \operatorname{length}(w) \le n\}) \Rightarrow\\{}\forall m: Nat, n \le m \Rightarrow \operatorname{span}(\mathbb{R}, \{\operatorname{sequentialWordEffect}(J, w) \mid w: \operatorname{List}(A), \operatorname{length}(w) \le m\}) = \operatorname{span}(\mathbb{R}, \{\operatorname{sequentialWordEffect}(J, w) \mid w: \operatorname{List}(A), \operatorname{length}(w) \le n\}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/SequentialVisibleSpaceStability.sequential_visible_space_once_stable_permanently` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The branch alphabet indexes real-linear Heisenberg dual maps on the full Hermitian matrix carrier. Each finite word effect is the existing source-order fold of those maps applied to identity.

At depth k the visible space is stated directly as the real span of all word effects of length at most k. No parallel visible-space definition is introduced.

Consecutive-stage equality makes the stable span invariant under every branch dual. Word induction then puts every longer effect in that span, while the depth inequality supplies the reverse inclusion.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/SequentialVisibleSpaceStability.sequential_visible_space_once_stable_permanently`
- Dependency: [D5/S3/Quantum/Completion/SequentialWordObservationResidual](../Completion/SequentialWordObservationResidual.md)
