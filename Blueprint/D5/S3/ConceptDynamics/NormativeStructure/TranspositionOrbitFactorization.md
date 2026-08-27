# Transposition Invariance and Orbit Factorization

## Abstract

Swap invariance is full role invariance and canonical orbit factorization.

**Theorem 1.1 (Transpositions generate full role invariance).**

$$\begin{gathered}\forall X, U, I: \operatorname{Type},\\{}T: X \times U \times I \times I \to Prop,\\{}R: \operatorname{Perm}\left(I\right) \to \left(X \times U \times I \times I \to X \times U \times I \times I\right) := \Lambda sigma: \operatorname{Perm}\left(I\right), \Lambda z: X \times U \times I \times I, \operatorname{relabelRoles}\left(sigma, z\right),\\{}p: X \times U \times I \times I \to \operatorname{Quotient}\left(\operatorname{orbitRel}\left(\operatorname{Perm}\left(I\right), X \times U \times I \times I, R\right)\right) := \operatorname{orbitProjection}\left(\operatorname{Perm}\left(I\right), X \times U \times I \times I, R\right),\\{}\operatorname{Finite}\left(I\right) \Rightarrow\\{}[((\forall i: I, j: I, z: X \times U \times I \times I, T\left(R\left(\operatorname{swap}\left(i, j\right), z\right)\right) \Leftrightarrow T\left(z\right)) \iff (\forall sigma: \operatorname{Perm}\left(I\right), z: X \times U \times I \times I, T\left(R\left(sigma, z\right)\right) \Leftrightarrow T\left(z\right))) \land\\{}((\forall sigma: \operatorname{Perm}\left(I\right), z: X \times U \times I \times I, T\left(R\left(sigma, z\right)\right) \Leftrightarrow T\left(z\right)) \iff (\exists D: \operatorname{Quotient}\left(\operatorname{orbitRel}\left(\operatorname{Perm}\left(I\right), X \times U \times I \times I, R\right)\right) \to Prop, T = \operatorname{compose}\left(D, p\right)))].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/TranspositionOrbitFactorization.transposition_orbit_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A permutation acts simultaneously on the actor and recipient coordinates while leaving the state and action coordinates fixed.

For a finite role carrier, invariance under every transposition is equivalent to invariance under every permutation. The proof applies Mathlib's finite permutation induction directly.

Full invariance is also equivalent to factorization through Mathlib's canonical orbit-relation quotient for this action. The finite-role instance is displayed as a premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/TranspositionOrbitFactorization.transposition_orbit_factorization`
