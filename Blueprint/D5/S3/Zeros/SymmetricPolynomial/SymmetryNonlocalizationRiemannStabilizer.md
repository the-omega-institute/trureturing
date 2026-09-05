# Symmetry Nonlocalization and Riemann Stabilizers

## Abstract

A fully symmetric quartic can have only off-line zeros, while RH says every nontrivial zeta zero is mirror-fixed.

**Theorem 1.1 (Full symmetry does not localize zeros).**

$$\begin{aligned}\forall delta, gamma\in \mathbb{R},\\{\exists F: \mathbb{C} \to \mathbb{C},\\{}F = \operatorname{offCriticalQuartic}\left(delta, gamma\right) \land\\{}\operatorname{Differentiable}\left(\mathbb{C}, F\right) \land\\{}{\forall s: \mathbb{C}, F(1 - s) = F(s)} \land {\forall s: \mathbb{C}, F(\operatorname{conj}\left(s\right)) = \operatorname{conj}\left(F(s)\right)} \land\\{}{\forall s: \mathbb{C}, F(s) = 0 \Leftrightarrow s \in \operatorname{sourceZeros}\left(delta, gamma\right)} \land\\{}{delta \neq 0 \Rightarrow {{\forall s: \mathbb{C}, F(s) = 0 \Rightarrow \operatorname{re}\left(s\right) \neq criticalAbscissa} \land \neg{\forall s: \mathbb{C}, F(s) = 0 \Rightarrow \operatorname{re}\left(s\right) = criticalAbscissa} \land \neg{\forall F: \mathbb{C} \to \mathbb{C},\\{}\operatorname{Differentiable}\left(\mathbb{C}, F\right) \Rightarrow {\forall s: \mathbb{C}, F(1 - s) = F(s)} \land {\forall s: \mathbb{C}, F(\operatorname{conj}\left(s\right)) = \operatorname{conj}\left(F(s)\right)} \Rightarrow {\forall s: \mathbb{C}, F(s) = 0 \Rightarrow \operatorname{re}\left(s\right) = criticalAbscissa}}}}} \land \\{}{\operatorname{RiemannHypothesis} \Leftrightarrow {\forall \rho: \mathbb{C}, \operatorname{riemannZeta}\left(\rho\right) = 0 \Rightarrow \neg{\exists n\in \mathbb{N}, \rho = -2 \cdot {n + 1}} \Rightarrow \rho \neq 1 \Rightarrow \operatorname{mirror}\left(\rho\right) = \rho}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/SymmetricPolynomial/SymmetryNonlocalizationRiemannStabilizer.full_symmetry_nonlocalization_and_rh_stabilizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta and gamma, the witness is exactly P_delta,gamma(s) = (((s - 1/2) - delta)^2 + gamma^2) (((s - 1/2) + delta)^2 + gamma^2). It is complex differentiable everywhere and is invariant under s mapping to 1-s, while complex conjugation commutes with evaluation.

Its zero condition is equivalent to membership in the displayed source set {1/2 + delta + i gamma, 1/2 + delta - i gamma, 1/2 - delta + i gamma, 1/2 - delta - i gamma}. The set may collapse when either coordinate is zero. Whenever delta is nonzero, every zero remains off the critical line.

Under nonzero delta, the same witness refutes the universal implication from entire full-zeta symmetry to fixed-line localization. The final conjunct uses Mathlib's exact nontrivial-zero premises and identifies the source J with mirror(rho) = 1 - conj(rho): RiemannHypothesis holds exactly when every such zero is fixed by mirror.

## References

- Truth anchor: `D5/S3/Zeros/SymmetricPolynomial/SymmetryNonlocalizationRiemannStabilizer.full_symmetry_nonlocalization_and_rh_stabilizer`
- Dependency: [D5/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization](FullSymmetryNonlocalization.md)
