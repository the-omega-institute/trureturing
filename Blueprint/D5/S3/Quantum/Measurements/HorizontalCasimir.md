# Horizontal Casimir Noncancellation

## Abstract

A positive multiplicity-weighted sum of local transverse squares cannot vanish by cancellation.

**Definition 1.1 (The finite-window horizontal Casimir).**

$$\begin{gathered}\forall O: Type,\\T: \operatorname{Finset}\left(O\right), m: O \to \mathbb{N},\\w: O \to \mathbb{R}, delta: O \to \mathbb{R},\\\operatorname{horizontalCasimir}\left(T, m, w, delta\right) = \sum_{o \in T} m\left(o\right) \cdot w\left(o\right) \cdot delta\left(o\right)^{2}.\end{gathered}$$

*Formalization.* `D5/S3/Quantum/Measurements/HorizontalCasimir.horizontalCasimir` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite orbit window T, the horizontal Casimir is the sum over T of the natural multiplicity, the real weight, and the squared real transverse displacement.

**Theorem 1.2 (The horizontal Casimir vanishes exactly coordinatewise).**

$$\begin{gathered}\forall O: Type,\\T: \operatorname{Finset}\left(O\right), m: O \to \mathbb{N},\\w: O \to \mathbb{R}, delta: O \to \mathbb{R},\\(\forall o \in T, 0 < m\left(o\right)) \Rightarrow\\(\forall o \in T, 0 < w\left(o\right)) \Rightarrow\\(\operatorname{horizontalCasimir}\left(T, m, w, delta\right) = 0) \iff (\forall o \in T, delta\left(o\right) = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/HorizontalCasimir.horizontal_casimir_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public statement retains the finite window and requires every selected multiplicity and every selected weight to be strictly positive.

Its forward implication says that zero Casimir forces every selected transverse displacement to vanish. Its reverse implication says that pointwise vanishing makes the same source-defined sum zero. Thus phases, signs, or correlations cannot cancel these local squares.

The result is finite-dimensional and algebraic. It uses no Riemann-hypothesis premise or unformalized section-level bridge.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/HorizontalCasimir.horizontalCasimir`
- Truth anchor: `D5/S3/Quantum/Measurements/HorizontalCasimir.horizontal_casimir_eq_zero_iff`
