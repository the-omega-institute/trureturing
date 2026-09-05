# Finite Spectral Cayley Identity

## Abstract

A finite real spectrum obeys the Li-Cayley norm identity and its diagonal determinant product.

**Theorem 1.1 (The finite Li coefficient is a diagonal Hilbert-Schmidt defect).**

$$\begin{aligned}\forall J \mathrm{finite}, \gamma: J \to \mathbb{R}, n \in \mathbb{N},\\\sum_{j \in J} 2(1 - \Re(\operatorname{C}(\gamma_{j})^{n})) = \sum_{j \in J} \left|1 - \operatorname{C}(\gamma_{j})^{n}\right|^{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/FiniteSpectralCayleyIdentity.finiteLiCoefficient_eq_diagonalHilbertSchmidtDefect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a finite index type and let gamma assign a real spectral ordinate to every index. Put x(t)=1/(4t^2+1) and C(t)=1-2x(t)+2i sqrt(x(t)(1-x(t))). The denominator is positive, x(t) lies in (0,1], and the square-root radicand is nonnegative.

Each C(t) has squared norm one. Expanding the squared norm of 1-C(t)^n and using that complex conjugation preserves real parts gives the displayed identity term by term, hence after summing over J.

The same Lean module proves the first-power identity sum |1-C(gamma_j)|^2 = 4 sum x(gamma_j), and evaluates the determinant of the corresponding finite diagonal matrix as the product of its scalar spectral factors.

This corrects the source claim to the algebra justified by the stated data. No automorphic L-function, GRH implication, infinite Hilbert-Schmidt operator, or Fredholm determinant is asserted; those require analytic and operator-theoretic infrastructure not present in the formal statement.

## References

- Truth anchor: `D5/S3/Weil/FiniteSpectralCayleyIdentity.finiteLiCoefficient_eq_diagonalHilbertSchmidtDefect`
