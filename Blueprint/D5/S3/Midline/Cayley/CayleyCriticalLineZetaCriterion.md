# Cayley Critical-Line Zeta Criterion

## Abstract

The canonical Cayley unit circle is the critical line, and radial neutrality of all nontrivial zeta zeros characterizes the Riemann hypothesis.

**Theorem 1.1 (Cayley critical-line zeta criterion).**

$$\left(\forall s \in \operatorname{Complex}\left(\right),\; \left\lVert \operatorname{cayleyCoefficient}\left(s\right) \right\rVert = 1 \Leftrightarrow \operatorname{re}\left(s\right) = \frac{1}{2}\right) \land \left(\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow \left(\forall rho \in \operatorname{Complex}\left(\right),\; \left(\operatorname{riemannZeta}\left(rho\right) = 0 \land \left(\left(\neg \left(\exists n \in \operatorname{Nat}\left(\right),\; rho = -\left(2 \cdot \left(n + 1\right)\right)\right)\right) \land rho \ne 1\right)\right) \Rightarrow \operatorname{logarithmicRadialDefect}\left(rho\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/Cayley/CayleyCriticalLineZetaCriterion.cayley_critical_line_zeta_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient c(s) is the imported canonical Cayley coordinate (s - 1)/s. Its norm is one exactly when the real part of s is one half; Lean's totalized value at zero satisfies the same equivalence because neither side holds there.

The radial quantity beta(rho) is the imported logarithmic radial defect log |c(rho)|. The nontrivial-zero premises are displayed binder for binder from Mathlib's RiemannHypothesis definition. They exclude zero and one, so beta vanishes exactly when the Cayley norm is one.

## References

- Truth anchor: `D5/S3/Midline/Cayley/CayleyCriticalLineZetaCriterion.cayley_critical_line_zeta_criterion`
- Dependency: [D5/S3/Midline/Cayley/LogarithmicRadialDefect](LogarithmicRadialDefect.md)
