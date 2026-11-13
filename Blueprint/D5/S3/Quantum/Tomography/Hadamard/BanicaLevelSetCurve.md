# Curves in regular analytic level sets

## Abstract

Global analytic curves with prescribed directions in regular level sets.

**Theorem 1.1 (Bounded analytic reparametrization).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve.globalize_analytic_curve`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve.globalize_analytic_curve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An analytic curve germ through zero with derivative v and satisfying a local property extends to a global analytic curve satisfying that property everywhere, with derivative kappa v for some positive kappa. The scalar substitution r t / sqrt(1+t^2) stays in the germ's interval and has derivative r at zero.

**Theorem 1.2 (Realize every kernel direction).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve.analytic_level_set_curve`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve.analytic_level_set_curve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Phi map finite-dimensional real normed spaces, be globally real analytic, vanish at zero and have surjective derivative there. Every vector v in the derivative kernel is the tangent of a global real analytic curve in the zero level set, up to a positive scalar factor.

The implicit function is parametrized by the derivative kernel. Its derivative is the kernel inclusion. Restriction to the line spanned by v gives the required curve germ, and the bounded scalar substitution makes the curve global. The regularity constant is the analytic order omega, written as top in ContDiff, which implies smoothness of every finite order.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve.analytic_level_set_curve`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve.globalize_analytic_curve`
