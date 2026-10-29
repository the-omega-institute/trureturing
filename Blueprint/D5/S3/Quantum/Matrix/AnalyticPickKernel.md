# Analytic matrix Pick kernels

## Abstract

Cauchy averaging proves full finite matrix-valued Caratheodory and Pick kernel positivity.

**Definition 1.1 (The full Caratheodory Gram matrix).**

Lean statement: `D5/S3/Quantum/Matrix/AnalyticPickKernel.caratheodoryGram`

*Formalization.* `D5/S3/Quantum/Matrix/AnalyticPickKernel.caratheodoryGram` (`✓ std3`).

*Citation.* William F. Donoghue Jr. (1974). *Monotone Matrix Functions and Analytic Continuation*. DOI: [10.1007/978-3-642-65755-9](https://doi.org/10.1007/978-3-642-65755-9). URL: <https://doi.org/10.1007/978-3-642-65755-9>.

*Commentary.*

For positive R, samples z_i in the radius-R disk, and a finite complex matrix function G, entry (i,a),(j,b) is entry a,b of G(z_i)+G(z_j) star divided by 1-z_i conjugate(z_j)/R squared. The indices include all sample and vector coordinates, so positivity tests arbitrary vectors assigned independently to all samples.

**Theorem 1.2 (Positivity from the actual Cauchy formula).**

Lean statement: `D5/S3/Quantum/Matrix/AnalyticPickKernel.finite_circle_caratheodory_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AnalyticPickKernel.finite_circle_caratheodory_posSemidef` (`✓ std3`). ∎

*Citation.* William F. Donoghue Jr. (1974). *Monotone Matrix Functions and Analytic Continuation*. DOI: [10.1007/978-3-642-65755-9](https://doi.org/10.1007/978-3-642-65755-9). URL: <https://doi.org/10.1007/978-3-642-65755-9>.

*Commentary.*

In every finite matrix dimension and for every finite sample set, suppose R>0, G is complex differentiable on the open radius-R disk and continuous on its closure, and G(eta)+G(eta) star is positive semidefinite on its boundary circle. Then the Caratheodory Gram matrix is positive semidefinite. Put phi_w(eta)=(1-conjugate(w) eta/R squared) inverse. Its pole is outside the closed disk. On the circle, conjugate(phi_z)=eta/(eta-z). The existing Banach-valued Cauchy average formula applied to phi_w G gives the G(z) term; taking the adjoint of the swapped identity supplies G(w) star. The complete boundary integrand factors as C star (G+G star) C, where C[a,(i,b)] is delta_ab phi_(z_i). Positivity follows by integration in the actual matrix Loewner order.

**Theorem 1.3 (The open disk without boundary regularity).**

Lean statement: `D5/S3/Quantum/Matrix/AnalyticPickKernel.open_disk_caratheodory_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AnalyticPickKernel.open_disk_caratheodory_posSemidef` (`✓ std3`). ∎

*Citation.* William F. Donoghue Jr. (1974). *Monotone Matrix Functions and Analytic Continuation*. DOI: [10.1007/978-3-642-65755-9](https://doi.org/10.1007/978-3-642-65755-9). URL: <https://doi.org/10.1007/978-3-642-65755-9>.

*Commentary.*

If G is complex differentiable on the open unit disk and G+G star is positive semidefinite there, every finite Caratheodory Gram matrix at R=1 is positive semidefinite. Restrict first to smaller closed disks containing the samples, then let their radii increase to one. Denominators stay nonzero, and the finite matrix positive cone is closed. No values or regularity on the unit circle are assumed.

**Definition 1.4 (Hermitian imaginary part).**

Lean statement: `D5/S3/Quantum/Matrix/AnalyticPickKernel.imaginaryPart`

*Formalization.* `D5/S3/Quantum/Matrix/AnalyticPickKernel.imaginaryPart` (`✓ std3`).

*Citation.* William F. Donoghue Jr. (1974). *Monotone Matrix Functions and Analytic Continuation*. DOI: [10.1007/978-3-642-65755-9](https://doi.org/10.1007/978-3-642-65755-9). URL: <https://doi.org/10.1007/978-3-642-65755-9>.

*Commentary.*

The imaginary part of A is (-i/2)(A-A star).

**Definition 1.5 (The finite Pick block matrix).**

Lean statement: `D5/S3/Quantum/Matrix/AnalyticPickKernel.pickGram`

*Formalization.* `D5/S3/Quantum/Matrix/AnalyticPickKernel.pickGram` (`✓ std3`).

*Citation.* William F. Donoghue Jr. (1974). *Monotone Matrix Functions and Analytic Continuation*. DOI: [10.1007/978-3-642-65755-9](https://doi.org/10.1007/978-3-642-65755-9). URL: <https://doi.org/10.1007/978-3-642-65755-9>.

*Commentary.*

Entry (i,a),(j,b) is entry a,b of T(z_i)-T(z_j) star divided by z_i-conjugate(z_j). On the upper half-plane all denominators are nonzero.

**Theorem 1.6 (Global analytic Pick positivity).**

Lean statement: `D5/S3/Quantum/Matrix/AnalyticPickKernel.upper_half_plane_pick_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AnalyticPickKernel.upper_half_plane_pick_posSemidef` (`✓ std3`). ∎

*Citation.* William F. Donoghue Jr. (1974). *Monotone Matrix Functions and Analytic Continuation*. DOI: [10.1007/978-3-642-65755-9](https://doi.org/10.1007/978-3-642-65755-9). URL: <https://doi.org/10.1007/978-3-642-65755-9>.

*Commentary.*

For every finite complex matrix dimension, every holomorphic T on the upper half-plane with pointwise nonnegative Hermitian imaginary part, and every finite family of points there, the full Pick block matrix is positive semidefinite. Set psi(u)=i(1+u)/(1-u) and G(u)=-i T(psi(u)). The disk theorem applies because G+G star is twice the imaginary part of T. The exact domain Cayley identity gives K=(1/2) C L C star, with C diagonal and C_(i,a)=1-u_i. The inverse coordinate is u_i=(z_i-i)/(z_i+i). No positive kernel, Herglotz measure or Taylor coefficients occur as premises.

These are classical Caratheodory, Pick and Loewner arguments, implemented through Mathlib's circleAverage_smul_div and closed matrix positivity cone; see Donoghue, Monotone Matrix Functions and Analytic Continuation, DOI 10.1007/978-3-642-65755-9, and Agler–McCarthy, DOI 10.1090/gsm/044. No mathematical novelty is claimed. The real boundary Hankel consequence uses additional local analytic and Hermitian real-axis hypotheses. Applying it to actual principal matrix powers still requires the global analytic and sector supplier bridge. Full independent X,Y He–Saunderson–Fawzi compatibility remains open.

The three typed dependent-family Reg attempts compile, but their source-selection bindings remain unfinished (IE-C050, source.selection_missing). See https://github.com/the-omega-institute/trureturing/issues/23333. Registration acceptance is not claimed.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AnalyticPickKernel.caratheodoryGram`
- Truth anchor: `D5/S3/Quantum/Matrix/AnalyticPickKernel.finite_circle_caratheodory_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/AnalyticPickKernel.imaginaryPart`
- Truth anchor: `D5/S3/Quantum/Matrix/AnalyticPickKernel.open_disk_caratheodory_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/AnalyticPickKernel.pickGram`
- Truth anchor: `D5/S3/Quantum/Matrix/AnalyticPickKernel.upper_half_plane_pick_posSemidef`
- Dependency: [D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion](../../Analytic/Characterizations/ShiftedHerglotzCriterion.md)
