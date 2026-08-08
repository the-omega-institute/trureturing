# Completed Zeta and the Zero-Symmetry Foundation

## Abstract

Continuation uniqueness, an entire xi reading, and conditional zero symmetry support the O-6 route.

**Theorem 1.1 (Analytic continuations of one local germ are unique).**

$$\forall U\subseteq\mathbb{C},\ \forall f,g:\mathbb{C}\to\mathbb{C},\ \forall s_{0}\in U,\ \operatorname{AnalyticOnNhd}_{\mathbb{C}}(f,U) \land \operatorname{AnalyticOnNhd}_{\mathbb{C}}(g,U) \land \operatorname{IsPreconnected}(U) \land \operatorname{EventuallyEq}_{\operatorname{nhds}(s_{0})}(f,g) \Rightarrow \operatorname{EqOn}(f,g,U)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CompletedZeta.analytic_continuation_unique` (`✓ std3`). ∎

*Citation.* Pintoo R. Jaiswar (2021). *Identity Theorem in Complex Analysis*. DOI: [10.37398/JSR.2021.650210](https://doi.org/10.37398/JSR.2021.650210).

*Commentary.*

Two functions analytic on neighborhoods of a supplied preconnected set agree throughout that set when they agree eventually in the ambient neighborhood of one supplied point. The set and both functions are explicit inputs; the theorem constructs no continuation and proves no domain is nonempty beyond the supplied member. Compared with the ingested source atom, mathlib's identity principle replaces the explicit first-coefficient estimate, geometric-tail bound, path construction, and finite disc cover. On the O-6 path this supplies uniqueness for identifying a continued coordinate reading with the classical completed reading, but not the missing existence or identification bridge.

**Definition 1.2 (The completed reading is mathlib's classical completed zeta).**

Lean statement: `D5/S3/Zeros/CompletedZeta.completedZetaReading`

*Formalization.* `D5/S3/Zeros/CompletedZeta.completedZetaReading` (`✓ std3`).

*Citation.* Mark W. Coffey (2007). *Theta and Riemann xi function representations from harmonic oscillator eigensolutions*. DOI: [10.1016/j.physleta.2006.10.055](https://doi.org/10.1016/j.physleta.2006.10.055).

*Commentary.*

The definition is an alias for mathlib's completed Riemann zeta. It does not define the ingested subscript-K reading directly from the coordinate heat trace, and it carries no theorem equating that heat trace with the continued function. This fixes the analytic object whose functional equation can feed the zero symmetries required below O-6 while leaving the coordinate-to-completion edge explicit.

**Definition 1.3 (The xi reading totalizes the pole-removed completion).**

Lean statement: `D5/S3/Zeros/CompletedZeta.xiReading`

*Formalization.* `D5/S3/Zeros/CompletedZeta.xiReading` (`✓ std3`).

*Citation.* Mark W. Coffey (2007). *Theta and Riemann xi function representations from harmonic oscillator eigensolutions*. DOI: [10.1016/j.physleta.2006.10.055](https://doi.org/10.1016/j.physleta.2006.10.055).

*Commentary.*

The entire reading is defined through mathlib's pole-removed completed zeta, including the correction that totalizes the two exceptional endpoints. It is not introduced by multiplying the meromorphic completed reading at those endpoints. This representation makes the object globally differentiable without silently assuming cancellation of poles, an analytic foundation needed before zero reflection can support O-6.

**Theorem 1.4 (Away from the endpoints xi has the classical product form).**

$\forall s\in\mathbb{C},\ s\neq 0 \land s\neq 1 \Rightarrow \operatorname{xiReading}(s)=\frac{1}{2}s(s-1)\operatorname{completedZetaReading}(s)$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CompletedZeta.xi_reading_eq_completed_zeta` (`✓ std3`). ∎

*Citation.* Mark W. Coffey (2007). *Theta and Riemann xi function representations from harmonic oscillator eigensolutions*. DOI: [10.1016/j.physleta.2006.10.055](https://doi.org/10.1016/j.physleta.2006.10.055).

*Commentary.*

When s is neither zero nor one, the totalized xi reading equals one half times s times s minus one times the completed-zeta reading. The two exclusions are explicit and are absent from the ingested definition's displayed global notation; endpoint values are governed by the pole-removed definition instead. The theorem does not identify completed zeta with the coordinate heat trace outside its convergence half-plane.

**Theorem 1.5 (The xi reading is entire).**

$\operatorname{Differentiable}_{\mathbb{C}}(\operatorname{xiReading})$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CompletedZeta.xi_reading_differentiable` (`✓ std3`). ∎

*Citation.* Mark W. Coffey (2007). *Theta and Riemann xi function representations from harmonic oscillator eigensolutions*. DOI: [10.1016/j.physleta.2006.10.055](https://doi.org/10.1016/j.physleta.2006.10.055).

*Commentary.*

The totalized xi reading is complex differentiable at every complex input. The proof uses mathlib's differentiability theorem for the pole-removed completed zeta; it does not formalize the ingested atom's Jacobi-theta, Poisson-summation, or Mellin-transform derivation. Entirety legitimizes the global zero reading used on the O-6 dependency path but supplies no positivity.

**Theorem 1.6 (The xi reading is reflection invariant).**

$\forall s\in\mathbb{C},\ \operatorname{xiReading}(1-s)=\operatorname{xiReading}(s)$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CompletedZeta.xi_reading_reflection` (`✓ std3`). ∎

*Citation.* Mark W. Coffey (2007). *Theta and Riemann xi function representations from harmonic oscillator eigensolutions*. DOI: [10.1016/j.physleta.2006.10.055](https://doi.org/10.1016/j.physleta.2006.10.055).

*Commentary.*

For every complex s, evaluating xi at one minus s gives the same value as evaluating it at s. This is the ingested functional equation with its equality orientation reversed only syntactically. The proof delegates the analytic derivation to mathlib's completed-zeta reflection theorem; it neither rebuilds theta analysis nor states that all zeros lie on the fixed line. Reflection supplies one of the zero-orbit symmetries needed to connect completed zeta to O-6.

**Theorem 1.7 (Supplied symmetries generate a zero orbit and reverse scaling).**

$$\forall H:\mathbb{C}\to\mathbb{C},\ (\forall s,\ H(\overline{s})=\overline{H(s)}) \land (\forall s,\ H(1-s)=H(s)) \Rightarrow \forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall \rho\in\mathbb{C},\ H(\rho)=0 \Rightarrow H(\rho)=0 \land H(\overline{\rho})=0 \land H(1-\rho)=0 \land H(1-\overline{\rho})=0 \land (\forall a,\ \operatorname{scalingLedger}(\ell,1-\overline{\rho},a)=-\operatorname{scalingLedger}(\ell,\rho,a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CompletedZeta.zero_quartet_scaling_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary reading H, conjugation covariance and reflection invariance are explicit premises. From a supplied zero, Lean derives zeros at its conjugate, reflection, and conjugate reflection, then proves pointwise reversal for a supplied additive scaling ledger. The additive carrier is inhabited by its zero and the ledger length is supplied; no ZeroData value, zero enumeration, or ZeroData inhabitance is assumed or produced. Compared with the ingested theorem, real coefficients and analytic continuation are replaced by the two exact symmetry premises, while pairwise distinctness, the claim that symmetry cannot exclude off-line zeros, and the nonmultiplicative numerical instrument are omitted. This theorem gives O-6 the symmetry-controlled zero orbit whose cross-position cancellation must be distinguished from local positivity.

## References

- Truth anchor: `D5/S3/Zeros/CompletedZeta.analytic_continuation_unique`
- Truth anchor: `D5/S3/Zeros/CompletedZeta.xi_reading_eq_completed_zeta`
- Truth anchor: `D5/S3/Zeros/CompletedZeta.zero_quartet_scaling_spec`
- Truth anchor: `D5/S3/Zeros/CompletedZeta.completedZetaReading`
- Truth anchor: `D5/S3/Zeros/CompletedZeta.xi_reading_differentiable`
- Truth anchor: `D5/S3/Zeros/CompletedZeta.xi_reading_reflection`
- Truth anchor: `D5/S3/Zeros/CompletedZeta.xiReading`
- Dependency: [D5/S3/Weil/ReflectionLedger](../Weil/ReflectionLedger.md)
