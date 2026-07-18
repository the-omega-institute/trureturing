# Completed Zeta and the Zero-Symmetry Foundation

## Theorem: Analytic continuations of one local germ are unique

Provenance: `literature-attested` via `D5/L/jaiswar2021identity` (`lit/jaiswar2021identity`)

Statement: `D5/S3/Zeros/CompletedZeta.analytic_continuation_unique` `✓ std3`

Two functions analytic on neighborhoods of a supplied preconnected set agree throughout that set when they agree eventually in the ambient neighborhood of one supplied point. The set and both functions are explicit inputs; the theorem constructs no continuation and proves no domain is nonempty beyond the supplied member. Compared with the ingested source atom, mathlib's identity principle replaces the explicit first-coefficient estimate, geometric-tail bound, path construction, and finite disc cover. On the O-6 path this supplies uniqueness for identifying a continued coordinate reading with the classical completed reading, but not the missing existence or identification bridge.

## Definition: The completed reading is mathlib's classical completed zeta

Provenance: `literature-attested` via `D5/L/coffey2007theta` (`lit/coffey2007theta`)

Statement: `D5/S3/Zeros/CompletedZeta.completedZetaReading` `✓ std3`

The definition is an alias for mathlib's completed Riemann zeta. It does not define the ingested subscript-K reading directly from the coordinate heat trace, and it carries no theorem equating that heat trace with the continued function. This fixes the analytic object whose functional equation can feed the zero symmetries required below O-6 while leaving the coordinate-to-completion edge explicit.

## Definition: The xi reading totalizes the pole-removed completion

Provenance: `literature-attested` via `D5/L/coffey2007theta` (`lit/coffey2007theta`)

Statement: `D5/S3/Zeros/CompletedZeta.xiReading` `✓ std3`

The entire reading is defined through mathlib's pole-removed completed zeta, including the correction that totalizes the two exceptional endpoints. It is not introduced by multiplying the meromorphic completed reading at those endpoints. This representation makes the object globally differentiable without silently assuming cancellation of poles, an analytic foundation needed before zero reflection can support O-6.

## Theorem: Away from the endpoints xi has the classical product form

Provenance: `literature-attested` via `D5/L/coffey2007theta` (`lit/coffey2007theta`)

Statement: `D5/S3/Zeros/CompletedZeta.xi_reading_eq_completed_zeta` `✓ std3`

When s is neither zero nor one, the totalized xi reading equals one half times s times s minus one times the completed-zeta reading. The two exclusions are explicit and are absent from the ingested definition's displayed global notation; endpoint values are governed by the pole-removed definition instead. The theorem does not identify completed zeta with the coordinate heat trace outside its convergence half-plane.

## Theorem: The xi reading is entire

Provenance: `literature-attested` via `D5/L/coffey2007theta` (`lit/coffey2007theta`)

Statement: `D5/S3/Zeros/CompletedZeta.xi_reading_differentiable` `✓ std3`

The totalized xi reading is complex differentiable at every complex input. The proof uses mathlib's differentiability theorem for the pole-removed completed zeta; it does not formalize the ingested atom's Jacobi-theta, Poisson-summation, or Mellin-transform derivation. Entirety legitimizes the global zero reading used on the O-6 dependency path but supplies no positivity.

## Theorem: The xi reading is reflection invariant

Provenance: `literature-attested` via `D5/L/coffey2007theta` (`lit/coffey2007theta`)

Statement: `D5/S3/Zeros/CompletedZeta.xi_reading_reflection` `✓ std3`

For every complex s, evaluating xi at one minus s gives the same value as evaluating it at s. This is the ingested functional equation with its equality orientation reversed only syntactically. The proof delegates the analytic derivation to mathlib's completed-zeta reflection theorem; it neither rebuilds theta analysis nor states that all zeros lie on the fixed line. Reflection supplies one of the zero-orbit symmetries needed to connect completed zeta to O-6.

## Theorem: Supplied symmetries generate a zero orbit and reverse scaling

Provenance: `repo-derived`

Statement: `D5/S3/Zeros/CompletedZeta.zero_quartet_scaling_spec` `✓ std3`

For an arbitrary reading H, conjugation covariance and reflection invariance are explicit premises. From a supplied zero, Lean derives zeros at its conjugate, reflection, and conjugate reflection, then proves pointwise reversal for a supplied additive scaling ledger. The additive carrier is inhabited by its zero and the ledger length is supplied; no ZeroData value, zero enumeration, or ZeroData inhabitance is assumed or produced. Compared with the ingested theorem, real coefficients and analytic continuation are replaced by the two exact symmetry premises, while pairwise distinctness, the claim that symmetry cannot exclude off-line zeros, and the nonmultiplicative numerical instrument are omitted. This theorem gives O-6 the symmetry-controlled zero orbit whose cross-position cancellation must be distinguished from local positivity.
