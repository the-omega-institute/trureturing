/- GID: D5/S3/Weil/ZetaPntBounds/SupportRayleighMonotonicity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/SupportRayleighMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The lowest normalized Rayleigh value is antitone under support enlargement. -/

import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Support Rayleigh monotonicity

Library-search audit trail (2026-08-29):

* Exact-name and shape searches for support monotonicity, Rayleigh infima,
  `sInf` with `tsupport`, and `l2Mass` found no existing D5 owner.
* The canonical test carrier and squared mass are imported from
  `TestFunctions.WeilTestFunction` and `ArchimedeanJumpDecomposition.l2Mass`.
* Pinned Mathlib's `csInf_le_csInf` is the exact order-theoretic lemma used
  after constructing the inclusion of the two attained-value sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaPntBounds.SupportRayleighMonotonicity

open Set
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

noncomputable section

/-- If a windowed quadratic cost is unchanged on tests supported in a smaller
window, enlarging the support window cannot increase its lowest normalized
Rayleigh value. The admissible sets are constructed directly from the
canonical Weil test carrier, topological support, and squared `L2` mass. -/
theorem support_rayleigh_monotonicity
    (energy : ℝ → WeilTestFunction → ℝ)
    {L1 L2 : ℝ}
    (hScale : L1 < L2)
    (hWindowInvariant : ∀ f : WeilTestFunction,
      tsupport (f : ℝ → ℂ) ⊆ Ioo (-L1) L1 → energy L2 f = energy L1 f)
    (hLargerBounded : BddBelow
      (energy L2 '' {f : WeilTestFunction |
        tsupport (f : ℝ → ℂ) ⊆ Ioo (-L2) L2 ∧ l2Mass f = 1}))
    (hSmallerNonempty :
      (energy L1 '' {f : WeilTestFunction |
        tsupport (f : ℝ → ℂ) ⊆ Ioo (-L1) L1 ∧ l2Mass f = 1}).Nonempty) :
    sInf (energy L2 '' {f : WeilTestFunction |
        tsupport (f : ℝ → ℂ) ⊆ Ioo (-L2) L2 ∧ l2Mass f = 1}) ≤
      sInf (energy L1 '' {f : WeilTestFunction |
        tsupport (f : ℝ → ℂ) ⊆ Ioo (-L1) L1 ∧ l2Mass f = 1}) := by
  apply csInf_le_csInf hLargerBounded hSmallerNonempty
  rintro value ⟨f, ⟨hSupport, hUnit⟩, rfl⟩
  refine ⟨f, ⟨?_, hUnit⟩, hWindowInvariant f hSupport⟩
  intro x hx
  have hxSmall := hSupport hx
  exact ⟨(neg_lt_neg hScale).trans hxSmall.1, hxSmall.2.trans hScale⟩

#print axioms support_rayleigh_monotonicity

end

end D5.S3.Weil.ZetaPntBounds.SupportRayleighMonotonicity
