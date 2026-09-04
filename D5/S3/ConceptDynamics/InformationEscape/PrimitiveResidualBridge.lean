/- GID: D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unique theorem capture is exactly the CIRPT residual of its leave-one-out and primitive kernels. -/

import D5.S3.ConceptDynamics.InformationEscape.Laws
import D5.S3.ConceptDynamics.InformationEscape.RoleHistogram

/- Library-search audit trail (2026-09-04):
   * Exact current-tree hits `kernelResidual`, `Catalog.withoutKernel`,
     `Catalog.constant_kernel_zero`, and
     `Catalog.uniqueCaptureCount_congr_kernel` are reused directly.
   * Repository searches found no existing catalog-level residual identity,
     closed-truth specialization, or certificate-erasure theorem.
   * Pinned Mathlib supplies Finset-to-Set coercion membership and
     extensionality; no parallel residual construction is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w z

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog

/-- CIRPT-IE-015: unique capture is the residual of the other theorem kernels
against the selected theorem's primitive kernel. -/
theorem uniqueCapturePairs_eq_kernelResidual
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    (catalog.uniqueCapturePairs index : Set (arena.State × arena.State)) =
      kernelResidual (catalog.withoutKernel index)
        (catalog.theoremAt index).primitives.toKernel := by
  ext pair
  change pair ∈ catalog.uniqueCapturePairs index ↔
    catalog.indistinguishable (catalog.without index) pair.1 pair.2 ∧
      ¬(catalog.theoremAt index).primitives.agrees pair.1 pair.2
  constructor
  · intro captured
    have uniqueParts := Finset.mem_filter.mp captured
    have escapeParts := Finset.mem_filter.mp uniqueParts.1
    exact ⟨escapeParts.2, uniqueParts.2⟩
  · rintro ⟨otherAgreement, selectedSeparation⟩
    have distinct : pair.1 ≠ pair.2 := by
      intro same
      apply selectedSeparation
      rw [same]
      exact (catalog.theoremAt index).primitives.agrees_equivalence.refl pair.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, otherAgreement⟩, selectedSeparation⟩
    simpa [offDiagonalPairs] using distinct

/-- CIRPT-IE-018: exact theorem gain depends only on the pointwise family of
primitive agreement kernels. -/
theorem theoremGain_depends_only_on_primitive_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ candidate left right,
      (catalog.theoremAt candidate).primitives.toKernel.relation left right ↔
        (units candidate).primitives.toKernel.relation left right)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).theoremGainRate index =
      catalog.theoremGainRate index := by
  unfold theoremGainRate
  rw [catalog.uniqueCaptureCount_congr_kernel units sameKernel index]

/-- CIRPT-IE-021: the constant closed-truth readout has the universal kernel. -/
theorem closed_truth_cut_kernel_universal (X : Type u) :
    (cutKernel (fun _ : X => true)).relation = fun _ _ => True := by
  funext left right
  simp [cutKernel]

/-- CIRPT-IE-021: a theorem unit carrying only the closed-truth kernel has no
unique object-level capture. -/
theorem closed_truth_uniqueCaptureCount_zero
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index)
    (closedTruthKernel : ∀ left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (cutKernel (fun _ : arena.State => true)).relation left right) :
    catalog.uniqueCaptureCount index = 0 := by
  apply catalog.constant_kernel_zero index
  intro left right
  exact closedTruthKernel left right |>.2 rfl

/-- CIRPT-IE-019: theorem statements and proof certificates do not affect
unique capture when every object-level primitive bundle is unchanged. -/
theorem theoremAt_proof_irrelevant
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, v} arena)
    (samePrimitives : ∀ candidate,
      (catalog.theoremAt candidate).primitives = (units candidate).primitives)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).uniqueCaptureCount index =
      catalog.uniqueCaptureCount index := by
  apply catalog.uniqueCaptureCount_congr_kernel units
  intro candidate left right
  rw [samePrimitives candidate]

end Catalog

end D5.S3.ConceptDynamics.InformationEscape
