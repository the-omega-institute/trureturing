/- GID: D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Postprocessing enlarges readout kernels, with equality exactly on injective realized postprocessing and strictness witnessed by a realized collision. -/

import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Image
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * Pinned Mathlib supplies `Setoid.ker`, its relation order, and `Set.range`.
   * Repository search found effective-image factorization criteria, but no
     exact postprocessing equality and strictness package on arbitrary readouts.
   * The equality criterion is intentionally stated with `Set.InjOn` on the
     realized range, rather than global injectivity on the ambient codomain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Refinement.PostprocessingKernelCalculus

universe u v w

/-- Deterministic postprocessing can only enlarge the equality kernel. -/
theorem postprocessing_kernel_le
    {X : Type u} {Y : Type v} {Z : Type w}
    (q : X -> Y) (postprocess : Y -> Z) :
    Setoid.ker q <= Setoid.ker (postprocess ∘ q) := by
  intro x y sameReadout
  exact congrArg postprocess sameReadout

/-- Postprocessing preserves exactly the original kernel iff it is injective on
values that the original readout actually realizes. -/
theorem postprocessing_kernel_eq_iff_injOn_range
    {X : Type u} {Y : Type v} {Z : Type w}
    (q : X -> Y) (postprocess : Y -> Z) :
    Setoid.ker (postprocess ∘ q) = Setoid.ker q <->
      Set.InjOn postprocess (Set.range q) := by
  constructor
  · intro kernelEquality
    intro first firstRealized second secondRealized samePostprocessed
    rcases firstRealized with ⟨x, rfl⟩
    rcases secondRealized with ⟨y, rfl⟩
    have sameAfter : Setoid.ker (postprocess ∘ q) x y := samePostprocessed
    rw [kernelEquality] at sameAfter
    exact sameAfter
  · intro injectiveOnRange
    apply le_antisymm
    · intro x y sameAfter
      exact injectiveOnRange ⟨x, rfl⟩ ⟨y, rfl⟩ sameAfter
    · exact postprocessing_kernel_le q postprocess

/-- Kernel growth is strict exactly when two realized readout values are
separated before postprocessing and collide afterwards. -/
theorem postprocessing_strict_iff_range_collision
    {X : Type u} {Y : Type v} {Z : Type w}
    (q : X -> Y) (postprocess : Y -> Z) :
    Setoid.ker q < Setoid.ker (postprocess ∘ q) <->
      exists x y, q x ≠ q y ∧ postprocess (q x) = postprocess (q y) := by
  constructor
  · intro strictGrowth
    by_contra noCollision
    push_neg at noCollision
    apply strictGrowth.2
    intro x y sameAfter
    by_contra differentBefore
    exact (noCollision x y differentBefore) sameAfter
  · rintro ⟨x, y, differentBefore, sameAfter⟩
    refine ⟨postprocessing_kernel_le q postprocess, ?_⟩
    intro reverseInclusion
    exact differentBefore (reverseInclusion sameAfter)

/-- A constant postprocessing is strictly lossy whenever the original readout
realizes two different values. -/
example :
    Setoid.ker (fun x : Bool => x) <
      Setoid.ker (fun _ : Bool => PUnit.unit) := by
  exact (postprocessing_strict_iff_range_collision
    (q := fun x : Bool => x)
    (postprocess := fun _ : Bool => PUnit.unit)).2
      ⟨false, true, Bool.false_ne_true, rfl⟩

#print axioms postprocessing_kernel_le
#print axioms postprocessing_kernel_eq_iff_injOn_range
#print axioms postprocessing_strict_iff_range_collision

end D5.S3.ObserverMemory.Refinement.PostprocessingKernelCalculus
