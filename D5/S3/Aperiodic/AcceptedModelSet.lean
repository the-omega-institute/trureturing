/- GID: D5/S3/Aperiodic/AcceptedModelSet
   generality: G
   mirror-B: D5/B/S3/Aperiodic/AcceptedModelSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admissibility predicates separate language-selected model sets from unrestricted lattice-window model sets. -/

import D5.S3.Aperiodic.AlgebraicCutProjectData
import Mathlib.Tactic

/-!
# Admissibility-selected model sets

A digit language, positivity cone, automaton, or canonical numeration rule may
select only some lattice points inside a cut-and-project window.  This module
adds an explicit acceptance predicate to the generic model-set construction.
It proves monotonicity in both the window and the acceptance rule, inclusion in
the unrestricted model set, exact recovery under universal acceptance, and a
translation law under shift-invariant acceptance.

This separation is necessary for the existing golden natural-number model
set, whose canonical digit range is strictly smaller than the unrestricted
lattice-window model set.  No regularity, density, diffraction, or ergodic
claim is made here.
-/

/- Library-search audit trail (2026-09-01):
   * `AlgebraicCutProjectData` owns the unrestricted generic model set.
   * `GoldenCutAndProject` explicitly records failure of reverse inclusion for
     the unrestricted lattice because natural-number beta expansions impose an
     additional sector constraint.
   * Repository search found no reusable accepted-model-set layer separating a
     lattice window from a language or cone predicate.
   * Pinned Mathlib supplies sets and elementary predicate reasoning. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Aperiodic.AcceptedModelSet

open D5.S3.Aperiodic.AlgebraicCutProjectData

universe u v w

variable {Lattice : Type u} {Physical : Type v} {Internal : Type w}
variable [AddCommGroup Lattice] [AddCommGroup Physical] [AddCommGroup Internal]

/-- Model set selected simultaneously by an internal window and a lattice
acceptance predicate. -/
def acceptedModelSet
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) (accepted : Lattice → Prop) : Set Physical :=
  {point | ∃ latticePoint : Lattice,
    accepted latticePoint ∧
      data.physicalProjection latticePoint = point ∧
        data.internalProjection latticePoint ∈ window}

/-- Every accepted model set lies in the unrestricted model set. -/
theorem acceptedModelSet_subset_modelSet
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) (accepted : Lattice → Prop) :
    acceptedModelSet data window accepted ⊆ modelSet data window := by
  rintro point ⟨latticePoint, _, hPhysical, hInternal⟩
  exact ⟨latticePoint, hPhysical, hInternal⟩

/-- Enlarging the window enlarges an accepted model set. -/
theorem acceptedModelSet_window_mono
    (data : CutProjectData Lattice Physical Internal)
    {window₁ window₂ : Set Internal} (accepted : Lattice → Prop)
    (hWindow : window₁ ⊆ window₂) :
    acceptedModelSet data window₁ accepted ⊆
      acceptedModelSet data window₂ accepted := by
  rintro point ⟨latticePoint, hAccepted, hPhysical, hInternal⟩
  exact ⟨latticePoint, hAccepted, hPhysical, hWindow hInternal⟩

/-- Weakening the acceptance rule enlarges the accepted model set. -/
theorem acceptedModelSet_predicate_mono
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) {accepted₁ accepted₂ : Lattice → Prop}
    (hAccepted : ∀ latticePoint, accepted₁ latticePoint → accepted₂ latticePoint) :
    acceptedModelSet data window accepted₁ ⊆
      acceptedModelSet data window accepted₂ := by
  rintro point ⟨latticePoint, h₁, hPhysical, hInternal⟩
  exact ⟨latticePoint, hAccepted latticePoint h₁, hPhysical, hInternal⟩

/-- Universal acceptance recovers the unrestricted model set exactly. -/
theorem acceptedModelSet_true
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) :
    acceptedModelSet data window (fun _ => True) = modelSet data window := by
  ext point
  simp [acceptedModelSet, modelSet]

/-- Empty acceptance selects no physical points. -/
theorem acceptedModelSet_false
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) :
    acceptedModelSet data window (fun _ => False) = ∅ := by
  ext point
  simp [acceptedModelSet]

/-- Conjunction of acceptance predicates gives intersection when physical
projection is injective. -/
theorem acceptedModelSet_and_of_physical_injective
    (data : CutProjectData Lattice Physical Internal)
    (hInjective : Function.Injective data.physicalProjection)
    (window : Set Internal) (accepted₁ accepted₂ : Lattice → Prop) :
    acceptedModelSet data window
        (fun latticePoint => accepted₁ latticePoint ∧ accepted₂ latticePoint) =
      acceptedModelSet data window accepted₁ ∩
        acceptedModelSet data window accepted₂ := by
  apply Set.Subset.antisymm
  · rintro point ⟨latticePoint, ⟨h₁, h₂⟩, hPhysical, hInternal⟩
    exact ⟨⟨latticePoint, h₁, hPhysical, hInternal⟩,
      ⟨latticePoint, h₂, hPhysical, hInternal⟩⟩
  · rintro point
    rintro ⟨⟨latticePoint₁, h₁, hPhysical₁, hInternal₁⟩,
      ⟨latticePoint₂, h₂, hPhysical₂, _⟩⟩
    have hLattice : latticePoint₁ = latticePoint₂ := by
      apply hInjective
      rw [hPhysical₁, hPhysical₂]
    subst latticePoint₂
    exact ⟨latticePoint₁, ⟨h₁, h₂⟩, hPhysical₁, hInternal₁⟩

/-- A shift-invariant acceptance predicate preserves the exact lattice
translation law. -/
theorem acceptedModelSet_translate_lattice
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) (accepted : Lattice → Prop) (shift : Lattice)
    (hShift : ∀ latticePoint,
      accepted (latticePoint + shift) ↔ accepted latticePoint) :
    acceptedModelSet data
        (translateSet (data.internalProjection shift) window) accepted =
      translatePhysicalSet (data.physicalProjection shift)
        (acceptedModelSet data window accepted) := by
  ext point
  constructor
  · rintro ⟨latticePoint, hAccepted, hPhysical, hInternal⟩
    change point - data.physicalProjection shift ∈
      acceptedModelSet data window accepted
    refine ⟨latticePoint - shift, ?_, ?_, ?_⟩
    · have hBack := (hShift (latticePoint - shift)).1
      simpa using hBack hAccepted
    · simp [hPhysical]
    · simpa [translateSet] using hInternal
  · intro hPoint
    change point - data.physicalProjection shift ∈
      acceptedModelSet data window accepted at hPoint
    obtain ⟨latticePoint, hAccepted, hPhysical, hInternal⟩ := hPoint
    refine ⟨latticePoint + shift, ?_, ?_, ?_⟩
    · exact (hShift latticePoint).2 hAccepted
    · simp only [map_add]
      rw [hPhysical]
      abel
    · change
        data.internalProjection (latticePoint + shift) -
            data.internalProjection shift ∈ window
      simpa using hInternal

example :
    acceptedModelSet
      ({ physicalProjection := AddMonoidHom.id ℤ
         internalProjection := AddMonoidHom.id ℤ } :
        CutProjectData ℤ ℤ ℤ)
      ({0} : Set ℤ) (fun value => 0 ≤ value) = {0} := by
  ext point
  simp [acceptedModelSet]

#print axioms acceptedModelSet_subset_modelSet
#print axioms acceptedModelSet_window_mono
#print axioms acceptedModelSet_predicate_mono
#print axioms acceptedModelSet_true
#print axioms acceptedModelSet_and_of_physical_injective
#print axioms acceptedModelSet_translate_lattice

end D5.S3.Aperiodic.AcceptedModelSet
