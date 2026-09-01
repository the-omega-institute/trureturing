/- GID: D5/S3/Aperiodic/AcceptedModelSet
   generality: G
   mirror-B: D5/B/S3/Aperiodic/AcceptedModelSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Model sets with an additional admissibility predicate separate geometric windows from language or cone constraints. -/

import D5.S3.Aperiodic.AlgebraicCutProjectData
import Mathlib.Tactic

/-!
# Accepted model sets

A window-selected lattice model set can be refined by an independent
admissibility predicate on lattice witnesses. This separates geometric
cut-and-project selection from digit-language, positivity-cone, parity, or
other symbolic constraints. The accepted model set is contained in the full
model set, is monotone in both the window and acceptance predicate, and agrees
with the full model set when every lattice point is accepted.

For additive cut-and-project data, a translation-invariant acceptance
predicate preserves the model-set translation law. No claim is made that a
particular symbolic language equals a full regular model set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Aperiodic.AcceptedModelSet

open D5.S3.Aperiodic.AlgebraicCutProjectData

universe u v w

variable {Ambient : Type u} {Physical : Type v} {Internal : Type w}

/-- Cut-and-project model set with an additional predicate on lattice
witnesses. -/
def acceptedModelSet
    (data : CutProjectData Ambient Physical Internal)
    (window : Set Internal) (accept : Ambient → Prop) : Set Physical :=
  {point | ∃ latticePoint,
    latticePoint ∈ data.lattice ∧
      accept latticePoint ∧
      data.physicalProjection latticePoint = point ∧
      data.internalProjection latticePoint ∈ window}

/-- Every accepted model-set point belongs to the underlying geometric model
set. -/
theorem acceptedModelSet_subset_modelSet
    (data : CutProjectData Ambient Physical Internal)
    (window : Set Internal) (accept : Ambient → Prop) :
    acceptedModelSet data window accept ⊆ data.modelSet window := by
  rintro point ⟨latticePoint, hLattice, _hAccept, hPhysical, hInternal⟩
  exact ⟨latticePoint, hLattice, hPhysical, hInternal⟩

/-- Enlarging the window enlarges the accepted model set. -/
theorem acceptedModelSet_window_mono
    (data : CutProjectData Ambient Physical Internal)
    {firstWindow secondWindow : Set Internal}
    (accept : Ambient → Prop)
    (hWindow : firstWindow ⊆ secondWindow) :
    acceptedModelSet data firstWindow accept ⊆
      acceptedModelSet data secondWindow accept := by
  rintro point ⟨latticePoint, hLattice, hAccept, hPhysical, hInternal⟩
  exact ⟨latticePoint, hLattice, hAccept, hPhysical,
    hWindow hInternal⟩

/-- Weakening the acceptance predicate enlarges the selected set. -/
theorem acceptedModelSet_accept_mono
    (data : CutProjectData Ambient Physical Internal)
    (window : Set Internal)
    {firstAccept secondAccept : Ambient → Prop}
    (hAccept : ∀ point, firstAccept point → secondAccept point) :
    acceptedModelSet data window firstAccept ⊆
      acceptedModelSet data window secondAccept := by
  rintro point ⟨latticePoint, hLattice, hFirst, hPhysical, hInternal⟩
  exact ⟨latticePoint, hLattice, hAccept latticePoint hFirst,
    hPhysical, hInternal⟩

/-- Universal acceptance recovers the full model set. -/
theorem acceptedModelSet_true
    (data : CutProjectData Ambient Physical Internal)
    (window : Set Internal) :
    acceptedModelSet data window (fun _ => True) =
      data.modelSet window := by
  ext point
  constructor
  · exact acceptedModelSet_subset_modelSet data window _
  · rintro ⟨latticePoint, hLattice, hPhysical, hInternal⟩
    exact ⟨latticePoint, hLattice, trivial, hPhysical, hInternal⟩

/-- Impossible acceptance selects no points. -/
@[simp]
theorem acceptedModelSet_false
    (data : CutProjectData Ambient Physical Internal)
    (window : Set Internal) :
    acceptedModelSet data window (fun _ => False) = ∅ := by
  ext point
  simp [acceptedModelSet]

section Additive

variable {Gamma : Type u} {G : Type v} {H : Type w}
variable [AddCommGroup Gamma] [AddCommGroup G] [AddCommGroup H]

/-- Accepted model set for additive cut-and-project data. -/
def additiveAcceptedModelSet
    (data : AdditiveCutProjectData Gamma G H)
    (window : Set H) (accept : Gamma → Prop) : Set G :=
  acceptedModelSet data.toCutProjectData window accept

/-- If admissibility is invariant under translation by a selected lattice
shift, accepted model sets retain the cut-and-project translation law. -/
theorem additiveAcceptedModelSet_translate
    (data : AdditiveCutProjectData Gamma G H)
    (window : Set H) (accept : Gamma → Prop)
    {shift : Gamma} (hShift : shift ∈ data.lattice)
    (hAccept : ∀ latticePoint,
      accept (latticePoint + shift) ↔ accept latticePoint) :
    additiveAcceptedModelSet data
        (AdditiveCutProjectData.translateSet
          (data.internalProjection shift) window)
        accept =
      AdditiveCutProjectData.translateSet
        (data.physicalProjection shift)
        (additiveAcceptedModelSet data window accept) := by
  ext point
  constructor
  · rintro ⟨latticePoint, hLattice, hAccepted, hPhysical, hInternal⟩
    refine ⟨latticePoint - shift,
      data.lattice.sub_mem hLattice hShift, ?_, ?_, ?_⟩
    · have hBack := hAccept (latticePoint - shift)
      have hSum : latticePoint - shift + shift = latticePoint := by abel
      rw [hSum] at hBack
      exact hBack.mp hAccepted
    · change data.physicalProjection (latticePoint - shift) =
        point - data.physicalProjection shift
      rw [map_sub, hPhysical]
    · change data.internalProjection latticePoint -
        data.internalProjection shift ∈ window at hInternal
      simpa [map_sub] using hInternal
  · rintro ⟨latticePoint, hLattice, hAccepted, hPhysical, hInternal⟩
    refine ⟨latticePoint + shift,
      data.lattice.add_mem hLattice hShift, ?_, ?_, ?_⟩
    · exact (hAccept latticePoint).mpr hAccepted
    · change data.physicalProjection (latticePoint + shift) = point
      rw [map_add, hPhysical]
      simp
    · change data.internalProjection (latticePoint + shift) -
        data.internalProjection shift ∈ window
      simpa [map_add] using hInternal

end Additive

example :
    acceptedModelSet
        (CutProjectData.mk (Set.univ : Set ℤ) id id)
        ({0} : Set ℤ) (fun value => 0 ≤ value) = {0} := by
  ext point
  simp [acceptedModelSet]

#print axioms acceptedModelSet_subset_modelSet
#print axioms acceptedModelSet_window_mono
#print axioms acceptedModelSet_accept_mono
#print axioms acceptedModelSet_true
#print axioms additiveAcceptedModelSet_translate

end D5.S3.Aperiodic.AcceptedModelSet
