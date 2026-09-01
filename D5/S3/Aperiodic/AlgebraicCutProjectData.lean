/- GID: D5/S3/Aperiodic/AlgebraicCutProjectData
   generality: G
   mirror-B: D5/B/S3/Aperiodic/AlgebraicCutProjectData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cut-and-project data select physical points by an internal window and obey exact window and translation laws. -/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# Algebraic cut-and-project data

A cut-and-project datum consists of an ambient carrier, a selected lattice,
and physical and internal projections. Its model set contains the physical
projections of lattice points whose internal projections lie in a window.
The set-level layer proves monotonicity, unions, the empty-window law, and
uniqueness of lattice witnesses under physical injectivity.

An additive specialization uses an additive subgroup and additive projection
homomorphisms. Its model sets are equivariant under simultaneous physical and
internal translations by lattice points. No local compactness, cocompactness,
density of the internal projection, regular-window boundary theorem, or
diffraction theorem is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Aperiodic.AlgebraicCutProjectData

universe u v w

/-- Set-level cut-and-project data. -/
structure CutProjectData
    (Ambient : Type u) (Physical : Type v) (Internal : Type w) where
  lattice : Set Ambient
  physicalProjection : Ambient → Physical
  internalProjection : Ambient → Internal

namespace CutProjectData

variable {Ambient : Type u} {Physical : Type v} {Internal : Type w}

/-- The model set selected by an internal window. -/
def modelSet
    (data : CutProjectData Ambient Physical Internal)
    (window : Set Internal) : Set Physical :=
  {point | ∃ latticePoint,
    latticePoint ∈ data.lattice ∧
      data.physicalProjection latticePoint = point ∧
      data.internalProjection latticePoint ∈ window}

/-- Physical projection is injective on the selected lattice. -/
def HasInjectivePhysicalProjection
    (data : CutProjectData Ambient Physical Internal) : Prop :=
  Set.InjOn data.physicalProjection data.lattice

/-- Membership is exactly the existence of a selected lattice witness. -/
theorem mem_modelSet_iff
    (data : CutProjectData Ambient Physical Internal)
    (window : Set Internal) (point : Physical) :
    point ∈ data.modelSet window ↔
      ∃ latticePoint,
        latticePoint ∈ data.lattice ∧
          data.physicalProjection latticePoint = point ∧
          data.internalProjection latticePoint ∈ window := by
  rfl

/-- Enlarging the internal window enlarges the model set. -/
theorem modelSet_mono
    (data : CutProjectData Ambient Physical Internal)
    {firstWindow secondWindow : Set Internal}
    (hWindow : firstWindow ⊆ secondWindow) :
    data.modelSet firstWindow ⊆ data.modelSet secondWindow := by
  rintro point ⟨latticePoint, hLattice, hPhysical, hInternal⟩
  exact ⟨latticePoint, hLattice, hPhysical, hWindow hInternal⟩

/-- The empty internal window selects no physical point. -/
@[simp]
theorem modelSet_empty
    (data : CutProjectData Ambient Physical Internal) :
    data.modelSet (∅ : Set Internal) = ∅ := by
  ext point
  simp [modelSet]

/-- A union of windows selects the union of the corresponding model sets. -/
theorem modelSet_union
    (data : CutProjectData Ambient Physical Internal)
    (firstWindow secondWindow : Set Internal) :
    data.modelSet (firstWindow ∪ secondWindow) =
      data.modelSet firstWindow ∪ data.modelSet secondWindow := by
  ext point
  constructor
  · rintro ⟨latticePoint, hLattice, hPhysical, hInternal⟩
    rcases hInternal with hFirst | hSecond
    · exact Or.inl ⟨latticePoint, hLattice, hPhysical, hFirst⟩
    · exact Or.inr ⟨latticePoint, hLattice, hPhysical, hSecond⟩
  · rintro (hFirst | hSecond)
    · rcases hFirst with ⟨latticePoint, hLattice, hPhysical, hInternal⟩
      exact ⟨latticePoint, hLattice, hPhysical, Or.inl hInternal⟩
    · rcases hSecond with ⟨latticePoint, hLattice, hPhysical, hInternal⟩
      exact ⟨latticePoint, hLattice, hPhysical, Or.inr hInternal⟩

/-- The universal window gives the physical image of the entire lattice. -/
theorem modelSet_univ
    (data : CutProjectData Ambient Physical Internal) :
    data.modelSet Set.univ = data.physicalProjection '' data.lattice := by
  ext point
  constructor
  · rintro ⟨latticePoint, hLattice, hPhysical, _⟩
    exact ⟨latticePoint, hLattice, hPhysical⟩
  · rintro ⟨latticePoint, hLattice, hPhysical⟩
    exact ⟨latticePoint, hLattice, hPhysical, Set.mem_univ _⟩

/-- Under physical injectivity, a physical model-set point has a unique
lattice witness, even when several window descriptions are available. -/
theorem latticeWitness_unique
    (data : CutProjectData Ambient Physical Internal)
    (hInjective : data.HasInjectivePhysicalProjection)
    {window : Set Internal} {point : Physical}
    {first second : Ambient}
    (hFirst : first ∈ data.lattice)
    (hSecond : second ∈ data.lattice)
    (hFirstPhysical : data.physicalProjection first = point)
    (hSecondPhysical : data.physicalProjection second = point) :
    first = second := by
  exact hInjective hFirst hSecond
    (hFirstPhysical.trans hSecondPhysical.symm)

end CutProjectData

section Additive

variable (Gamma : Type u) (Physical : Type v) (Internal : Type w)
variable [AddCommGroup Gamma] [AddCommGroup Physical] [AddCommGroup Internal]

/-- Additive cut-and-project data with a subgroup lattice and additive
physical and internal projections. -/
structure AdditiveCutProjectData where
  lattice : AddSubgroup Gamma
  physicalProjection : Gamma →+ Physical
  internalProjection : Gamma →+ Internal

namespace AdditiveCutProjectData

variable {Gamma : Type u} {Physical : Type v} {Internal : Type w}
variable [AddCommGroup Gamma] [AddCommGroup Physical] [AddCommGroup Internal]

/-- Forget additive structure and retain the set-level cut-and-project datum. -/
def toCutProjectData
    (data : AdditiveCutProjectData Gamma Physical Internal) :
    CutProjectData Gamma Physical Internal where
  lattice := data.lattice
  physicalProjection := data.physicalProjection
  internalProjection := data.internalProjection

/-- Model set of additive cut-and-project data. -/
def modelSet
    (data : AdditiveCutProjectData Gamma Physical Internal)
    (window : Set Internal) : Set Physical :=
  data.toCutProjectData.modelSet window

/-- Additive translation of a subset. -/
def translateSet {A : Type*} [AddGroup A] (shift : A) (set : Set A) : Set A :=
  {point | point - shift ∈ set}

@[simp]
theorem mem_translateSet_iff
    {A : Type*} [AddGroup A] (shift point : A) (set : Set A) :
    point ∈ translateSet shift set ↔ point - shift ∈ set := by
  rfl

/-- Simultaneous internal and physical translation by a lattice point leaves
the cut-and-project selection law equivariant. -/
theorem modelSet_translate
    (data : AdditiveCutProjectData Gamma Physical Internal)
    (window : Set Internal) {shift : Gamma}
    (hShift : shift ∈ data.lattice) :
    data.modelSet
        (translateSet (data.internalProjection shift) window) =
      translateSet (data.physicalProjection shift)
        (data.modelSet window) := by
  ext point
  constructor
  · rintro ⟨latticePoint, hLattice, hPhysical, hInternal⟩
    refine ⟨latticePoint - shift, data.lattice.sub_mem hLattice hShift, ?_, ?_⟩
    · change data.physicalProjection (latticePoint - shift) =
        point - data.physicalProjection shift
      rw [map_sub, hPhysical]
    · change data.internalProjection latticePoint -
        data.internalProjection shift ∈ window at hInternal
      simpa [map_sub] using hInternal
  · rintro ⟨latticePoint, hLattice, hPhysical, hInternal⟩
    refine ⟨latticePoint + shift, data.lattice.add_mem hLattice hShift, ?_, ?_⟩
    · change data.physicalProjection (latticePoint + shift) = point
      rw [map_add, hPhysical]
      simp
    · change data.internalProjection (latticePoint + shift) -
        data.internalProjection shift ∈ window
      simpa [map_add] using hInternal

end AdditiveCutProjectData

end Additive

example :
    (CutProjectData.mk (Set.univ : Set ℤ) id id).modelSet
      ({0} : Set ℤ) = {0} := by
  ext point
  simp [CutProjectData.modelSet]

#print axioms CutProjectData.modelSet_mono
#print axioms CutProjectData.modelSet_union
#print axioms CutProjectData.latticeWitness_unique
#print axioms AdditiveCutProjectData.modelSet_translate

end D5.S3.Aperiodic.AlgebraicCutProjectData
