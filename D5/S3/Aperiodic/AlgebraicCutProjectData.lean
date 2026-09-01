/- GID: D5/S3/Aperiodic/AlgebraicCutProjectData
   generality: G
   mirror-B: D5/B/S3/Aperiodic/AlgebraicCutProjectData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Additive physical and internal projections define reusable model sets with exact window translation laws. -/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# Algebraic cut-and-project data

A finite or infinite cut-and-project construction begins with an additive
lattice carrier and two additive projections, one physical and one internal.
For an internal window `W`, its model set consists of physical projections of
lattice elements whose internal projections lie in `W`.

This module proves the algebraic laws that do not require topology: window
monotonicity, empty and union laws, exact translation by lattice elements, and
intersection preservation when the physical projection is injective.

Discreteness and cocompactness of the lattice, density of the internal image,
regular-window boundary hypotheses, diffraction, and unique ergodicity are
separate topological or analytic layers.
-/

/- Library-search audit trail (2026-09-01):
   * `GoldenCutAndProject`, `MinkowskiModelSet`, and the Tribonacci model set
     are specialized constructions.  None owns a reusable projection/window
     interface.
   * Repository search found no generic cut-and-project data structure or
     exact model-set translation theorem.
   * Pinned Mathlib supplies additive homomorphisms, sets, and elementary
     additive-group normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Aperiodic.AlgebraicCutProjectData

universe u v w

/-- Algebraic physical/internal projection data on an additive lattice
carrier. -/
structure CutProjectData
    (Lattice : Type u) (Physical : Type v) (Internal : Type w)
    [AddCommGroup Lattice] [AddCommGroup Physical] [AddCommGroup Internal] where
  physicalProjection : Lattice →+ Physical
  internalProjection : Lattice →+ Internal

variable {Lattice : Type u} {Physical : Type v} {Internal : Type w}
variable [AddCommGroup Lattice] [AddCommGroup Physical] [AddCommGroup Internal]

/-- Translate a set by requiring the shifted-back point to lie in the original
set. -/
def translateSet (shift : Internal) (window : Set Internal) : Set Internal :=
  {point | point - shift ∈ window}

/-- The same translation operation on physical space. -/
def translatePhysicalSet
    (shift : Physical) (set : Set Physical) : Set Physical :=
  {point | point - shift ∈ set}

/-- Physical projection of lattice points selected by an internal window. -/
def modelSet
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) : Set Physical :=
  {point | ∃ latticePoint : Lattice,
    data.physicalProjection latticePoint = point ∧
      data.internalProjection latticePoint ∈ window}

/-- Enlarging the internal window enlarges the model set. -/
theorem modelSet_mono
    (data : CutProjectData Lattice Physical Internal)
    {window₁ window₂ : Set Internal}
    (hWindow : window₁ ⊆ window₂) :
    modelSet data window₁ ⊆ modelSet data window₂ := by
  rintro point ⟨latticePoint, hPhysical, hInternal⟩
  exact ⟨latticePoint, hPhysical, hWindow hInternal⟩

/-- The empty window selects no physical points. -/
theorem modelSet_empty
    (data : CutProjectData Lattice Physical Internal) :
    modelSet data ∅ = ∅ := by
  ext point
  simp [modelSet]

/-- Model sets preserve arbitrary unions of windows. -/
theorem modelSet_iUnion
    (data : CutProjectData Lattice Physical Internal)
    {Index : Type*} (window : Index → Set Internal) :
    modelSet data (⋃ index, window index) =
      ⋃ index, modelSet data (window index) := by
  ext point
  constructor
  · rintro ⟨latticePoint, hPhysical, hInternal⟩
    simp only [Set.mem_iUnion] at hInternal ⊢
    obtain ⟨index, hIndex⟩ := hInternal
    exact ⟨index, latticePoint, hPhysical, hIndex⟩
  · simp only [Set.mem_iUnion]
    rintro ⟨index, latticePoint, hPhysical, hInternal⟩
    exact ⟨latticePoint, hPhysical, Set.mem_iUnion.mpr ⟨index, hInternal⟩⟩

/-- Translating the internal window by a lattice point translates the physical
model set by its physical projection. -/
theorem modelSet_translate_lattice
    (data : CutProjectData Lattice Physical Internal)
    (window : Set Internal) (shift : Lattice) :
    modelSet data
        (translateSet (data.internalProjection shift) window) =
      translatePhysicalSet (data.physicalProjection shift)
        (modelSet data window) := by
  ext point
  constructor
  · rintro ⟨latticePoint, hPhysical, hInternal⟩
    change point - data.physicalProjection shift ∈ modelSet data window
    refine ⟨latticePoint - shift, ?_, ?_⟩
    · simp [hPhysical]
    · simpa [translateSet] using hInternal
  · intro hPoint
    change point - data.physicalProjection shift ∈ modelSet data window at hPoint
    obtain ⟨latticePoint, hPhysical, hInternal⟩ := hPoint
    refine ⟨latticePoint + shift, ?_, ?_⟩
    · simp only [map_add]
      rw [hPhysical]
      abel
    · change
        data.internalProjection (latticePoint + shift) -
            data.internalProjection shift ∈ window
      simpa using hInternal

/-- A model set of an intersection always lies in the intersection of the two
model sets. -/
theorem modelSet_inter_subset
    (data : CutProjectData Lattice Physical Internal)
    (window₁ window₂ : Set Internal) :
    modelSet data (window₁ ∩ window₂) ⊆
      modelSet data window₁ ∩ modelSet data window₂ := by
  rintro point ⟨latticePoint, hPhysical, hInternal₁, hInternal₂⟩
  exact ⟨⟨latticePoint, hPhysical, hInternal₁⟩,
    ⟨latticePoint, hPhysical, hInternal₂⟩⟩

/-- An injective physical projection makes model sets preserve binary
intersections exactly. -/
theorem modelSet_inter_of_physical_injective
    (data : CutProjectData Lattice Physical Internal)
    (hInjective : Function.Injective data.physicalProjection)
    (window₁ window₂ : Set Internal) :
    modelSet data (window₁ ∩ window₂) =
      modelSet data window₁ ∩ modelSet data window₂ := by
  apply Set.Subset.antisymm
  · exact modelSet_inter_subset data window₁ window₂
  · rintro point
    rintro ⟨⟨latticePoint₁, hPhysical₁, hInternal₁⟩,
      ⟨latticePoint₂, hPhysical₂, hInternal₂⟩⟩
    have hLattice : latticePoint₁ = latticePoint₂ := by
      apply hInjective
      rw [hPhysical₁, hPhysical₂]
    subst latticePoint₂
    exact ⟨latticePoint₁, hPhysical₁, hInternal₁, hInternal₂⟩

/-- The full internal window selects exactly the range of the physical
projection. -/
theorem modelSet_univ
    (data : CutProjectData Lattice Physical Internal) :
    modelSet data Set.univ = Set.range data.physicalProjection := by
  ext point
  constructor
  · rintro ⟨latticePoint, hPhysical, _⟩
    exact ⟨latticePoint, hPhysical⟩
  · rintro ⟨latticePoint, rfl⟩
    exact ⟨latticePoint, rfl, Set.mem_univ _⟩

example :
    modelSet
      ({ physicalProjection := AddMonoidHom.id ℤ
         internalProjection := AddMonoidHom.id ℤ } :
        CutProjectData ℤ ℤ ℤ)
      ({0} : Set ℤ) = {0} := by
  ext point
  simp [modelSet]

#print axioms modelSet_mono
#print axioms modelSet_iUnion
#print axioms modelSet_translate_lattice
#print axioms modelSet_inter_of_physical_injective
#print axioms modelSet_univ

end D5.S3.Aperiodic.AlgebraicCutProjectData
