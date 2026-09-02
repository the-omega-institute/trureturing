/- GID: D5/S3/Fourier/CutProjectScheme
   generality: G
   mirror-B: D5/B/S3/Fourier/CutProjectScheme
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: The algebraic core of a cut-and-project scheme produces model sets functorially from internal windows. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CutProjectScheme

universe u v

/-- The algebraic core of a cut-and-project scheme.

The carrier is an additive subgroup of physical times internal space, and the
physical projection is required to be injective on that subgroup. Topological
lattice, cocompactness, and density hypotheses are deliberately left to later
specialized extensions. -/
structure Scheme (Physical : Type u) (Internal : Type v)
    [AddGroup Physical] [AddGroup Internal] where
  lattice : AddSubgroup (Physical × Internal)
  physical_injective : Function.Injective (fun point : lattice => point.1.1)

namespace Scheme

/-- Physical projection restricted to the lattice carrier. -/
def physicalProjection
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) : scheme.lattice → Physical :=
  fun point => point.1.1

/-- Internal projection restricted to the lattice carrier. -/
def internalProjection
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) : scheme.lattice → Internal :=
  fun point => point.1.2

/-- Lattice points selected by an internal-space window. -/
def selectedLattice
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) (window : Set Internal) :
    Set scheme.lattice :=
  scheme.internalProjection ⁻¹' window

/-- Physical projection of the lattice points selected by an internal window. -/
def modelSet
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) (window : Set Internal) : Set Physical :=
  scheme.physicalProjection '' scheme.selectedLattice window

/-- Membership in a model set is witnessed by one selected lattice point. -/
theorem mem_modelSet_iff
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) (window : Set Internal) (x : Physical) :
    x ∈ scheme.modelSet window ↔
      ∃ point : scheme.lattice,
        scheme.internalProjection point ∈ window ∧
          scheme.physicalProjection point = x := by
  rfl

/-- Enlarging the internal window can only enlarge the model set. -/
theorem modelSet_mono
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) {left right : Set Internal}
    (h : left ⊆ right) :
    scheme.modelSet left ⊆ scheme.modelSet right := by
  intro x hx
  rcases (scheme.mem_modelSet_iff left x).1 hx with ⟨point, hpoint, hphysical⟩
  exact (scheme.mem_modelSet_iff right x).2 ⟨point, h hpoint, hphysical⟩

/-- The empty internal window selects no physical points. -/
@[simp]
theorem modelSet_empty
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) :
    scheme.modelSet (∅ : Set Internal) = ∅ := by
  ext x
  simp [modelSet, selectedLattice]

/-- The full internal window selects the full physical projection of the lattice. -/
@[simp]
theorem modelSet_univ
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) :
    scheme.modelSet (Set.univ : Set Internal) = Set.range scheme.physicalProjection := by
  ext x
  simp [modelSet, selectedLattice]

/-- Physical injectivity makes model-set construction preserve binary window intersections. -/
theorem modelSet_inter
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) (left right : Set Internal) :
    scheme.modelSet (left ∩ right) =
      scheme.modelSet left ∩ scheme.modelSet right := by
  ext x
  constructor
  · intro hx
    rcases (scheme.mem_modelSet_iff (left ∩ right) x).1 hx with
      ⟨point, hpoint, hphysical⟩
    exact ⟨
      (scheme.mem_modelSet_iff left x).2 ⟨point, hpoint.1, hphysical⟩,
      (scheme.mem_modelSet_iff right x).2 ⟨point, hpoint.2, hphysical⟩⟩
  · rintro ⟨hxLeft, hxRight⟩
    rcases (scheme.mem_modelSet_iff left x).1 hxLeft with
      ⟨leftPoint, hLeft, hLeftPhysical⟩
    rcases (scheme.mem_modelSet_iff right x).1 hxRight with
      ⟨rightPoint, hRight, hRightPhysical⟩
    have pointsEqual : leftPoint = rightPoint :=
      scheme.physical_injective (hLeftPhysical.trans hRightPhysical.symm)
    subst rightPoint
    exact (scheme.mem_modelSet_iff (left ∩ right) x).2
      ⟨leftPoint, ⟨hLeft, hRight⟩, hLeftPhysical⟩

/-- Equal windows give equal model sets without changing the lattice carrier. -/
theorem modelSet_congr
    {Physical : Type u} {Internal : Type v}
    [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) {left right : Set Internal}
    (h : left = right) :
    scheme.modelSet left = scheme.modelSet right := by
  subst right
  rfl

#print axioms modelSet_mono
#print axioms modelSet_inter

end Scheme

end D5.S3.Fourier.CutProjectScheme
