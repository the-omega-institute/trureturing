/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionSupport
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized coordinates identify the 31 projective axes over F5 with a finite chart. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

abbrev F5 := ZMod 5
abbrev Vector := Fin 3 → F5

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The actual projective plane over `F₅`; finite coordinates are introduced only
through an equivalence below. -/
abbrev ProjectiveAxis := Projectivization F5 Vector

/-- The finite chart used to evaluate the concrete certificates. -/
abbrev AxisChart := Fin 31

noncomputable instance : Fintype ProjectiveAxis := Fintype.ofFinite ProjectiveAxis

noncomputable instance : DecidableEq ProjectiveAxis := Classical.decEq ProjectiveAxis

private theorem inv_f5 (x : F5) : x⁻¹ = x ^ 3 := by
  by_cases hx : x = 0
  · simp [hx]
  · apply ZMod.inv_eq_of_mul_eq_one
    calc
      x * x ^ 3 = x ^ 4 := by ring
      _ = 1 := by
        simpa using (ZMod.pow_card_sub_one_eq_one (p := 5) hx)

/-- A representative is projectively normalized by making its first nonzero
coordinate equal to one. -/
def IsNormalized (v : Vector) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

instance (v : Vector) : Decidable (IsNormalized v) := by
  unfold IsNormalized
  infer_instance

def normalizedVectors : Finset Vector :=
  Finset.univ.filter IsNormalized

/-- A canonical normalized representative of a projective direction. -/
abbrev NormalizedVector := normalizedVectors

def normalize (v : Vector) : NormalizedVector := by
  by_cases h0 : v 0 ≠ 0
  · refine ⟨fun i => v 0 ^ 3 * v i, ?_⟩
    simp only [normalizedVectors, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Or.inl
    rw [← inv_f5]
    exact inv_mul_cancel₀ h0
  by_cases h1 : v 1 ≠ 0
  · refine ⟨fun i => v 1 ^ 3 * v i, ?_⟩
    simp only [normalizedVectors, Finset.mem_filter, Finset.mem_univ, true_and]
    have hz0 : v 0 = 0 := not_ne_iff.mp h0
    apply Or.inr
    apply Or.inl
    constructor
    · simp [hz0]
    · rw [← inv_f5]
      exact inv_mul_cancel₀ h1
  by_cases h2 : v 2 ≠ 0
  · refine ⟨fun i => v 2 ^ 3 * v i, ?_⟩
    simp only [normalizedVectors, Finset.mem_filter, Finset.mem_univ, true_and]
    have hz0 : v 0 = 0 := not_ne_iff.mp h0
    have hz1 : v 1 = 0 := not_ne_iff.mp h1
    apply Or.inr
    apply Or.inr
    refine ⟨by simp [hz0], by simp [hz1], ?_⟩
    rw [← inv_f5]
    exact inv_mul_cancel₀ h2
  · refine ⟨![1, 0, 0], ?_⟩
    simp [normalizedVectors, IsNormalized]

/-- The canonical normalized vector represented by each chart index. -/
def axisVector : AxisChart → Vector :=
  ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3],
    ![0, 1, 4], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 0, 3],
    ![1, 0, 4], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3],
    ![1, 1, 4], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3],
    ![1, 2, 4], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3],
    ![1, 3, 4], ![1, 4, 0], ![1, 4, 1], ![1, 4, 2], ![1, 4, 3],
    ![1, 4, 4]]

private def axisIndex (v : Vector) : AxisChart :=
  if v 0 = 0 then
    if v 1 = 0 then
      0
    else
      ⟨(v 2).val + 1, by
        have h2 := (v 2).val_lt
        omega⟩
  else
    ⟨6 + 5 * (v 1).val + (v 2).val, by
      have h1 := (v 1).val_lt
      have h2 := (v 2).val_lt
      omega⟩

private theorem axisIndex_axisVector (p : AxisChart) :
    axisIndex (axisVector p) = p := by
  fin_cases p <;> rfl

private theorem axisVector_axisIndex (v : NormalizedVector) :
    axisVector (axisIndex v.1) = v.1 := by
  fin_cases v <;> ext i <;> fin_cases i <;> rfl

/-- The chart lists every normalized projective representative exactly once. -/
theorem axisVector_unique_complete :
    ∀ v : NormalizedVector, ∃! p : AxisChart, axisVector p = v.1 := by
  intro v
  refine ⟨axisIndex v.1, axisVector_axisIndex v, ?_⟩
  intro p hp
  calc
    p = axisIndex (axisVector p) := (axisIndex_axisVector p).symm
    _ = axisIndex v.1 := congrArg axisIndex hp

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
