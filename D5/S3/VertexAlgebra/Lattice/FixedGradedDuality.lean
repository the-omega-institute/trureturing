/- GID: D5/S3/VertexAlgebra/Lattice/FixedGradedDuality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedGradedDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.Properties]
   utility: none
   digest: Conditional fixed-grade nondegeneracy and the algebraic graded restricted dual.
-/

import D5.S3.VertexAlgebra.LatticeEnergyGrading
import D5.S3.VertexAlgebra.LatticeInvolution
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.DirectSum.Module

/-! Conditional fixed-grade nondegeneracy and the algebraic graded restricted dual. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators DirectSum

namespace D5.S3.VertexAlgebra.FixedGradedDuality

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeInvolution

abbrev FixedGrade (D : LatticeData) (h : ℤ) : Type :=
  ↥(Submodule.comap (fixedSpace D).subtype (grade D h))

def fixedGradeSubmodule (D : LatticeData) (h : ℤ) :
    Submodule ℂ (FixedCarrier D) := Submodule.comap (fixedSpace D).subtype (grade D h)

def fixedGradeToCarrier (D : LatticeData) (h : ℤ) :
    FixedGrade D h →ₗ[ℂ] Carrier D :=
  (fixedSpace D).subtype.comp (fixedGradeSubmodule D h).subtype

def fixedGradeForm (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (h : ℤ) : LinearMap.BilinForm ℂ (FixedGrade D h) :=
  B.comp (fixedGradeToCarrier D h) (fixedGradeToCarrier D h)

theorem fixedGradeForm_apply (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (h : ℤ) (x y : FixedGrade D h) :
    fixedGradeForm D B h x y = B (fixedGradeToCarrier D h x) (fixedGradeToCarrier D h y) := rfl

private theorem gradeProjection_zero_of_not_mem (D : LatticeData) (h : ℤ)
    (v : Carrier D) (hv : h ∉ stateEnergies D v) : gradeProjection D h v = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext a
  rw [map_zero, gradeProjection_coeff]
  by_cases ha : energy D a = h
  · have ha' : a ∉ (carrierCoeffEquiv D v).support := by
      intro has
      apply hv
      exact Finset.mem_image.mpr ⟨a, has, ha⟩
    simp [ha, Finsupp.notMem_support_iff.mp ha']
  · simp [ha]

theorem fixedGradeProjection_mem (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (h : ℤ) (v : FixedCarrier D) :
    gradeProjection D h (v : Carrier D) ∈ fixedSpace D := by
  rw [mem_fixedSpace]
  have hv : theta D (v : Carrier D) = (v : Carrier D) :=
    (mem_fixedSpace D (v : Carrier D)).mp v.property
  rw [hgrade, hv]

def fixedGradeProjection (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (h : ℤ) : FixedCarrier D →ₗ[ℂ] FixedGrade D h where
  toFun v := ⟨⟨gradeProjection D h (v : Carrier D),
    fixedGradeProjection_mem D hgrade h v⟩, gradeProjection_mem D h (v : Carrier D)⟩
  map_add' v w := by
    apply Subtype.ext
    apply Subtype.ext
    simp [map_add]
  map_smul' c v := by
    apply Subtype.ext
    apply Subtype.ext
    simp [map_smul]

@[simp] theorem fixedGradeProjection_val (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (h : ℤ) (v : FixedCarrier D) :
    fixedGradeToCarrier D h (fixedGradeProjection D hgrade h v) =
      gradeProjection D h (v : Carrier D) := rfl

theorem fixedGradeProjection_sum (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (v : FixedCarrier D) :
    ∑ h ∈ stateEnergies D (v : Carrier D),
      (fixedGradeSubmodule D h).subtype (fixedGradeProjection D hgrade h v) = v := by
  apply Subtype.ext
  simpa [fixedGradeToCarrier, fixedGradeProjection] using
    (sum_gradeProjections D (v : Carrier D))

theorem fixedGrades_independent (D : LatticeData) :
    iSupIndep (fixedGradeSubmodule D) := by
  intro h
  rw [disjoint_iff_inf_le]
  rintro v ⟨hv, ho⟩
  apply Subtype.ext
  apply (carrierCoeffEquiv D).injective
  ext a
  by_cases ha : energy D a = h
  · let f : Carrier D →ₗ[ℂ] ℂ :=
      (Finsupp.lapply a).comp (carrierCoeffEquiv D).toLinearMap
    have hle : (⨆ j ≠ h, grade D j) ≤ LinearMap.ker f := by
      apply iSup₂_le
      intro j hj
      intro w hw
      exact (mem_grade_iff D j w).mp hw a (by omega)
    have hval : (v : Carrier D) ∈ ⨆ j ≠ h, grade D j := by
      refine Submodule.iSup_induction
        (fun j : ℤ => ⨆ _ : j ≠ h, fixedGradeSubmodule D j) ho
        (motive := fun w : FixedCarrier D =>
          (w : Carrier D) ∈ ⨆ j ≠ h, grade D j) ?_ ?_ ?_
      · intro j w hw
        refine Submodule.iSup_induction (fun _ : j ≠ h => fixedGradeSubmodule D j) hw
          (motive := fun w : FixedCarrier D =>
            (w : Carrier D) ∈ ⨆ j ≠ h, grade D j) ?_ ?_ ?_
        · intro hj w hw
          have hw' : (w : Carrier D) ∈ grade D j := hw
          have inner : (w : Carrier D) ∈ ⨆ _ : j ≠ h, grade D j :=
            (le_iSup (fun _ : j ≠ h => grade D j) hj) hw'
          exact (le_iSup (fun j : ℤ => ⨆ _ : j ≠ h, grade D j) j) inner
        · exact Submodule.zero_mem _
        · intro x y hx hy
          exact Submodule.add_mem _ hx hy
      · exact Submodule.zero_mem _
      · intro x y hx hy
        exact Submodule.add_mem _ hx hy
    exact hle hval
  · exact (mem_grade_iff D h (v : Carrier D)).mp hv a ha

theorem fixedGrades_iSup (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v)) :
    (⨆ h : ℤ, fixedGradeSubmodule D h) = ⊤ := by
  apply top_unique
  intro v hv
  rw [← fixedGradeProjection_sum D hgrade v]
  apply Submodule.sum_mem
  intro h hh
  exact le_iSup (fixedGradeSubmodule D) h
    (fixedGradeProjection D hgrade h v).property

def fixedEnergyDecomposition (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v)) :
    FixedCarrier D ≃ₗ[ℂ] (⨁ h : ℤ, FixedGrade D h) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fixedGradeSubmodule D))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (fixedGrades_independent D) (fixedGrades_iSup D hgrade))).symm

theorem fixedGrade_finiteDimensional (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    FiniteDimensional ℂ (FixedGrade D h) := by
  letI : FiniteDimensional ℂ (grade D h) := grade_finiteDimensional D hD h
  let e : FixedGrade D h →ₗ[ℂ] grade D h := {
    toFun := fun x => ⟨(x : FixedCarrier D), x.property⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }
  apply FiniteDimensional.of_injective e
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : grade D h => (z : Carrier D)) hxy

private theorem plusPart_mem_fixedSpace (D : LatticeData) (v : Carrier D) :
    plusPart D v ∈ fixedSpace D := by
  rw [mem_fixedSpace]
  have hi : theta D (theta D v) = v := theta_involutive D v
  simp only [plusPart, map_smul, map_add]
  rw [hi]
  rw [add_comm]

private theorem plusPart_grade_mem (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (h : ℤ) (v : Carrier D) : plusPart D (gradeProjection D h v) ∈ grade D h := by
  have hp := gradeProjection_mem D h v
  have ht : theta D (gradeProjection D h v) ∈ grade D h := by
    rw [hgrade]
    exact gradeProjection_mem D h (theta D v)
  exact (grade D h).smul_mem _ ((grade D h).add_mem hp ht)

def fixedGradeWitness (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (h : ℤ) (v : Carrier D) : FixedGrade D h :=
  ⟨⟨plusPart D (gradeProjection D h v), plusPart_mem_fixedSpace D _⟩,
    plusPart_grade_mem D hgrade h v⟩

@[simp] theorem fixedGradeWitness_val (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (h : ℤ) (v : Carrier D) :
    fixedGradeToCarrier D h (fixedGradeWitness D hgrade h v) =
      plusPart D (gradeProjection D h v) := rfl

private theorem pairing_plusPart_right_of_fixed_left (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (x : Carrier D) (hx : x ∈ fixedSpace D) (v : Carrier D) :
    B x (plusPart D v) = B x v := by
  have hfix : theta D x = x := (mem_fixedSpace D x).mp hx
  have hright : B x (theta D v) = B x v := by
    have h := htheta x (theta D v)
    have hi : theta D (theta D v) = v := theta_involutive D v
    rw [hfix, hi] at h
    exact h.symm
  simp only [plusPart, LinearMap.BilinForm.smul_right,
    LinearMap.BilinForm.add_right]
  rw [hright]
  ring_nf

private theorem pairing_plusPart_left_of_fixed_right (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (y : Carrier D) (hy : y ∈ fixedSpace D) (v : Carrier D) :
    B (plusPart D v) y = B v y := by
  have hfix : theta D y = y := (mem_fixedSpace D y).mp hy
  have hleft : B (theta D v) y = B v y := by
    have h := htheta (theta D v) y
    have hi : theta D (theta D v) = v := theta_involutive D v
    rw [hi, hfix] at h
    exact h.symm
  simp only [plusPart, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_left]
  rw [hleft]
  ring_nf

private theorem left_grade_projection_pairing (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (h : ℤ) (x : Carrier D) (hx : x ∈ grade D h) (v : Carrier D) :
    B x (gradeProjection D h v) = B x v := by
  classical
  have hsum := sum_gradeProjections D v
  by_cases hh : h ∈ stateEnergies D v
  · calc
      B x (gradeProjection D h v) =
          ∑ j ∈ stateEnergies D v, B x (gradeProjection D j v) := by
        symm
        apply Finset.sum_eq_single h
        · intro j hj hne
          exact horth h j x (gradeProjection D j v) hx
            (gradeProjection_mem D j v) hne.symm
        · intro hn
          exact (hn hh).elim
      _ = B x v := by
        calc
          ∑ j ∈ stateEnergies D v, B x (gradeProjection D j v) =
              B x (∑ j ∈ stateEnergies D v, gradeProjection D j v) := by
                symm
                simp only [map_sum, LinearMap.BilinForm.add_right]
          _ = B x v := by rw [hsum]
  · calc
      B x (gradeProjection D h v) = 0 := by
        rw [gradeProjection_zero_of_not_mem D h v hh]
        simp
      _ = ∑ j ∈ stateEnergies D v, B x (gradeProjection D j v) := by
        symm
        apply Finset.sum_eq_zero
        intro j hj
        apply horth h j x (gradeProjection D j v) hx
          (gradeProjection_mem D j v)
        intro heq
        apply hh
        simpa [heq] using hj
      _ = B x v := by
        calc
          ∑ j ∈ stateEnergies D v, B x (gradeProjection D j v) =
              B x (∑ j ∈ stateEnergies D v, gradeProjection D j v) := by
                symm
                simp only [map_sum, LinearMap.BilinForm.add_right]
          _ = B x v := by rw [hsum]

private theorem right_grade_projection_pairing (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (h : ℤ) (y : Carrier D) (hy : y ∈ grade D h) (v : Carrier D) :
    B (gradeProjection D h v) y = B v y := by
  classical
  have hsum := sum_gradeProjections D v
  by_cases hh : h ∈ stateEnergies D v
  · calc
      B (gradeProjection D h v) y =
          ∑ j ∈ stateEnergies D v, B (gradeProjection D j v) y := by
        symm
        apply Finset.sum_eq_single h
        · intro j hj hne
          exact horth j h (gradeProjection D j v) y
            (gradeProjection_mem D j v) hy hne
        · intro hn
          exact (hn hh).elim
      _ = B v y := by
        calc
          ∑ j ∈ stateEnergies D v, B (gradeProjection D j v) y =
              B (∑ j ∈ stateEnergies D v, gradeProjection D j v) y := by
                symm
                simp only [map_sum, LinearMap.sum_apply, LinearMap.BilinForm.add_left]
          _ = B v y := by rw [hsum]
  · calc
      B (gradeProjection D h v) y = 0 := by
        rw [gradeProjection_zero_of_not_mem D h v hh]
        simp
      _ = ∑ j ∈ stateEnergies D v, B (gradeProjection D j v) y := by
        symm
        apply Finset.sum_eq_zero
        intro j hj
        apply horth j h (gradeProjection D j v) y
          (gradeProjection_mem D j v) hy
        intro heq
        apply hh
        simpa [heq] using hj
      _ = B v y := by
        calc
          ∑ j ∈ stateEnergies D v, B (gradeProjection D j v) y =
              B (∑ j ∈ stateEnergies D v, gradeProjection D j v) y := by
                symm
                simp only [map_sum, LinearMap.sum_apply, LinearMap.BilinForm.add_left]
          _ = B v y := by rw [hsum]

theorem fixedGrade_dualEquiv (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    ∃ hND : (fixedGradeForm D B h).Nondegenerate,
      Nonempty (FixedGrade D h ≃ₗ[ℂ] Module.Dual ℂ (FixedGrade D h)) := by
  letI : FiniteDimensional ℂ (FixedGrade D h) := fixedGrade_finiteDimensional D hD h
  have hleft : ∀ x : FixedGrade D h,
      (∀ y : FixedGrade D h, fixedGradeForm D B h x y = 0) → x = 0 := by
    intro x hx
    by_contra hxn
    have hdetect : ∃ y : Carrier D,
        B (fixedGradeToCarrier D h x) y ≠ 0 := by
      by_contra hn
      push_neg at hn
      have hz : fixedGradeToCarrier D h x = 0 := hB.1 _ hn
      apply hxn
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    obtain ⟨y, hy⟩ := hdetect
    let z := fixedGradeWitness D hgrade h y
    have hzy : B (fixedGradeToCarrier D h x) (fixedGradeToCarrier D h z) =
        B (fixedGradeToCarrier D h x) y := by
      rw [fixedGradeWitness_val]
      rw [pairing_plusPart_right_of_fixed_left D B htheta
        (fixedGradeToCarrier D h x) x.1.property
        (gradeProjection D h y)]
      exact left_grade_projection_pairing D B horth h
        (fixedGradeToCarrier D h x) x.property y
    have hz := hx z
    have hzero : B (fixedGradeToCarrier D h x) y = 0 := by
      rw [← hzy]
      simpa [fixedGradeForm] using hz
    exact hy hzero
  have hright : ∀ y : FixedGrade D h,
      (∀ x : FixedGrade D h, fixedGradeForm D B h x y = 0) → y = 0 := by
    intro y hy
    by_contra hyn
    have hdetect : ∃ x : Carrier D, B x (fixedGradeToCarrier D h y) ≠ 0 := by
      by_contra hn
      push_neg at hn
      have hz : fixedGradeToCarrier D h y = 0 := hB.2 _ hn
      apply hyn
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    obtain ⟨x, hx⟩ := hdetect
    let z := fixedGradeWitness D hgrade h x
    have hzx : B (fixedGradeToCarrier D h z) (fixedGradeToCarrier D h y) =
        B x (fixedGradeToCarrier D h y) := by
      rw [fixedGradeWitness_val]
      rw [pairing_plusPart_left_of_fixed_right D B htheta
        (fixedGradeToCarrier D h y) y.1.property
        (gradeProjection D h x)]
      exact right_grade_projection_pairing D B horth h
        (fixedGradeToCarrier D h y) y.property x
    have hz := hy z
    have hzero : B x (fixedGradeToCarrier D h y) = 0 := by
      rw [← hzx]
      simpa [fixedGradeForm] using hz
    exact hx hzero
  have hND : (fixedGradeForm D B h).Nondegenerate := ⟨hleft, hright⟩
  exact ⟨hND, ⟨(fixedGradeForm D B h).toDual hND⟩⟩

abbrev FixedRestrictedDual (D : LatticeData) :=
  ⨁ h : ℤ, Module.Dual ℂ (FixedGrade D h)

def fixedRestrictedDualEvaluation (D : LatticeData)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (v : FixedRestrictedDual D) : Module.Dual ℂ (FixedCarrier D) := by
  let component : ∀ h : ℤ, FixedGrade D h →ₗ[ℂ] ℂ :=
    fun h => v h
  let eval : (⨁ h : ℤ, FixedGrade D h) →ₗ[ℂ] ℂ :=
    DFinsupp.lsum ℂ component
  exact eval.comp (fixedEnergyDecomposition D hgrade).toLinearMap

theorem fixedGrade_dual_evaluation (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (h : ℤ) [FiniteDimensional ℂ (FixedGrade D h)]
    (hND : (fixedGradeForm D B h).Nondegenerate)
    (f : Module.Dual ℂ (FixedGrade D h)) (x : FixedGrade D h) :
    fixedGradeForm D B h (((fixedGradeForm D B h).toDual hND).symm f) x = f x := by
  exact LinearMap.BilinForm.apply_toDual_symm_apply f x

/-- A selected nondegeneracy proof for each fixed grade.  The choice is made only
from the explicit ambient hypotheses above; it does not assume perfection of a
restricted pairing. -/
noncomputable def fixedGradeNondegenerate (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    (fixedGradeForm D B h).Nondegenerate :=
  (fixedGrade_dualEquiv D B hB hgrade htheta horth hD h).choose

theorem fixedGradeNondegenerate_spec (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    fixedGradeNondegenerate D B hB hgrade htheta horth hD h =
      (fixedGrade_dualEquiv D B hB hgrade htheta horth hD h).choose := rfl

/-- The actual finite-grade dual equivalence supplied by the restricted pairing. -/
noncomputable def fixedGradeDualEquiv (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    FixedGrade D h ≃ₗ[ℂ] Module.Dual ℂ (FixedGrade D h) := by
  letI : FiniteDimensional ℂ (FixedGrade D h) := fixedGrade_finiteDimensional D hD h
  exact (fixedGradeForm D B h).toDual
    (fixedGradeNondegenerate D B hB hgrade htheta horth hD h)

theorem fixedGradeDualEquiv_evaluation (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ (FixedGrade D h)) (x : FixedGrade D h) :
    fixedGradeForm D B h
        ((fixedGradeDualEquiv D B hB hgrade htheta horth hD h).symm f) x = f x := by
  letI : FiniteDimensional ℂ (FixedGrade D h) := fixedGrade_finiteDimensional D hD h
  simpa [fixedGradeDualEquiv] using fixedGrade_dual_evaluation D B h
    (fixedGradeNondegenerate D B hB hgrade htheta horth hD h) f x

/-- The direct sum of the finite-grade dual equivalences, transported back to the
original fixed carrier through its internal energy decomposition. -/
noncomputable def fixedRestrictedDualEquiv (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    FixedCarrier D ≃ₗ[ℂ] FixedRestrictedDual D :=
  (fixedEnergyDecomposition D hgrade).trans
    (DirectSum.congrLinearEquiv (fun h =>
      fixedGradeDualEquiv D B hB hgrade htheta horth hD h))

end D5.S3.VertexAlgebra.FixedGradedDuality
