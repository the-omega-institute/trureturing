/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaGradeIntertwiner
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dimension.Constructions]
   utility: none
   digest: Theta-equivariant maps between two finite energy grades are exactly the two diagonal sign blocks. -/

import D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeTraceSplit
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeIntertwiner

open D5.S3.VertexAlgebra.SourceBPZ
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open ThetaReflectionAction
open ThetaGradeTraceSplit

def plusIn (D : LatticeData) (n : ℤ) :
    plusGrade D n →ₗ[ℂ] grade D n where
  toFun := fun x => ⟨x.1, x.2.1⟩
  map_add' := by intro x y; apply Subtype.ext; rfl
  map_smul' := by intro c x; apply Subtype.ext; rfl

def minusIn (D : LatticeData) (n : ℤ) :
    minusGrade D n →ₗ[ℂ] grade D n where
  toFun := fun x => ⟨x.1, x.2.1⟩
  map_add' := by intro x y; apply Subtype.ext; rfl
  map_smul' := by intro c x; apply Subtype.ext; rfl

def gradeIn (D : LatticeData) (n : ℤ) :
    grade D n →ₗ[ℂ] Carrier D where
  toFun := fun x => x.1
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

def thetaIntertwiner (D : LatticeData) (m n : ℤ) :
    Submodule ℂ (grade D m →ₗ[ℂ] grade D n) where
  carrier := {F | (gradeTheta D n).comp F = F.comp (gradeTheta D m)}
  zero_mem' := by
    apply LinearMap.ext
    intro x
    simp
  add_mem' := by
    intro F G hF hG
    change (gradeTheta D n).comp (F + G) = (F + G).comp (gradeTheta D m)
    change (gradeTheta D n).comp F = F.comp (gradeTheta D m) at hF
    change (gradeTheta D n).comp G = G.comp (gradeTheta D m) at hG
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, map_add] using
      congrArg₂ (fun a b => a + b)
        (congrArg (fun k : grade D m →ₗ[ℂ] grade D n => k x) hF)
        (congrArg (fun k : grade D m →ₗ[ℂ] grade D n => k x) hG)
  smul_mem' := by
    intro c F hF
    change (gradeTheta D n).comp (c • F) = (c • F).comp (gradeTheta D m)
    change (gradeTheta D n).comp F = F.comp (gradeTheta D m) at hF
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun k : grade D m →ₗ[ℂ] grade D n => k x) hF
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul] using
      congrArg (fun z : grade D n => c • z) hx

private theorem plusIn_theta (D : LatticeData) (n : ℤ) (x : plusGrade D n) :
    gradeTheta D n (plusIn D n x) = plusIn D n x := by
  apply Subtype.ext
  change theta D x.1 = x.1
  exact (mem_fixedSpace D x.1).mp x.2.2

private theorem minusIn_theta (D : LatticeData) (n : ℤ) (x : minusGrade D n) :
    gradeTheta D n (minusIn D n x) = -minusIn D n x := by
  apply Subtype.ext
  simpa [gradeTheta, minusIn, theta] using
    (mem_eigenspace D (-1) x.1).mp x.2.2

private theorem plusGradeMap_theta (D : LatticeData) (n : ℤ) (x : grade D n) :
    plusGradeMap D n (gradeTheta D n x) = plusGradeMap D n x := by
  apply Subtype.ext
  change plusPart D (theta D x.1) = plusPart D x.1
  simp only [plusPart, map_add]
  have hi : theta D (theta D x.1) = x.1 := theta_involutive D x.1
  rw [hi, add_comm]

private theorem minusGradeMap_theta (D : LatticeData) (n : ℤ) (x : grade D n) :
    minusGradeMap D n (gradeTheta D n x) = -minusGradeMap D n x := by
  apply Subtype.ext
  change minusPart D (theta D x.1) = -minusPart D x.1
  simp only [minusPart, map_sub]
  have hi : theta D (theta D x.1) = x.1 := theta_involutive D x.1
  rw [hi]
  module

private theorem plusIn_plusGradeMap_fixed (D : LatticeData) (n : ℤ)
    (x : grade D n) (hx : x.1 ∈ fixedSpace D) :
    plusIn D n (plusGradeMap D n x) = x := by
  apply Subtype.ext
  change plusPart D x.1 = x.1
  rw [plusPart, (mem_fixedSpace D x.1).mp hx, ← two_smul ℂ x.1,
    smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

private theorem minusIn_minusGradeMap_anti (D : LatticeData) (n : ℤ)
    (x : grade D n) (hx : x.1 ∈ minusSpace D) :
    minusIn D n (minusGradeMap D n x) = x := by
  apply Subtype.ext
  change minusPart D x.1 = x.1
  have he : theta D x.1 = (-1 : ℂ) • x.1 :=
    (mem_eigenspace D (-1) x.1).mp hx
  rw [minusPart, he]
  module

private theorem intertwiner_plus_mem (D : LatticeData) (m n : ℤ)
    (F : thetaIntertwiner D m n) (x : plusGrade D m) :
    (F.1 (plusIn D m x)).1 ∈ fixedSpace D := by
  have h := congrArg
    (fun k : grade D m →ₗ[ℂ] grade D n => k (plusIn D m x)) F.2
  change gradeTheta D n (F.1 (plusIn D m x)) =
    F.1 (gradeTheta D m (plusIn D m x)) at h
  rw [plusIn_theta] at h
  apply (mem_fixedSpace D _).mpr
  have hv := congrArg (fun z : grade D n => z.1) h
  simpa only [gradeTheta_val] using hv

private theorem intertwiner_minus_mem (D : LatticeData) (m n : ℤ)
    (F : thetaIntertwiner D m n) (x : minusGrade D m) :
    (F.1 (minusIn D m x)).1 ∈ minusSpace D := by
  have h := congrArg
    (fun k : grade D m →ₗ[ℂ] grade D n => k (minusIn D m x)) F.2
  change gradeTheta D n (F.1 (minusIn D m x)) =
    F.1 (gradeTheta D m (minusIn D m x)) at h
  rw [minusIn_theta] at h
  apply (mem_eigenspace D (-1) _).mpr
  have hv := congrArg (fun z : grade D n => z.1) h
  change theta D (F.1 (minusIn D m x)).1 =
    (F.1 (-minusIn D m x)).1 at hv
  rw [map_neg] at hv
  change theta D (F.1 (minusIn D m x)).1 =
    -(F.1 (minusIn D m x)).1 at hv
  simpa only [neg_one_smul] using hv

private theorem intertwiner_plus_grade_mem (D : LatticeData) (m n : ℤ)
    (F : thetaIntertwiner D m n) (x : plusGrade D m) :
    (F.1 (plusIn D m x)).1 ∈ plusGrade D n :=
  ⟨(F.1 (plusIn D m x)).property, intertwiner_plus_mem D m n F x⟩

private theorem intertwiner_minus_grade_mem (D : LatticeData) (m n : ℤ)
    (F : thetaIntertwiner D m n) (x : minusGrade D m) :
    (F.1 (minusIn D m x)).1 ∈ minusGrade D n :=
  ⟨(F.1 (minusIn D m x)).property, intertwiner_minus_mem D m n F x⟩

set_option backward.isDefEq.respectTransparency true in
def plusBlock (D : LatticeData) (m n : ℤ) :
    thetaIntertwiner D m n →ₗ[ℂ]
      (plusGrade D m →ₗ[ℂ] plusGrade D n) where
  toFun F :=
    let hmem : ∀ x : plusGrade D m,
        (F.1 (plusIn D m x)).1 ∈ plusGrade D n :=
      intertwiner_plus_grade_mem D m n F
    ((gradeIn D n).comp (F.1.comp (plusIn D m))).codRestrict (plusGrade D n)
      hmem
  map_add' F G := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_smul' c F := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

set_option backward.isDefEq.respectTransparency true in
def minusBlock (D : LatticeData) (m n : ℤ) :
    thetaIntertwiner D m n →ₗ[ℂ]
      (minusGrade D m →ₗ[ℂ] minusGrade D n) where
  toFun F :=
    let hmem : ∀ x : minusGrade D m,
        (F.1 (minusIn D m x)).1 ∈ minusGrade D n :=
      intertwiner_minus_grade_mem D m n F
    ((gradeIn D n).comp (F.1.comp (minusIn D m))).codRestrict (minusGrade D n)
      hmem
  map_add' F G := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_smul' c F := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

def thetaIntertwinerToBlocks (D : LatticeData) (m n : ℤ) :
    thetaIntertwiner D m n →ₗ[ℂ]
      (plusGrade D m →ₗ[ℂ] plusGrade D n) ×
        (minusGrade D m →ₗ[ℂ] minusGrade D n) :=
  (plusBlock D m n).prod (minusBlock D m n)

private theorem plusGradeMap_plusIn (D : LatticeData) (n : ℤ) (x : plusGrade D n) :
    plusGradeMap D n (plusIn D n x) = x := by
  apply Subtype.ext
  change plusPart D x.1 = x.1
  rw [plusPart, (mem_fixedSpace D x.1).mp x.2.2, ← two_smul ℂ x.1,
    smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

private theorem minusGradeMap_plusIn (D : LatticeData) (n : ℤ) (x : plusGrade D n) :
    minusGradeMap D n (plusIn D n x) = 0 := by
  apply Subtype.ext
  change minusPart D x.1 = 0
  rw [minusPart, (mem_fixedSpace D x.1).mp x.2.2, sub_self, smul_zero]

private theorem plusGradeMap_minusIn (D : LatticeData) (n : ℤ) (x : minusGrade D n) :
    plusGradeMap D n (minusIn D n x) = 0 := by
  apply Subtype.ext
  change plusPart D x.1 = 0
  have he : theta D x.1 = (-1 : ℂ) • x.1 :=
    (mem_eigenspace D (-1) x.1).mp x.2.2
  rw [plusPart, he, smul_add]
  simp

private theorem minusGradeMap_minusIn (D : LatticeData) (n : ℤ) (x : minusGrade D n) :
    minusGradeMap D n (minusIn D n x) = x := by
  apply Subtype.ext
  change minusPart D x.1 = x.1
  have he : theta D x.1 = (-1 : ℂ) • x.1 :=
    (mem_eigenspace D (-1) x.1).mp x.2.2
  rw [minusPart, he]
  module

def blockMap (D : LatticeData) (m n : ℤ) :
    ((plusGrade D m →ₗ[ℂ] plusGrade D n) ×
      (minusGrade D m →ₗ[ℂ] minusGrade D n)) →ₗ[ℂ]
        (grade D m →ₗ[ℂ] grade D n) where
  toFun p :=
    { toFun := fun x =>
        plusIn D n (p.1 (plusGradeMap D m x)) +
          minusIn D n (p.2 (minusGradeMap D m x))
      map_add' := by
        intro x y
        simp only [map_add, LinearMap.add_apply]
        module
      map_smul' := by
        intro c x
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
        module
    }
  map_add' p q := by
    apply LinearMap.ext
    intro x
    change
      plusIn D n ((p.1 + q.1) (plusGradeMap D m x)) +
          minusIn D n ((p.2 + q.2) (minusGradeMap D m x)) =
        (plusIn D n (p.1 (plusGradeMap D m x)) +
          minusIn D n (p.2 (minusGradeMap D m x))) +
            (plusIn D n (q.1 (plusGradeMap D m x)) +
              minusIn D n (q.2 (minusGradeMap D m x)))
    simp only [LinearMap.add_apply, map_add]
    abel
  map_smul' c p := by
    apply LinearMap.ext
    intro x
    change
      plusIn D n ((c • p.1) (plusGradeMap D m x)) +
          minusIn D n ((c • p.2) (minusGradeMap D m x)) =
        c • (plusIn D n (p.1 (plusGradeMap D m x)) +
          minusIn D n (p.2 (minusGradeMap D m x)))
    simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply]
    module

@[simp] theorem blockMap_apply (D : LatticeData) (m n : ℤ)
    (p : (plusGrade D m →ₗ[ℂ] plusGrade D n) ×
      (minusGrade D m →ₗ[ℂ] minusGrade D n)) (x : grade D m) :
    blockMap D m n p x =
      plusIn D n (p.1 (plusGradeMap D m x)) +
        minusIn D n (p.2 (minusGradeMap D m x)) := by
  rfl

private theorem blockMap_intertwines (D : LatticeData) (m n : ℤ)
    (p : (plusGrade D m →ₗ[ℂ] plusGrade D n) ×
      (minusGrade D m →ₗ[ℂ] minusGrade D n)) :
    (gradeTheta D n).comp (blockMap D m n p) =
      (blockMap D m n p).comp (gradeTheta D m) := by
  apply LinearMap.ext
  intro x
  change gradeTheta D n
      (plusIn D n (p.1 (plusGradeMap D m x)) +
        minusIn D n (p.2 (minusGradeMap D m x))) =
    plusIn D n (p.1 (plusGradeMap D m (gradeTheta D m x))) +
      minusIn D n (p.2 (minusGradeMap D m (gradeTheta D m x)))
  rw [map_add, plusIn_theta, minusIn_theta,
    plusGradeMap_theta, minusGradeMap_theta]
  simp only [map_neg]

def thetaIntertwinerFromBlocks (D : LatticeData) (m n : ℤ) :
    ((plusGrade D m →ₗ[ℂ] plusGrade D n) ×
      (minusGrade D m →ₗ[ℂ] minusGrade D n)) →ₗ[ℂ]
        thetaIntertwiner D m n :=
  (blockMap D m n).codRestrict (thetaIntertwiner D m n)
    (fun p => blockMap_intertwines D m n p)

@[simp] theorem thetaIntertwinerFromBlocks_val (D : LatticeData) (m n : ℤ)
    (p : (plusGrade D m →ₗ[ℂ] plusGrade D n) ×
      (minusGrade D m →ₗ[ℂ] minusGrade D n)) :
    (thetaIntertwinerFromBlocks D m n p).1 = blockMap D m n p := by
  rfl

@[simp] theorem plusBlock_val (D : LatticeData) (m n : ℤ)
    (F : thetaIntertwiner D m n) (x : plusGrade D m) :
    ((plusBlock D m n F) x).1 = (F.1 (plusIn D m x)).1 := by
  rfl

@[simp] theorem minusBlock_val (D : LatticeData) (m n : ℤ)
    (F : thetaIntertwiner D m n) (x : minusGrade D m) :
    ((minusBlock D m n F) x).1 = (F.1 (minusIn D m x)).1 := by
  rfl

private theorem grade_decomp (D : LatticeData) (m : ℤ) (x : grade D m) :
    x = plusIn D m (plusGradeMap D m x) +
      minusIn D m (minusGradeMap D m x) := by
  apply Subtype.ext
  change x.1 = plusPart D x.1 + minusPart D x.1
  exact (thetaRep_grade_plus_minus_decomposition D m x).1

theorem thetaIntertwinerFromBlocks_toBlocks (D : LatticeData) (m n : ℤ)
    (p : (plusGrade D m →ₗ[ℂ] plusGrade D n) ×
      (minusGrade D m →ₗ[ℂ] minusGrade D n)) :
    thetaIntertwinerToBlocks D m n (thetaIntertwinerFromBlocks D m n p) = p := by
  apply Prod.ext
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change
      ((plusBlock D m n (thetaIntertwinerFromBlocks D m n p)) x).1 =
        (p.1 x).1
    rw [plusBlock_val, thetaIntertwinerFromBlocks_val]
    change ((blockMap D m n p) (plusIn D m x)).1 = (p.1 x).1
    rw [blockMap_apply, plusGradeMap_plusIn, minusGradeMap_plusIn]
    rw [map_zero]
    change (p.1 x).1 + 0 = (p.1 x).1
    simp
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change
      ((minusBlock D m n (thetaIntertwinerFromBlocks D m n p)) x).1 =
        (p.2 x).1
    rw [minusBlock_val, thetaIntertwinerFromBlocks_val]
    change ((blockMap D m n p) (minusIn D m x)).1 = (p.2 x).1
    rw [blockMap_apply, plusGradeMap_minusIn, minusGradeMap_minusIn]
    rw [map_zero]
    change 0 + (p.2 x).1 = (p.2 x).1
    simp

theorem thetaIntertwinerFromBlocks_leftInverse (D : LatticeData) (m n : ℤ)
    (F : thetaIntertwiner D m n) :
    thetaIntertwinerFromBlocks D m n (thetaIntertwinerToBlocks D m n F) = F := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have h := grade_decomp D m x
  change
    (blockMap D m n (thetaIntertwinerToBlocks D m n F)) x = F.1 x
  rw [blockMap_apply]
  change
    plusIn D n ((plusBlock D m n F) (plusGradeMap D m x)) +
        minusIn D n ((minusBlock D m n F) (minusGradeMap D m x)) = F.1 x
  calc
    _ = F.1 (plusIn D m (plusGradeMap D m x) +
        minusIn D m (minusGradeMap D m x)) := by
      apply Subtype.ext
      change
        ((plusBlock D m n F (plusGradeMap D m x)).1) +
            ((minusBlock D m n F (minusGradeMap D m x)).1) =
          (F.1 (plusIn D m (plusGradeMap D m x) +
            minusIn D m (minusGradeMap D m x))).1
      rw [plusBlock_val, minusBlock_val]
      exact congrArg Subtype.val (F.1.map_add _ _).symm
    _ = F.1 x := (congrArg F.1 h).symm

def thetaIntertwinerEquiv (D : LatticeData) (m n : ℤ) :
    thetaIntertwiner D m n ≃ₗ[ℂ]
      (plusGrade D m →ₗ[ℂ] plusGrade D n) ×
        (minusGrade D m →ₗ[ℂ] minusGrade D n) :=
  LinearEquiv.ofLinearMap
    (thetaIntertwinerToBlocks D m n)
    (thetaIntertwinerFromBlocks D m n)
    (by
      apply LinearMap.ext
      intro p
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        thetaIntertwinerFromBlocks_toBlocks D m n p)
    (by
      apply LinearMap.ext
      intro F
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        thetaIntertwinerFromBlocks_leftInverse D m n F)

theorem thetaIntertwiner_finrank (D : LatticeData) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Module.finrank ℂ (thetaIntertwiner D m n) =
      Module.finrank ℂ (plusGrade D m) * Module.finrank ℂ (plusGrade D n) +
        Module.finrank ℂ (minusGrade D m) * Module.finrank ℂ (minusGrade D n) := by
  letI : FiniteDimensional ℂ (grade D m) := grade_finiteDimensional D hD m
  letI : FiniteDimensional ℂ (grade D n) := grade_finiteDimensional D hD n
  letI : FiniteDimensional ℂ (plusGrade D m) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (plusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (minusGrade D m) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (minusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  rw [(thetaIntertwinerEquiv D m n).finrank_eq, Module.finrank_prod,
    Module.finrank_linearMap, Module.finrank_linearMap]

private theorem grade_finrank_eq_plus_add_minus (D : LatticeData) (n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Module.finrank ℂ (grade D n) =
      Module.finrank ℂ (plusGrade D n) + Module.finrank ℂ (minusGrade D n) := by
  letI : FiniteDimensional ℂ (grade D n) := grade_finiteDimensional D hD n
  letI : FiniteDimensional ℂ (plusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (minusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  rw [(gradeSplitEquiv D n).finrank_eq, Module.finrank_prod]

theorem thetaIntertwiner_finrank_trace_character (D : LatticeData) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    (2 : ℂ) * (Module.finrank ℂ (thetaIntertwiner D m n) : ℂ) =
      (Module.finrank ℂ (grade D m) : ℂ) *
          (Module.finrank ℂ (grade D n) : ℂ) +
        LinearMap.trace ℂ (grade D m) (gradeTheta D m) *
          LinearMap.trace ℂ (grade D n) (gradeTheta D n) := by
  letI : FiniteDimensional ℂ (grade D m) := grade_finiteDimensional D hD m
  letI : FiniteDimensional ℂ (grade D n) := grade_finiteDimensional D hD n
  letI : FiniteDimensional ℂ (plusGrade D m) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (plusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (minusGrade D m) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (minusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  rw [thetaIntertwiner_finrank D m n hD,
    grade_theta_trace_eq_fixed_minus_anti D m hD,
    grade_theta_trace_eq_fixed_minus_anti D n hD,
    grade_finrank_eq_plus_add_minus D m hD,
    grade_finrank_eq_plus_add_minus D n hD]
  push_cast
  ring

end D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeIntertwiner
