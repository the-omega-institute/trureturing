/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaGradeIntertwiner
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/ThetaGradeIntertwiner
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

end D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeIntertwiner
