/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaGradeTraceSplit
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/ThetaGradeTraceSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: The theta twined trace is the fixed-minus-anti-fixed dimension on each finite energy grade. -/

import D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeTraceSplit

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField
open SourcePairingLaws OriginalSourcePairing OriginalSourceCoevaluation
open ThetaReflectionAction

/-- The theta-even and theta-odd parts of one energy grade. -/
def plusGrade (D : LatticeData) (n : ℤ) : Submodule ℂ (Carrier D) :=
  grade D n ⊓ fixedSpace D

def minusGrade (D : LatticeData) (n : ℤ) : Submodule ℂ (Carrier D) :=
  grade D n ⊓ minusSpace D

private def plusPartLinear (D : LatticeData) : Carrier D →ₗ[ℂ] Carrier D where
  toFun := plusPart D
  map_add' x y := by
    simp only [plusPart, map_add, smul_add]
    module
  map_smul' c x := by
    simp only [plusPart, map_smul, smul_add, smul_smul]
    simp only [RingHom.id_apply]
    module

private def minusPartLinear (D : LatticeData) : Carrier D →ₗ[ℂ] Carrier D where
  toFun := minusPart D
  map_add' x y := by
    simp only [minusPart, map_add, smul_sub]
    module
  map_smul' c x := by
    simp only [minusPart, map_smul, smul_sub, smul_smul]
    simp only [RingHom.id_apply]
    module

def plusGradeMap (D : LatticeData) (n : ℤ) :
    grade D n →ₗ[ℂ] plusGrade D n :=
  ((plusPartLinear D).domRestrict (grade D n)).codRestrict
    (plusGrade D n) (fun v => by
      have h := thetaRep_grade_plus_minus_decomposition D n v
      exact ⟨h.2.1, h.2.2.2.1⟩)

def minusGradeMap (D : LatticeData) (n : ℤ) :
    grade D n →ₗ[ℂ] minusGrade D n :=
  ((minusPartLinear D).domRestrict (grade D n)).codRestrict
    (minusGrade D n) (fun v => by
      have h := thetaRep_grade_plus_minus_decomposition D n v
      exact ⟨h.2.2.1, h.2.2.2.2⟩)

def gradeTheta (D : LatticeData) (n : ℤ) :
    grade D n →ₗ[ℂ] grade D n :=
  (thetaLinear D).domRestrict (grade D n) |>.codRestrict
    (grade D n) (fun v => by
      change thetaLinear D v.1 ∈ grade D n
      simpa [thetaRep, theta] using
        thetaRep_preserves_energy_grade D n v.1 v.2)

@[simp] theorem gradeTheta_val (D : LatticeData) (n : ℤ) (v : grade D n) :
    (gradeTheta D n v).1 = theta D v.1 := by
  rfl

private theorem plusPart_fixed (D : LatticeData) (v : Carrier D)
    (hv : v ∈ fixedSpace D) : plusPart D v = v := by
  rw [plusPart, (mem_fixedSpace D v).mp hv, ← two_smul ℂ v,
    smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

private theorem minusPart_fixed (D : LatticeData) (v : Carrier D)
    (hv : v ∈ fixedSpace D) : minusPart D v = 0 := by
  rw [minusPart, (mem_fixedSpace D v).mp hv, sub_self, smul_zero]

private theorem plusPart_minus (D : LatticeData) (v : Carrier D)
    (hv : v ∈ minusSpace D) : plusPart D v = 0 := by
  have he : theta D v = (-1 : ℂ) • v := (mem_eigenspace D (-1) v).mp hv
  rw [plusPart, he, smul_add]
  simp

private theorem minusPart_minus (D : LatticeData) (v : Carrier D)
    (hv : v ∈ minusSpace D) : minusPart D v = v := by
  have he : theta D v = (-1 : ℂ) • v := (mem_eigenspace D (-1) v).mp hv
  rw [minusPart, he]
  module

def gradeSplitEquiv (D : LatticeData) (n : ℤ) :
    grade D n ≃ₗ[ℂ] plusGrade D n × minusGrade D n := by
  let e : grade D n →ₗ[ℂ] plusGrade D n × minusGrade D n :=
    (plusGradeMap D n).prod (minusGradeMap D n)
  exact LinearEquiv.ofBijective e ⟨
    (by
      intro v w h
      apply Subtype.ext
      have hp := congrArg
        (fun z : plusGrade D n × minusGrade D n => z.1.1)
        h
      have hm := congrArg
        (fun z : plusGrade D n × minusGrade D n => z.2.1)
        h
      change plusPart D v.1 = plusPart D w.1 at hp
      change minusPart D v.1 = minusPart D w.1 at hm
      have hv := thetaRep_grade_plus_minus_decomposition D n v
      have hw := thetaRep_grade_plus_minus_decomposition D n w
      exact (hv.1.trans (congrArg₂ (fun a b => a + b) hp hm)).trans hw.1.symm),
    (by
      intro p
      refine ⟨⟨p.1.1 + p.2.1, (grade D n).add_mem p.1.2.1 p.2.2.1⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change plusPart D (p.1.1 + p.2.1) = p.1.1
        simp only [plusPart, map_add]
        rw [(mem_fixedSpace D p.1.1).mp p.1.2.2]
        rw [(mem_eigenspace D (-1) p.2.1).mp p.2.2.2]
        module
      · apply Subtype.ext
        change minusPart D (p.1.1 + p.2.1) = p.2.1
        simp only [minusPart, map_add]
        rw [(mem_fixedSpace D p.1.1).mp p.1.2.2]
        rw [(mem_eigenspace D (-1) p.2.1).mp p.2.2.2]
        module)⟩

private theorem gradeSplitEquiv_fst (D : LatticeData) (n : ℤ) (v : grade D n) :
    (gradeSplitEquiv D n v).1.1 = plusPart D v.1 := by
  rfl

private theorem gradeSplitEquiv_snd (D : LatticeData) (n : ℤ) (v : grade D n) :
    (gradeSplitEquiv D n v).2.1 = minusPart D v.1 := by
  rfl


theorem grade_split_theta_conj (D : LatticeData) (n : ℤ) :
    (gradeSplitEquiv D n).conj (gradeTheta D n) =
      (LinearMap.id : plusGrade D n →ₗ[ℂ] plusGrade D n).prodMap
        (-(LinearMap.id : minusGrade D n →ₗ[ℂ] minusGrade D n)) := by
  let e := gradeSplitEquiv D n
  have hplus_theta (v : grade D n) :
      plusPart D (theta D v.1) = plusPart D v.1 := by
    simp only [plusPart, map_add]
    have hi : theta D (theta D v.1) = v.1 := theta_involutive D v.1
    rw [hi]
    rw [add_comm]
  have hminus_theta (v : grade D n) :
      minusPart D (theta D v.1) = -minusPart D v.1 := by
    simp only [minusPart, map_sub]
    have hi : theta D (theta D v.1) = v.1 := theta_involutive D v.1
    rw [hi]
    module
  have hconj : e.conj (gradeTheta D n) =
      (LinearMap.id : plusGrade D n →ₗ[ℂ] plusGrade D n).prodMap
        (-(LinearMap.id : minusGrade D n →ₗ[ℂ] minusGrade D n)) := by
    apply LinearMap.ext
    intro p
    obtain ⟨v, rfl⟩ := e.surjective p
    rw [e.conj_apply]
    simp only [LinearMap.comp_apply]
    change e (gradeTheta D n (e.symm (e v))) = _
    rw [e.symm_apply_apply]
    apply Prod.ext
    · apply Subtype.ext
      change (e (gradeTheta D n v)).1.1 = (e v).1.1
      calc
        (e (gradeTheta D n v)).1.1 = plusPart D (theta D v.1) := by
          change (gradeSplitEquiv D n (gradeTheta D n v)).1.1 = _
          rw [gradeSplitEquiv_fst]
          rfl
        _ = plusPart D v.1 := hplus_theta v
        _ = (e v).1.1 := by
          change _ = (gradeSplitEquiv D n v).1.1
          rw [gradeSplitEquiv_fst]
    · apply Subtype.ext
      change (e (gradeTheta D n v)).2.1 = -(e v).2.1
      calc
        (e (gradeTheta D n v)).2.1 = minusPart D (theta D v.1) := by
          change (gradeSplitEquiv D n (gradeTheta D n v)).2.1 = _
          rw [gradeSplitEquiv_snd]
          rfl
        _ = -minusPart D v.1 := hminus_theta v
        _ = -(e v).2.1 := by
          change _ = -(gradeSplitEquiv D n v).2.1
          rw [gradeSplitEquiv_snd]
  exact hconj

set_option maxHeartbeats 800000 in
theorem grade_theta_trace_eq_fixed_minus_anti (D : LatticeData) (n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    LinearMap.trace ℂ (grade D n) (gradeTheta D n) =
      (Module.finrank ℂ (plusGrade D n) : ℂ) -
        (Module.finrank ℂ (minusGrade D n) : ℂ) := by
  letI : FiniteDimensional ℂ (grade D n) := grade_finiteDimensional D hD n
  letI : FiniteDimensional ℂ (plusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  letI : FiniteDimensional ℂ (minusGrade D n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let e := gradeSplitEquiv D n
  have hplus_theta (v : grade D n) :
      plusPart D (theta D v.1) = plusPart D v.1 := by
    simp only [plusPart, map_add]
    have hi : theta D (theta D v.1) = v.1 := theta_involutive D v.1
    rw [hi]
    rw [add_comm]
  have hminus_theta (v : grade D n) :
      minusPart D (theta D v.1) = -minusPart D v.1 := by
    simp only [minusPart, map_sub]
    have hi : theta D (theta D v.1) = v.1 := theta_involutive D v.1
    rw [hi]
    module
  have hconj : e.conj (gradeTheta D n) =
      (LinearMap.id : plusGrade D n →ₗ[ℂ] plusGrade D n).prodMap
        (-(LinearMap.id : minusGrade D n →ₗ[ℂ] minusGrade D n)) := by
    apply LinearMap.ext
    intro p
    obtain ⟨v, rfl⟩ := e.surjective p
    rw [e.conj_apply]
    simp only [LinearMap.comp_apply]
    change e (gradeTheta D n (e.symm (e v))) = _
    rw [e.symm_apply_apply]
    apply Prod.ext
    · apply Subtype.ext
      change (e (gradeTheta D n v)).1.1 = (e v).1.1
      calc
        (e (gradeTheta D n v)).1.1 = plusPart D (theta D v.1) := by
          change (gradeSplitEquiv D n (gradeTheta D n v)).1.1 = _
          rw [gradeSplitEquiv_fst]
          rfl
        _ = plusPart D v.1 := hplus_theta v
        _ = (e v).1.1 := by
          change _ = (gradeSplitEquiv D n v).1.1
          rw [gradeSplitEquiv_fst]
    · apply Subtype.ext
      change (e (gradeTheta D n v)).2.1 = -(e v).2.1
      calc
        (e (gradeTheta D n v)).2.1 = minusPart D (theta D v.1) := by
          change (gradeSplitEquiv D n (gradeTheta D n v)).2.1 = _
          rw [gradeSplitEquiv_snd]
          rfl
        _ = -minusPart D v.1 := hminus_theta v
        _ = -(e v).2.1 := by
          change _ = -(gradeSplitEquiv D n v).2.1
          rw [gradeSplitEquiv_snd]
  rw [← LinearMap.trace_conj' (gradeTheta D n) e]
  rw [hconj, LinearMap.trace_prodMap']
  simp [LinearMap.trace_id, sub_eq_add_neg]

end D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeTraceSplit
