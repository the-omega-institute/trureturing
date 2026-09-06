/- GID: D5/S3/Quantum/Magic/QuquintCertificateAssembly
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintCertificateAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=consumer=D5/S3/Quantum/Magic/QuquintFiniteMaximum.second_variation_negative
   digest: Negative definiteness of all thirty-two numerical branch matrices. -/

import D5.S3.Quantum.Magic.QuquintCertificateFirst
import D5.S3.Quantum.Magic.QuquintCertificateSecond
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
open Matrix
open D5.S3.Quantum.Magic.QuquintCertificateData
open D5.S3.Quantum.Magic.QuquintCertificateFirst
open D5.S3.Quantum.Magic.QuquintCertificateSecond
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000
namespace D5.S3.Quantum.Magic.QuquintCertificateAssembly
private def lower (s : Fin 32) : Matrix (Fin 4) (Fin 4) ℝ :=
  match s.val with
  | 0 => lower0
  | 1 => lower1
  | 2 => lower2
  | 3 => lower3
  | 4 => lower4
  | 5 => lower5
  | 6 => lower6
  | 7 => lower7
  | 8 => lower8
  | 9 => lower9
  | 10 => lower10
  | 11 => lower11
  | 12 => lower12
  | 13 => lower13
  | 14 => lower14
  | 15 => lower15
  | 16 => lower16
  | 17 => lower17
  | 18 => lower18
  | 19 => lower19
  | 20 => lower20
  | 21 => lower21
  | 22 => lower22
  | 23 => lower23
  | 24 => lower24
  | 25 => lower25
  | 26 => lower26
  | 27 => lower27
  | 28 => lower28
  | 29 => lower29
  | 30 => lower30
  | _ => lower31
private def pivots (s : Fin 32) : Fin 4 → ℝ :=
  match s.val with
  | 0 => pivots0
  | 1 => pivots1
  | 2 => pivots2
  | 3 => pivots3
  | 4 => pivots4
  | 5 => pivots5
  | 6 => pivots6
  | 7 => pivots7
  | 8 => pivots8
  | 9 => pivots9
  | 10 => pivots10
  | 11 => pivots11
  | 12 => pivots12
  | 13 => pivots13
  | 14 => pivots14
  | 15 => pivots15
  | 16 => pivots16
  | 17 => pivots17
  | 18 => pivots18
  | 19 => pivots19
  | 20 => pivots20
  | 21 => pivots21
  | 22 => pivots22
  | 23 => pivots23
  | 24 => pivots24
  | 25 => pivots25
  | 26 => pivots26
  | 27 => pivots27
  | 28 => pivots28
  | 29 => pivots29
  | 30 => pivots30
  | _ => pivots31
private theorem ldl_identity (s : Fin 32) :
    -branch s = lower s * Matrix.diagonal (pivots s) * (lower s)ᵀ := by
  fin_cases s <;> simp only [lower, pivots]
  · exact ldl_0
  · exact ldl_1
  · exact ldl_2
  · exact ldl_3
  · exact ldl_4
  · exact ldl_5
  · exact ldl_6
  · exact ldl_7
  · exact ldl_8
  · exact ldl_9
  · exact ldl_10
  · exact ldl_11
  · exact ldl_12
  · exact ldl_13
  · exact ldl_14
  · exact ldl_15
  · exact ldl_16
  · exact ldl_17
  · exact ldl_18
  · exact ldl_19
  · exact ldl_20
  · exact ldl_21
  · exact ldl_22
  · exact ldl_23
  · exact ldl_24
  · exact ldl_25
  · exact ldl_26
  · exact ldl_27
  · exact ldl_28
  · exact ldl_29
  · exact ldl_30
  · exact ldl_31
private theorem pivots_positive (s : Fin 32) (i : Fin 4) : 0 < pivots s i := by
  have h := radical_bounds
  fin_cases s <;> fin_cases i <;> norm_num [pivots, pivots0, pivots1, pivots2, pivots3, pivots4, pivots5, pivots6, pivots7, pivots8, pivots9, pivots10, pivots11, pivots12, pivots13, pivots14, pivots15, pivots16, pivots17, pivots18, pivots19, pivots20, pivots21, pivots22, pivots23, pivots24, pivots25, pivots26, pivots27, pivots28, pivots29, pivots30, pivots31] <;> linarith
private theorem lower_unit (s : Fin 32) : IsUnit (lower s) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have ht : (lower s).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [lower, lower0, lower1, lower2, lower3, lower4, lower5, lower6, lower7, lower8, lower9, lower10, lower11, lower12, lower13, lower14, lower15, lower16, lower17, lower18, lower19, lower20, lower21, lower22, lower23, lower24, lower25, lower26, lower27, lower28, lower29, lower30, lower31] at *
  rw [Matrix.det_of_isLowerTriangular _ ht]
  have hd (i : Fin 4) : lower s i i = 1 := by
    fin_cases s <;> fin_cases i <;> norm_num [lower, lower0, lower1, lower2, lower3, lower4, lower5, lower6, lower7, lower8, lower9, lower10, lower11, lower12, lower13, lower14, lower15, lower16, lower17, lower18, lower19, lower20, lower21, lower22, lower23, lower24, lower25, lower26, lower27, lower28, lower29, lower30, lower31]
  simp_rw [hd]
  simp
theorem all_branches_negative : ∀ s : Fin 32, Matrix.PosDef (-branch s) := by
  intro s
  rw [ldl_identity]
  have h := (lower_unit s).posDef_star_right_conjugate_iff.mpr
    (Matrix.PosDef.diagonal (pivots_positive s))
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
#print axioms ldl_identity
#print axioms pivots_positive
#print axioms lower_unit
#print axioms all_branches_negative
end D5.S3.Quantum.Magic.QuquintCertificateAssembly
