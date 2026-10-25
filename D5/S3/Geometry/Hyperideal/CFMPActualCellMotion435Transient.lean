import D5.S3.Geometry.Hyperideal.CFMPNativeMovingPoint435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalCellsIndependent435Transient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open CFMPOriginalCellsIndependent435Transient

namespace CFMPActualCellMotion435Transient

theorem endpoint_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (i j : Fin 4) (hij : i ≠ j) :
    DifferentiableAt ℝ (fun s => endpoint (l s) i j) t := by
  have hcoords := differentiableAt_pi.mp hl
  have hG : DifferentiableAt ℝ (fun s => lengthGram (l s) i j) t := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact differentiableAt_const _
      | exact (hcoords 0).cosh.neg
      | exact (hcoords 1).cosh.neg
      | exact (hcoords 2).cosh.neg
      | exact (hcoords 3).cosh.neg
      | exact (hcoords 4).cosh.neg
      | exact (hcoords 5).cosh.neg
  have hz : 1 - lengthGram (l t) i j ≠ 0 := by
    fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | simp [lengthGram]; positivity
  have ha := hG.neg.div ((differentiableAt_const (1 : ℝ)).sub hG) hz
  have hb := (differentiableAt_const (1 : ℝ)).div
    ((differentiableAt_const (1 : ℝ)).sub hG) hz
  apply differentiableAt_pi.mpr
  intro k
  simp only [endpoint,Pi.add_apply,Pi.single_apply]
  split_ifs <;> fun_prop

theorem vertices_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (j : Fin 4) :
    DifferentiableAt ℝ (fun s => vertices (l s) n j) t := by
  fin_cases n <;> fin_cases j <;> simp only [vertices] <;>
    first
    | exact differentiableAt_const _
    | exact endpoint_differentiable l t hl _ _ (by decide)


def cellPoint (l : Fin 6 → ℝ) (n : Fin 20) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  drop (vertices l n 0) + (edgeMatrix l n).mulVec u

theorem edgeMatrix_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) :
    DifferentiableAt ℝ (fun s => edgeMatrix (l s) n) t := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  exact (differentiableAt_pi.mp (vertices_differentiable l t hl n j.succ) i.castSucc).sub
    (differentiableAt_pi.mp (vertices_differentiable l t hl n 0) i.castSucc)

theorem cellPoint_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (u : Fin 3 → ℝ) :
    DifferentiableAt ℝ (fun s => cellPoint (l s) n u) t := by
  have hv (j : Fin 4) (i : Fin 3) :
      DifferentiableAt ℝ (fun s => vertices (l s) n j i.castSucc) t :=
    differentiableAt_pi.mp (vertices_differentiable l t hl n j) i.castSucc
  apply differentiableAt_pi.mpr
  intro i
  change DifferentiableAt ℝ (fun s => vertices (l s) n 0 i.castSucc +
    ∑ j : Fin 3, (vertices (l s) n j.succ i.castSucc -
      vertices (l s) n 0 i.castSucc) * u j) t
  apply (hv 0 i).add
  simpa -implicitDefEqProofs only [Fin.sum_univ_three, Pi.add_def, Pi.sub_def] using
    (((((hv (0 : Fin 3).succ i).sub (hv 0 i)).mul_const (u 0)).add
      (((hv (1 : Fin 3).succ i).sub (hv 0 i)).mul_const (u 1))).add
      (((hv (2 : Fin 3).succ i).sub (hv 0 i)).mul_const (u 2)))

theorem actual_native_cell_velocity (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (u : Fin 3 → ℝ)
    (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (D : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : HasDerivAt M D t) (hdet : (M t).det ≠ 0)
    (hq : 0 < CFMPFrameContinuity435Transient.q (M t) (cellPoint (l t) n u))
    (hd : CFMPNativePullbackMetric435Transient.delta
      (CFMPFrameContinuity435Transient.ambient (M t) (cellPoint (l t) n u)) ≠ 0) :
    deriv (fun s => CFMPNativePullbackMetric435Transient.nativeMap
      (CFMPFrameContinuity435Transient.ambient (M s) (cellPoint (l s) n u))) t =
      deriv (fun r : ℝ => CFMPNativePullbackMetric435Transient.nativeMap
        (CFMPFrameContinuity435Transient.ambient (M t)
          (cellPoint (l t) n u + r •
            (deriv (fun s => cellPoint (l s) n u) t +
              CFMPFrameMotion435Transient.field (D*(M t)⁻¹) (cellPoint (l t) n u))))) 0 := by
  exact CFMPNativeMovingPoint435Transient.total_native_velocity M D
    (fun s => cellPoint (l s) n u) _ t hM
    (cellPoint_differentiable l t hl n u).hasDerivAt hdet hq hd

#print axioms actual_native_cell_velocity
end CFMPActualCellMotion435Transient
