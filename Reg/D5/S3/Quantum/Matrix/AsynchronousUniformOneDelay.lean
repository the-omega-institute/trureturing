import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay
import Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius
import Reg.Support.SingleDependentReadout

noncomputable section
open Matrix
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open _root_.D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open _root_.D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
open _root_.D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal

namespace Reg.D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ≥0∞)

def actual : Realization signature :=
  realize signature (fun _ _ lam => ENNReal.ofReal (Real.sqrt lam)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ≥0∞)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ℓ : ℕ} (_hℓ : 0 < ℓ) (n : Fin ℓ → ℕ)
    (_hn : ∀ i, 0 < n i) (N : Matrix (Vtx n) (Vtx n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (_hN : ∀ p q, p.1 = q.1 → N p q = 0)
    (_hδ : ∀ i j, i ≠ j → 1 ≤ δ i j ∧ δ i j ≤ 1)
    (K : ℕ) (_hK : 1 ≤ K) (lam : ℝ) (_hl0 : 0 < lam) (_hl1 : lam < 1)
    (_hradius : radius N = ENNReal.ofReal lam),
    radius (asyncMatrix N δ K) = R.readout () () lam ∧
      R.readout () () lam < 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let U := AsynchronousTwoBlockRadius.halfBlock
  have hN : ∀ p q : Vtx (![1,1] : Fin 2 → ℕ),
      p.1 = q.1 → zeroDiagonal U U p q = 0 := by
    rintro ⟨i,x⟩ ⟨j,y⟩ hij
    fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y
    all_goals first | rfl | norm_num at hij
  have h := law (ℓ := 2) (by omega) ![1,1] (by intro i; fin_cases i <;> decide)
    (zeroDiagonal U U) !![0,1;1,0] hN
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)
    1 (by omega) (1/2) (by norm_num) (by norm_num)
    AsynchronousTwoBlockRadius.half_radius
  exact (lt_irrefl (1 : ℝ≥0∞)) h.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1/4 : ℝ), (1/9 : ℝ), ?_⟩
  change ENNReal.ofReal (Real.sqrt (1/4)) ≠ ENNReal.ofReal (Real.sqrt (1/9))
  have h4 : Real.sqrt (1/4) = (1/2 : ℝ) := by
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have h9 : Real.sqrt (1/9) = (1/3 : ℝ) := by
    rw [show (1/9 : ℝ) = (1/3)^2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [h4, h9]
  norm_num

def realization : Registration arena (type_of% (@whole_uniform_one_delay)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@whole_uniform_one_delay, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_uniform_one_delay) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ lam => ENNReal.ofReal (Real.sqrt lam))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay
