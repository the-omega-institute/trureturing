import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.BanachGeometry.LinfKNumber
import Reg.Support.SingleDependentReadout

/-! # Audit of the finite-coordinate strict-descent criterion -/

open _root_.D5.S3.Analytic.BanachGeometry.LinfKNumber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit


noncomputable section
namespace Reg.D5.S3.Analytic.BanachGeometry.LinfKNumber

/-- The dimension indexes the original finite-coordinate state space. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℕ (fun n => Fin n → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => ‖w‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The whole telescope, with the perturbed-vector norm as readout. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {w z : Fin n → ℝ}, w ≠ 0 →
    (∀ i, |w i| = ‖w‖ → 0 < z i * w i) →
    ¬ ∀ t : ℝ, ‖w‖ ≤ R.readout () n (w + t • z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let w : Fin 1 → ℝ := fun _ => 1
  have hn : ‖w‖ = 1 := by simp [w, Pi.norm_def]
  have hw : w ≠ 0 := by intro hz; have := congrFun hz 0; norm_num [w] at this
  have hh := @h 1 w w hw (by intro i _; norm_num [w])
  apply hh
  intro t
  change ‖w‖ ≤ 1
  exact hn.le

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, (fun _ => 1), ?_⟩
  change ‖(0 : Fin 1 → ℝ)‖ ≠ ‖(fun _ : Fin 1 => (1 : ℝ))‖
  rw [norm_zero]
  intro h
  have hz := norm_eq_zero.mp h.symm
  have hzero := congrFun hz 0
  norm_num at hzero

def family : Registration arena (type_of% (@active_not_BJ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@active_not_BJ, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@active_not_BJ) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BanachGeometry.LinfKNumber.active_not_BJ_unit
  realizationName := `Reg.D5.S3.Analytic.BanachGeometry.LinfKNumber.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ w => ‖w‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BanachGeometry.LinfKNumber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.BanachGeometry.LinfKNumber
