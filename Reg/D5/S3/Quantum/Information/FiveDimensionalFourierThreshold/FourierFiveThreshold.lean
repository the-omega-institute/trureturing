import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveThreshold
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveThreshold

open _root_.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    CoordinateFive (fun _ => CoordinateFive) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ x y => positiveFourierScore x y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 377 / 100) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x y : CoordinateFive), ‖x‖ = 1 → ‖y‖ = 1 → R.readout () x y < 377 / 100

private theorem rejected_law : ¬ arena.Law rejected := by
  let x : CoordinateFive := coordinateBasisFive 0
  have hx : ‖x‖ = 1 := coordinateBasisFive.orthonormal.norm_eq_one 0
  intro h
  exact (lt_irrefl (377 / 100 : ℝ)) (h x x hx hx)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let x : CoordinateFive := coordinateBasisFive 0
  let y : CoordinateFive := coordinateBasisFive 1
  refine ⟨x, x, y, ?_⟩
  change positiveFourierScore x x ≠ positiveFourierScore x y
  have hxx : positiveFourierScore x x = 0 := by
    simp [positiveFourierScore, score, scoreTerm]
  have hnonneg (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ scoreTerm p q :=
    div_nonneg (sq_nonneg _) (add_nonneg hp hq)
  have hzero : scoreTerm (‖x 0‖ ^ 2) (‖y 0‖ ^ 2) = 1 := by
    norm_num [scoreTerm, x, y, coordinateBasisFive, EuclideanSpace.basisFun_apply,
      PiLp.single_apply]
  have hleft : 1 ≤ score (fun j => ‖x j‖ ^ 2) (fun j => ‖y j‖ ^ 2) := by
    rw [← hzero]
    apply Finset.single_le_sum (f := fun j : Fin 5 => scoreTerm (‖x j‖ ^ 2) (‖y j‖ ^ 2))
    · exact fun _ _ => hnonneg _ _ (sq_nonneg _) (sq_nonneg _)
    · exact Finset.mem_univ 0
  rw [hxx]
  unfold positiveFourierScore
  have hright :
      0 ≤ score
        (fun j => ‖QuantumPhaseEstimationGeneral.QFT 5 (WithLp.ofLp x) j‖ ^ 2)
        (fun j => ‖QuantumPhaseEstimationGeneral.QFT 5 (WithLp.ofLp y) j‖ ^ 2) :=
    Finset.sum_nonneg (fun _ _ => hnonneg _ _ (sq_nonneg _) (sq_nonneg _))
  exact ne_of_lt (by linarith only [hleft, hright])

def sourceRegistration :
    Registration arena (type_of% @positiveFourierScore_lt_377_div_100) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positiveFourierScore_lt_377_div_100, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

/-- The observed value is the actual two-basis score at each pair of unit vectors. -/
def thresholdRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positiveFourierScore_lt_377_div_100) (Realization signature) Unit Unit := {
  unitName := .str ``sourceRegistration "unit"
  realizationName := ``sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => positiveFourierScore x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveThreshold
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveThreshold
