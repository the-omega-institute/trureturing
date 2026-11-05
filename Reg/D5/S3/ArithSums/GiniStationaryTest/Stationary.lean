import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.GiniStationaryTest.Stationary
import Reg.Support.SingleDependentReadout

/-! Typed observations for the stationary Gini comparison. -/

namespace Reg.D5.S3.ArithSums.GiniStationaryTest.Stationary
open _root_.D5.S3.ArithSums.GiniStationaryTest.Defs
open _root_.D5.S3.ArithSums.GiniStationaryTest.Stationary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Derivatives
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => chiDeriv 2 (-1) z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ z : ℝ, 0 < z →
    chiDeriv 1 0 z = 1 ∧ R.readout () () z = (2 * z + (z ^ 2)⁻¹) / 3
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 (by norm_num)).2
  norm_num [rejected, realize] at he
def evidence : Registration arena (type_of% @chiDeriv_parameters) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨chiDeriv_parameters, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change chiDeriv 2 (-1) 1 ≠ chiDeriv 2 (-1) 2
    rw [(chiDeriv_parameters 1 (by norm_num)).2,
      (chiDeriv_parameters 2 (by norm_num)).2]
    norm_num
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chiDeriv_parameters) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Stationary.Derivatives.unit
  realizationName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Stationary.Derivatives.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => chiDeriv 2 (-1) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GiniStationaryTest.Stationary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Derivatives

namespace StationaryTest
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ u => giniMean 2 (-1) u) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 1 ≤ n → ∀ u : Fin n → ℝ, (∀ i, 0 < u i) →
    giniMean 1 0 u = 1 →
    (∃ ρ : ℝ, ∀ k, chiDeriv 2 (-1) (u k) + ρ * chiDeriv 1 0 (u k) = 0) →
    1 ≤ R.readout () n u
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 (by omega) (fun _ => 1) (by intro i; norm_num)
    (by norm_num [giniMean, _root_.D5.S3.ArithSums.GiniMeanEndpointComparison.giniMean])
    (by
      refine ⟨-chiDeriv 2 (-1) 1, ?_⟩
      intro k
      change chiDeriv 2 (-1) 1 + -chiDeriv 2 (-1) 1 * chiDeriv 1 0 1 = 0
      rw [(chiDeriv_parameters 1 (by norm_num)).1]
      ring)
  norm_num [rejected, realize] at he
def evidence : Registration arena (type_of% @stationaryTest_one_zero_two_negOne) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stationaryTest_one_zero_two_negOne, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    norm_num [actual, realize, giniMean,
      _root_.D5.S3.ArithSums.GiniMeanEndpointComparison.giniMean]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stationaryTest_one_zero_two_negOne) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Stationary.StationaryTest.unit
  realizationName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Stationary.StationaryTest.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => giniMean 2 (-1) u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GiniStationaryTest.Stationary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end StationaryTest
end
end Reg.D5.S3.ArithSums.GiniStationaryTest.Stationary
