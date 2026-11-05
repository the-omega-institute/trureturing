import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.GiniStationaryTest.Witness
import Reg.Support.SingleDependentReadout

/-! Observation families for Gini comparison statements. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.GiniStationaryTest.Witness
open _root_.D5.S3.ArithSums.GiniStationaryTest.Defs
open _root_.D5.S3.ArithSums.GiniMeanEndpointComparison (highTuple)

noncomputable section
namespace Reg.D5.S3.ArithSums.GiniStationaryTest.Witness

namespace Identity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ t k => (t + k)^3 * (1 + k*t) - (k+1)^3*t*(t^2+k)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ t k : ℝ, R.readout () t k = k*(t-1)^3*(t-k^2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1
  norm_num [rejected, realize] at hh
def evidence : Registration arena (type_of% (@witness_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨witness_identity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨0, 0, 1, by norm_num [actual, realize]⟩
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@witness_identity)
    (type_of% (realize signature
      (fun _ t k => (t+k)^3*(1+k*t)-(k+1)^3*t*(t^2+k)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.ArithSums.GiniStationaryTest.Witness.witness_identity.information_unit
  realizationName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Witness.Identity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ t k => (t+k)^3*(1+k*t)-(k+1)^3*t*(t^2+k)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GiniStationaryTest.Witness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Identity

namespace TupleSum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ mt p => ∑ i : Fin (mt.1 + 1), highTuple (mt.1 + 1) mt.2 1 i ^ p)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (t p : ℝ), R.readout () ⟨m, t⟩ p = t ^ p + m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1 0
  norm_num [rejected, realize] at hh
def evidence : Registration arena (type_of% (@sum_highTuple_rpow)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_highTuple_rpow, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨0, 2⟩, 0, 1, ?_⟩
    change (∑ i : Fin (0 + 1), highTuple (0 + 1) 2 1 i ^ (0 : ℝ)) ≠
      (∑ i : Fin (0 + 1), highTuple (0 + 1) 2 1 i ^ (1 : ℝ))
    rw [sum_highTuple_rpow, sum_highTuple_rpow]
    norm_num
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_highTuple_rpow)
    (type_of% (realize signature
      (fun _ mt p => ∑ i : Fin (mt.1 + 1), highTuple (mt.1 + 1) mt.2 1 i ^ p)
      (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.ArithSums.GiniStationaryTest.Witness.sum_highTuple_rpow.information_unit
  realizationName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Witness.TupleSum.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ mt p => ∑ i : Fin (mt.1 + 1), highTuple (mt.1 + 1) mt.2 1 i ^ p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GiniStationaryTest.Witness
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end TupleSum

namespace Comparison
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ n t => giniMean 2 (-1) (highTuple n t 1)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ n t => giniMean 1 0 (highTuple n t 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 3 ≤ n → ∀ (t : ℝ), 0 < t → t < 1 →
    R.readout () n t < giniMean 1 0 (highTuple n t 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (lt_irrefl _) (h 3 le_rfl (1/2) (by norm_num) (by norm_num))
def evidence : Registration arena (type_of% (@witness_comparison)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨witness_comparison, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨3, 1/2, 1/4, ?_⟩
    change giniMean 2 (-1) (highTuple 3 (1/2) 1) ≠
      giniMean 2 (-1) (highTuple 3 (1/4) 1)
    simp only [giniMean, if_neg (by norm_num : (2 : ℝ) ≠ -1),
      _root_.D5.S3.ArithSums.GiniMeanEndpointComparison.giniMean,
      sum_highTuple_rpow 2 (1/2) 2, sum_highTuple_rpow 2 (1/2) (-1),
      sum_highTuple_rpow 2 (1/4) 2, sum_highTuple_rpow 2 (1/4) (-1)]
    norm_num [Real.rpow_neg_one, Real.rpow_two]
    exact ne_of_gt (Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num))
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@witness_comparison)
    (type_of% (realize signature
      (fun _ n t => giniMean 2 (-1) (highTuple n t 1)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.ArithSums.GiniStationaryTest.Witness.witness_comparison.information_unit
  realizationName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Witness.Comparison.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n t => giniMean 2 (-1) (highTuple n t 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GiniStationaryTest.Witness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Comparison

namespace Nonmembership
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => Set ((ℝ × ℝ) × (ℝ × ℝ)))
def actual : Realization signature := realize signature
  (fun _ _ n => Gamma n (Set.Ioi 0)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => Set.univ) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 3 ≤ n →
    (((1,0),(2,-1)) : (ℝ × ℝ) × (ℝ × ℝ)) ∉ R.readout () () n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 le_rfl (Set.mem_univ _)
def evidence : Registration arena (type_of% (@not_mem_Gamma)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨not_mem_Gamma, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 0, 3, ?_⟩
    intro he
    have hz : (((1,0),(2,-1)) : (ℝ × ℝ) × (ℝ × ℝ)) ∈ Gamma 0 (Set.Ioi 0) := by
      intro x hx
      norm_num [giniMean, _root_.D5.S3.ArithSums.GiniMeanEndpointComparison.giniMean]
    change Gamma 0 (Set.Ioi 0) = Gamma 3 (Set.Ioi 0) at he
    apply not_mem_Gamma 3 le_rfl
    rw [← he]
    exact hz
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@not_mem_Gamma)
    (type_of% (realize signature
      (fun _ _ n => Gamma n (Set.Ioi 0)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.ArithSums.GiniStationaryTest.Witness.not_mem_Gamma.information_unit
  realizationName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Witness.Nonmembership.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => Gamma n (Set.Ioi 0)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GiniStationaryTest.Witness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Nonmembership

end Reg.D5.S3.ArithSums.GiniStationaryTest.Witness
