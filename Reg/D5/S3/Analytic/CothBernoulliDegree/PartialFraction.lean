import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.CothBernoulliDegree.PartialFraction
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction
open _root_.D5.S3.Analytic.CothBernoulliDegree.Defs
open _root_.D5.S3.Analytic.CothBernoulliDegree.PartialFraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev partialSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def partialActual : Realization partialSignature :=
  realize partialSignature (fun _ p t => P p.1 p.2 t) (fun e => nomatch e)
def partialBad : Realization partialSignature :=
  realize partialSignature (fun _ p t => P p.1 p.2 t + 1) (fun e => nomatch e)
def partialArena : Arena where
  signature := partialSignature
  Law R := ∀ m n : ℕ, ∀ {t : ℝ}, 0 < t →
    R.readout () ⟨m, n⟩ t = 2 * ∑' k : ℕ,
      (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
        (t ^ (m + 2 * n) / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2))
private theorem partialBad_rejected : ¬ partialArena.Law partialBad := by
  intro h
  have hb := h 0 0 (t := 1) (by norm_num)
  have ha := P_eq_tsum 0 0 (t := 1) (by norm_num)
  change P 0 0 1 + 1 = _ at hb
  linarith
private theorem p00_pos : 0 < P 0 0 1 := by
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr zero_lt_one
  have hc : Real.sinh 1 < Real.cosh 1 := Real.sinh_lt_cosh 1
  simpa [P, p] using (sub_pos.mpr ((one_lt_div hs).mpr hc))
private theorem partialDependence : ObservationalDependence partialSignature partialActual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  change P 0 0 0 ≠ P 0 0 1
  rw [show P 0 0 0 = 0 by simp [P, p]]
  exact ne_of_lt p00_pos

def partialFamily : Registration partialArena (type_of% @P_eq_tsum) where
  actual := partialActual
  bridge := Iff.rfl
  variation := ⟨P_eq_tsum, partialBad, partialBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    partialArena.Law partialActual partialBad partialBad_rejected
  dependence := partialDependence

abbrev derivSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def derivActual : Realization derivSignature :=
  realize derivSignature (fun _ p t => iteratedDeriv p.2.2 (P p.1 p.2.1) t)
    (fun e => nomatch e)
def derivBad : Realization derivSignature :=
  realize derivSignature (fun _ p t => iteratedDeriv p.2.2 (P p.1 p.2.1) t + 1)
    (fun e => nomatch e)
private theorem derivDependence : ObservationalDependence derivSignature derivActual := by
  intro i
  refine ⟨⟨0, 0, 0⟩, 0, 1, ?_⟩
  change iteratedDeriv 0 (P 0 0) 0 ≠ iteratedDeriv 0 (P 0 0) 1
  simp only [iteratedDeriv_zero]
  rw [show P 0 0 0 = 0 by simp [P, p]]
  exact ne_of_lt p00_pos

def sumArena : Arena where
  signature := derivSignature
  Law R := ∀ m n r : ℕ, ∀ {t : ℝ}, 0 < t →
    HasSum (fun k : ℕ => (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
      iteratedDeriv r (fun s : ℝ =>
        s ^ (m + 2 * n) / (s ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) t)
      (R.readout () ⟨m, n, r⟩ t / 2)
private theorem sumBad_rejected : ¬ sumArena.Law derivBad := by
  intro h
  have he := (hasSum_iteratedDeriv_P 0 0 0 (t := 1) (by norm_num)).unique
    (h 0 0 0 (t := 1) (by norm_num))
  change iteratedDeriv 0 (P 0 0) 1 / 2 = (iteratedDeriv 0 (P 0 0) 1 + 1) / 2 at he
  linarith

def sumFamily : Registration sumArena (type_of% @hasSum_iteratedDeriv_P) where
  actual := derivActual
  bridge := Iff.rfl
  variation := ⟨hasSum_iteratedDeriv_P, derivBad, sumBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sumArena.Law derivActual derivBad sumBad_rejected
  dependence := derivDependence

def derivArena : Arena where
  signature := derivSignature
  Law R := ∀ m n r : ℕ, ∀ {t : ℝ}, 0 < t →
    R.readout () ⟨m, n, r⟩ t = 2 * ∑' k : ℕ,
      (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
        iteratedDeriv r (fun s : ℝ =>
          s ^ (m + 2 * n) / (s ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) t
private theorem derivBad_rejected : ¬ derivArena.Law derivBad := by
  intro h
  have hb := h 0 0 0 (t := 1) (by norm_num)
  have ha := iteratedDeriv_P 0 0 0 (t := 1) (by norm_num)
  change iteratedDeriv 0 (P 0 0) 1 + 1 = _ at hb
  linarith

def derivFamily : Registration derivArena (type_of% @iteratedDeriv_P) where
  actual := derivActual
  bridge := Iff.rfl
  variation := ⟨iteratedDeriv_P, derivBad, derivBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    derivArena.Law derivActual derivBad derivBad_rejected
  dependence := derivDependence

noncomputable def partialAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@P_eq_tsum) (Realization partialSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction.partialUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction.partialFamily
  realizationSource := none
  generated := false
  arena := .source ⟨partialArena⟩
  objectArena := .source ⟨partialArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source partialArena ⟨partialFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize partialSignature (fun _ p t => P p.1 p.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.PartialFraction
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms partialAudit

noncomputable def sumAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasSum_iteratedDeriv_P) (Realization derivSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction.sumUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction.sumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sumArena⟩
  objectArena := .source ⟨sumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumArena ⟨sumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivSignature (fun _ p t => iteratedDeriv p.2.2 (P p.1 p.2.1) t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.PartialFraction
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sumAudit

noncomputable def derivAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@iteratedDeriv_P) (Realization derivSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction.derivUnit
  realizationName := `Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction.derivFamily
  realizationSource := none
  generated := false
  arena := .source ⟨derivArena⟩
  objectArena := .source ⟨derivArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source derivArena ⟨derivFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivSignature (fun _ p t => iteratedDeriv p.2.2 (P p.1 p.2.1) t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CothBernoulliDegree.PartialFraction
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms derivAudit

end
end Reg.D5.S3.Analytic.CothBernoulliDegree.PartialFraction
