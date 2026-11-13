import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
import Reg.Support.SingleDependentReadout

/-! Source-faithful dependent-family audits of the long-division statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
open _root_.D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature (ℕ × ℕ × ℕ)
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p n => longDivisionPrefix p.1 p.2.1 p.2.2 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ b p q n : ℕ,
    q * R.readout () (b,p,q) n + remainder b p q n = b ^ n * p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := h 2 0 1 0
  norm_num [rejected, realize, remainder] at hi

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(2,1,3), 0, 2, ?_⟩
  change longDivisionPrefix 2 1 3 0 ≠ longDivisionPrefix 2 1 3 2
  decide

def family : Registration arena (type_of% (@long_division_invariant)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨long_division_invariant, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@long_division_invariant) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient.long_division_invariant.__information_unit
  realizationName := `Reg.D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => longDivisionPrefix p.1 p.2.1 p.2.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

def rejectedZero : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev valueArena : Arena where
  signature := signature
  Law R := ∀ {b p q : ℕ}, 1 < b → p < q →
    HasSum (fun n => (digit b p q n : ℝ) / (b : ℝ) ^ (n + 1)) ((p : ℝ) / q) ∧
    Filter.Tendsto (fun n => (R.readout () (b,p,q) n : ℝ) / (b : ℝ) ^ n)
      Filter.atTop (nhds ((p : ℝ) / q))

private theorem value_rejected_law : ¬ valueArena.Law rejectedZero := by
  intro h
  have hi : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
      Filter.atTop (nhds (1 / 2)) := by
    simpa [rejectedZero, realize] using
      (h (b := 2) (p := 1) (q := 2) (by decide) (by decide)).2
  have he := tendsto_nhds_unique (tendsto_const_nhds (x := (0 : ℝ))) hi
  norm_num at he

def valueFamily : Registration valueArena (type_of% (@long_division_value)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@long_division_value, rejectedZero, value_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    valueArena.Law actual rejectedZero value_rejected_law
  dependence := dependence

abbrev periodArena : Arena where
  signature := signature
  Law R := ∀ {b p q : ℕ}, 1 < b → p < q → ∀ L : ℕ, q ∣ b ^ L - 1 →
    Function.Periodic (digit b p q) L ∧
      ((b : ℝ) ^ L - 1) * ((p : ℝ) / q) = (R.readout () (b,p,q) L : ℝ)

private theorem period_rejected_law : ¬ periodArena.Law rejected := by
  intro h
  have hi := (h (b := 2) (p := 0) (q := 1) (by decide) (by decide) 0 (by decide)).2
  norm_num [rejected, realize] at hi

def periodFamily : Registration periodArena (type_of% (@long_division_period)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@long_division_period, rejected, period_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    periodArena.Law actual rejected period_rejected_law
  dependence := dependence

def valueRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@long_division_value) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient.long_division_value.__information_unit
  realizationName := `Reg.D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient.valueFamily
  realizationSource := none
  generated := false
  arena := .source ⟨valueArena⟩
  objectArena := .source ⟨valueArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source valueArena ⟨valueFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => longDivisionPrefix p.1 p.2.1 p.2.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

def periodRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@long_division_period) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient.long_division_period.__information_unit
  realizationName := `Reg.D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient.periodFamily
  realizationSource := none
  generated := false
  arena := .source ⟨periodArena⟩
  objectArena := .source ⟨periodArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source periodArena ⟨periodFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => longDivisionPrefix p.1 p.2.1 p.2.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }


#print axioms valueFamily
#print axioms periodFamily
end Reg.D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
