import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Invariants.MatharA000159Recurrence
import Reg.Support.SingleDependentReadout
namespace Reg.D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open _root_.D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)
def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ n : ℕ, 9 ≤ n →
      2 * (-252307 * (n : ℚ) + 1041077) * R.readout () () n +
      (504614 * (n : ℚ) ^ 2 - 3362985 * (n : ℚ) + 5118150) * R.readout () () (n - 1) +
      (1280831 * (n : ℚ) ^ 2 - 7397886 * (n : ℚ) + 6461565) * R.readout () () (n - 2) +
      (746598 * (n : ℚ) ^ 2 - 2913543 * (n : ℚ) - 1336090) * R.readout () () (n - 3) +
      (-405481 * (n : ℚ) ^ 2 + 6175011 * (n : ℚ) - 15469320) * R.readout () () (n - 4) +
      (-375862 * (n : ℚ) ^ 2 + 4098537 * (n : ℚ) - 8846430) * R.readout () () (n - 5) +
      2 * (-187931 * (n : ℚ) + 560630) * R.readout () () (n - 6) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 9 (by decide)
  change (2 * (-252307 * (9 : ℚ) + 1041077) * 1 +
    (504614 * (9 : ℚ)^2 - 3362985 * 9 + 5118150) * 1 +
    (1280831 * (9 : ℚ)^2 - 7397886 * 9 + 6461565) * 1 +
    (746598 * (9 : ℚ)^2 - 2913543 * 9 - 1336090) * 1 +
    (-405481 * (9 : ℚ)^2 + 6175011 * 9 - 15469320) * 1 +
    (-375862 * (9 : ℚ)^2 + 4098537 * 9 - 8846430) * 1 +
    2 * (-187931 * (9 : ℚ) + 560630) * 1 = 0) at he
  norm_num at he

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 3, 4, ?_⟩
    change a 3 ≠ a 4
    norm_num [a, U, Finset.sum_range_succ, sub_pow, Nat.choose, mul_assoc,
      Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_ofNat_mul, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Invariants.MatharA000159Recurrence.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Invariants.MatharA000159Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Invariants.MatharA000159Recurrence
    definition := some {
      owner := `D5.S1.Recurrence.Invariants.MatharA000159Recurrence
      name := `D5.S1.Recurrence.Invariants.MatharA000159Recurrence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S1.Recurrence.Invariants.MatharA000159Recurrence
