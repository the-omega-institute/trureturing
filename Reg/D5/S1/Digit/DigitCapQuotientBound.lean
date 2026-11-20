import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.DigitCapQuotientBound
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audit of the all-radix quotient-digit counting bound. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapQuotientBound
open LeanInformationAudit

namespace Reg.D5.S1.Digit.DigitCapQuotientBound
noncomputable section

private lemma count_varies : count 5 4 (repunit 0) ≠ count 5 4 (repunit 1) := by
  rw [count_repunit 5 0 (by norm_num) (by norm_num),
    count_repunit 5 1 (by norm_num) (by norm_num)]
  norm_num

namespace count_le_pow
abbrev signature : Signature where
  Params := Sigma (fun _ : ℕ => ℕ)
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ p n => count p.2 p.1 n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 3) (fun e => nomatch e)
def sourceStatement : Prop := ∀ ell q m k n : ℕ, 2 ≤ ell → 1 ≤ q → k ≤ q * ell - 1 →
  n < ell ^ (m + 1) → count k ell n ≤ q ^ m
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ell q m k n : ℕ, 2 ≤ ell → 1 ≤ q → k ≤ q * ell - 1 →
    n < ell ^ (m + 1) → R.readout () ⟨ell, k⟩ n ≤ q ^ m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 1 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.DigitCapQuotientBound.count_le_pow, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨⟨4, 5⟩, repunit 0, repunit 1, count_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.DigitCapQuotientBound.count_le_pow)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p n => count p.2 p.1 n)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.DigitCapQuotientBound.count_le_pow.__information_unit,
  realizationName := `Reg.D5.S1.Digit.DigitCapQuotientBound.count_le_pow.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p n => count p.2 p.1 n)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.DigitCapQuotientBound, definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"], stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end count_le_pow

end
end Reg.D5.S1.Digit.DigitCapQuotientBound
