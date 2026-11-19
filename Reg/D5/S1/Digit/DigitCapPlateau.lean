import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.DigitCapPlateau
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audits of the plateau count and exponent. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapPlateau
open LeanInformationAudit

namespace Reg.D5.S1.Digit.DigitCapPlateau
noncomputable section

private lemma count_varies :
    count 5 4 ((2 - 1) * repunitSum 4 0) ≠ count 5 4 ((2 - 1) * repunitSum 4 1) := by
  rw [count_plateau 4 2 5 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    count_plateau 4 2 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  norm_num

private lemma exponent_varies : exponent 5 4 ≠ exponent 15 4 := by
  rw [exponent_plateau 4 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    exponent_plateau 4 4 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h ⊢
    exact h
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  intro h
  have h' := EReal.coe_injective h
  push_cast at h'
  rw [h4, div_self (by positivity)] at h'
  field_simp at h'
  linarith

namespace count_plateau
abbrev signature : Signature where
  Params := Sigma (fun _ : ℕ => Sigma (fun _ : ℕ => ℕ))
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ p m => count p.2.2 p.1 ((p.2.1 - 1) * repunitSum p.1 m)) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ ell q k m : ℕ, 2 ≤ ell → 2 ≤ q → q ≤ ell →
  (q - 1) * (ell + 1) ≤ k → k ≤ q * ell - 1 → count k ell ((q - 1) * repunitSum ell m) = q ^ m
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ell q k m : ℕ, 2 ≤ ell → 2 ≤ q → q ≤ ell →
    (q - 1) * (ell + 1) ≤ k → k ≤ q * ell - 1 → R.readout () ⟨ell, ⟨q, k⟩⟩ m = q ^ m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 2 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.DigitCapPlateau.count_plateau, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨⟨4, ⟨2, 5⟩⟩, 0, 1, count_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.DigitCapPlateau.count_plateau)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ p m => count p.2.2 p.1 ((p.2.1 - 1) * repunitSum p.1 m))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.DigitCapPlateau.count_plateau.__information_unit,
  realizationName := `Reg.D5.S1.Digit.DigitCapPlateau.count_plateau.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p m => count p.2.2 p.1 ((p.2.1 - 1) * repunitSum p.1 m)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.DigitCapPlateau, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"], stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end count_plateau

namespace exponent_plateau
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Output _ _ := EReal
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ ell k => exponent k ell) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => ⊤) (fun e => nomatch e)
def sourceStatement : Prop := ∀ ell q k : ℕ, 2 ≤ ell → 2 ≤ q → q ≤ ell →
  (q - 1) * (ell + 1) ≤ k → k ≤ q * ell - 1 →
    exponent k ell = ((Real.log q / Real.log ell : ℝ) : EReal)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ell q k : ℕ, 2 ≤ ell → 2 ≤ q → q ≤ ell →
    (q - 1) * (ell + 1) ≤ k → k ≤ q * ell - 1 →
      R.readout () ell k = ((Real.log q / Real.log ell : ℝ) : EReal)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (⊤ : EReal) = _ at hh
  exact EReal.coe_ne_top _ hh.symm
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.DigitCapPlateau.exponent_plateau, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨4, 5, 15, exponent_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.DigitCapPlateau.exponent_plateau)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ ell k => exponent k ell)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.DigitCapPlateau.exponent_plateau.__information_unit,
  realizationName := `Reg.D5.S1.Digit.DigitCapPlateau.exponent_plateau.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ ell k => exponent k ell)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.DigitCapPlateau, definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end exponent_plateau

end
end Reg.D5.S1.Digit.DigitCapPlateau
