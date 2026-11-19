import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.DigitCapLowerExponent
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audit of the singleton representation count. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapLowerExponent
open LeanInformationAudit

namespace Reg.D5.S1.Digit.DigitCapLowerExponent
noncomputable section

private lemma count_zero_cap_varies : count 0 4 (4 ^ 0 - 1) ≠ count 0 4 (4 ^ 1 - 1) := by
  have he : IsEmpty (Partitions 0 4 3) := ⟨by
    intro a
    have hz : a.val = 0 := by
      ext i
      have h := a.property.1 i
      simpa using (show a.val i = 0 by omega)
    have hw := a.property.2
    rw [hz] at hw
    simp [weight] at hw⟩
  have h3 : count 0 4 3 = 0 := @Nat.card_of_isEmpty _ he
  have h0 : count 0 4 0 ≠ 0 := by
    have hf := partitions_finite 0 4 0 (by norm_num)
    have hne : Nonempty (Partitions 0 4 0) := ⟨⟨0, by simp, by simp [weight]⟩⟩
    exact Nat.pos_iff_ne_zero.mp Nat.card_pos
  norm_num
  rw [h3]
  exact h0

namespace count_pow_sub_one
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
  (fun _ p s => count p.2 p.1 (p.1 ^ s - 1)) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ ell k s : ℕ, 2 ≤ ell → ell - 1 ≤ k → k ≤ 2 * ell - 2 →
  count k ell (ell ^ s - 1) = 1
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ell k s : ℕ, 2 ≤ ell → ell - 1 ≤ k → k ≤ 2 * ell - 2 →
    R.readout () ⟨ell, k⟩ s = 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.DigitCapLowerExponent.count_pow_sub_one, rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨⟨4, 0⟩, 0, 1, count_zero_cap_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.DigitCapLowerExponent.count_pow_sub_one)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p s => count p.2 p.1 (p.1 ^ s - 1))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.DigitCapLowerExponent.count_pow_sub_one.__information_unit,
  realizationName := `Reg.D5.S1.Digit.DigitCapLowerExponent.count_pow_sub_one.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p s => count p.2 p.1 (p.1 ^ s - 1))
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.DigitCapLowerExponent, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end count_pow_sub_one

end
end Reg.D5.S1.Digit.DigitCapLowerExponent
