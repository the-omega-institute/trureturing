import D5.S1.Words.Palindromes.ThueMorseSharpPrefix
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound observations for the complete sharp prefix comparison. -/

open _root_.D5.S1.Words.Complexity
open _root_.D5.S1.Words.FridPrefix
open _root_.D5.S1.Words.Palindromes.PeriodDoubling
open _root_.D5.S1.Words.Palindromes.ThueMorse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Palindromes.ThueMorseSharpPrefix
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => PL (factor n 0)) (fun e => nomatch e)

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change PL (factor 0 0) ≠ PL (factor 1 0)
  have hz := prefix_signed_upper 0
  have ho := combined_prefix_signed_lower 1
  rw [Nat.cast_zero, signed_weight_arithmetic.1] at hz
  norm_num only [Nat.cast_one, signed_weight_arithmetic.2.1] at ho
  omega

abbrev upperArena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n ≤ 2 * signedWeight (n : ℤ)

def upperBad : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem upper_bad_law : ¬ upperArena.Law upperBad := by
  intro h
  have hh := h 0
  change 1 ≤ 2 * signedWeight (0 : ℤ) at hh
  rw [signed_weight_arithmetic.1] at hh
  omega

def upperFamily : Registration upperArena
    (type_of% (@_root_.D5.S1.Words.Palindromes.ThueMorse.prefix_signed_upper)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefix_signed_upper, upperBad, upper_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨upperBad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, upper_bad_law⟩
    · intro i
      exact nomatch i
  dependence := actual_dependence

abbrev sharpArena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 1 ≤ n → R.readout () () n ≤ 2 * combinedLength (factor n 0)) ∧
    (∃ n : ℕ, 1 ≤ n ∧ PL (factor n 0) = 2 * combinedLength (factor n 0) ∧
      0 < PL (factor n 0))

def sharpBad : Realization signature :=
  realize signature (fun _ _ n => 2 * combinedLength (factor n 0) + 1)
    (fun e => nomatch e)

theorem sharp_bad_law : ¬ sharpArena.Law sharpBad := by
  intro h
  have hh := h.1 1 (by decide)
  change 2 * combinedLength (factor 1 0) + 1 ≤ 2 * combinedLength (factor 1 0) at hh
  omega

def sharpFamily : Registration sharpArena
    (type_of% (@_root_.D5.S1.Words.Palindromes.ThueMorse.sharp_factor_two_prefix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_factor_two_prefix, sharpBad, sharp_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨sharpBad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, sharp_bad_law⟩
    · intro i
      exact nomatch i
  dependence := actual_dependence

def registration_upper : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Palindromes.ThueMorse.prefix_signed_upper)
    (Realization signature) Type Unit := {
  unitName := `D5.S1.Words.Palindromes.ThueMorse.prefix_signed_upper.__information_unit
  realizationName := `Reg.D5.S1.Words.Palindromes.ThueMorseSharpPrefix.upperFamily
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some { owner := `D5.S1.Words.Palindromes.ThueMorseSharpPrefix, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def registration_sharp : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Palindromes.ThueMorse.sharp_factor_two_prefix)
    (Realization signature) Type Unit := {
  unitName := `D5.S1.Words.Palindromes.ThueMorse.sharp_factor_two_prefix.__information_unit
  realizationName := `Reg.D5.S1.Words.Palindromes.ThueMorseSharpPrefix.sharpFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sharpArena⟩
  objectArena := .source ⟨sharpArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sharpArena ⟨sharpFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some { owner := `D5.S1.Words.Palindromes.ThueMorseSharpPrefix, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration_upper
#print axioms registration_sharp

end
end Reg.D5.S1.Words.Palindromes.ThueMorseSharpPrefix
