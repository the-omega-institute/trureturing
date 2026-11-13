import D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound factorial-index observation in the complete conjecture. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome
open _root_.D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome

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
  realize signature (fun _ _ m => F m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ m : ℕ, IsLeast {h : ℕ | 1 ≤ h ∧ 2 ^ m ∣ h.factorial} (R.readout () () m)) ∧
    S 0 = 0 ∧
    (∀ r : ℕ, IsLeast {m : ℕ | S r < m ∧ F m ≠ F (S r)} (S (r + 1))) ∧
    P 1 = 1 ∧
    (∀ i : ℕ, 2 ≤ i → IsLeast {L : ℕ | 2 ≤ L ∧ Pal i L} (P i)) ∧
    StrictMono A ∧
    (∀ i : ℕ, 1 ≤ i → (First i ↔ ∃ m : ℕ, i = A m)) ∧
    (∀ m : ℕ, 2 ≤ m → P (A (m - 1)) = A m)

private theorem rejected_failure : ¬ arena.Law rejected := by
  intro h
  have hh := (h.1 0).1.1
  change 1 ≤ (0 : ℕ) at hh
  omega

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_failure⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_failure⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change F 0 ≠ F 1
    have h0 := result.1 0
    have h1 := result.1 1
    have hf0 : F 0 = 1 := by
      have hu : F 0 ≤ 1 := h0.2 (by norm_num)
      have hl := h0.1.1
      omega
    rw [hf0]
    intro he
    have hh := h1.1.2
    rw [← he] at hh
    norm_num at hh

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Type Unit := {
  unitName := `D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome.result.__information_unit
  realizationName := `Reg.D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome
    definition := some {
      owner := `D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome
      name := `D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{ path := #["fn", "arg", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end
end Reg.D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome
