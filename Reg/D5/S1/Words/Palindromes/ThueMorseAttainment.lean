import D5.S1.Words.Palindromes.ThueMorseAttainment
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.Complexity
open _root_.D5.S1.Words.Palindromes.PeriodDoubling
open _root_.D5.S1.Words.Palindromes.ThueMorse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Palindromes.ThueMorseAttainment
noncomputable section
open Classical

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
  realize signature (fun _ _ n => combinedLength (factor n 0)) (fun e => nomatch e)
def zeroBad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def successorBad : Realization signature :=
  realize signature (fun _ _ n => _root_.D5.S1.Words.FridPrefix.PL (factor n 0) + 1)
    (fun e => nomatch e)

abbrev familyArena : Arena where
  signature := signature
  Law R := ∀ m, signedWeight (attainingLength m : ℤ) = m + 1 ∧
    R.readout () () (attainingLength m) = m + 1 ∧
    _root_.D5.S1.Words.FridPrefix.PL (factor (attainingLength m) 0) = m + 1

private theorem zero_bad_law : ¬ familyArena.Law zeroBad := by
  intro h
  have hh : (0 : ℕ) = 1 := (h 0).2.1
  omega

private theorem actual_dependence : ∀ i : Unit, ∃ (p : Unit) (s t : ℕ),
    actual.readout p i s ≠ actual.readout p i t := by
  intro i
  refine ⟨(), attainingLength 0, attainingLength 1, ?_⟩
  change combinedLength (factor (attainingLength 0) 0) ≠
    combinedLength (factor (attainingLength 1) 0)
  rw [(family_attains 0).2.1, (family_attains 1).2.1]
  decide

def familyProof : Registration familyArena (familyArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨family_attains, zeroBad, zero_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨zeroBad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, zero_bad_law⟩
    · intro i
      exact nomatch i
  dependence := actual_dependence

abbrev wholeArena : Arena where
  signature := signature
  Law R := ∀ K : ℕ, 1 ≤ K → ∃ n : ℕ, 1 ≤ n ∧
    R.readout () () n = _root_.D5.S1.Words.FridPrefix.PL (factor n 0) ∧
    K ≤ _root_.D5.S1.Words.FridPrefix.PL (factor n 0)

private theorem successor_bad_law : ¬ wholeArena.Law successorBad := by
  intro h
  obtain ⟨n, _, hn, _⟩ := h 1 (by omega)
  change _root_.D5.S1.Words.FridPrefix.PL (factor n 0) + 1 =
    _root_.D5.S1.Words.FridPrefix.PL (factor n 0) at hn
  omega

def wholeProof : Registration wholeArena (wholeArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unbounded_equal_cost, successorBad, successor_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨successorBad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl,
        successor_bad_law⟩
    · intro i
      exact nomatch i
  dependence := actual_dependence

noncomputable def registration_family : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Palindromes.ThueMorse.family_attains)
    (type_of% (realize.{0,0,0,0,0} signature actual.readout actual.anchor)) Unit Unit := {
  unitName := .str (.str `D5.S1.Words.Palindromes.ThueMorse.family_attains
    "Reg.D5.S1.Words.Palindromes.ThueMorseAttainment/familyArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Words.Palindromes.ThueMorseAttainment.familyProof
  realizationSource := none
  generated := false
  arena := .source ⟨familyArena⟩
  objectArena := .source ⟨familyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source familyArena ⟨familyProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Words.Palindromes.ThueMorseAttainment,
    definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_whole : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Palindromes.ThueMorse.unbounded_equal_cost)
    (type_of% (realize.{0,0,0,0,0} signature actual.readout actual.anchor)) Unit Unit := {
  unitName := .str (.str `D5.S1.Words.Palindromes.ThueMorse.unbounded_equal_cost
    "Reg.D5.S1.Words.Palindromes.ThueMorseAttainment/wholeArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Words.Palindromes.ThueMorseAttainment.wholeProof
  realizationSource := none
  generated := false
  arena := .source ⟨wholeArena⟩
  objectArena := .source ⟨wholeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wholeArena ⟨wholeProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Words.Palindromes.ThueMorseAttainment,
    definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "body", "arg", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration_family
#print axioms registration_whole
end
end Reg.D5.S1.Words.Palindromes.ThueMorseAttainment
