import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-source count readouts with the complete original telescopes. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge (rowWeight)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
theorem actual_dependence : actual.readout () () 2 ≠ actual.readout () () 10 := by
  change (a 2 : ℤ) ≠ (a 10 : ℤ)
  have ha : (a 2 : ℤ) ≤ 60466176 := by
    have h : a 2 ≤ 6^(5*2) := by
      calc
        _ ≤ (Finset.univ : Finset (Array 2 6)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = _ := by simp
    norm_num at h
    exact_mod_cast h
  have hp : (0:ℤ) ≤ pairCount 10 := by
    unfold pairCount
    apply Finset.sum_nonneg
    intro q _
    split_ifs <;> norm_num
  have hb := source_count 10 (by decide)
  norm_num only [show (32:ℤ)^10 = 1125899906842624 by norm_num] at hb
  intro he
  rw [← he] at hb
  linarith

namespace Scanner
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 * R.readout () () n = ∑ q : Array n 3, if Anchored q then rowWeight (false,false) (word q) else 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := scanner_count 0
  have hb := h 0
  change _ at hb
  dsimp only [rejected, realize] at hb
  linarith
def family : Registration arena (type_of% @scanner_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨scanner_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 10, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@scanner_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.Scanner.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.Scanner.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Scanner

namespace Source
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_ : 2 ≤ n), 16 * R.readout () () n = (32:ℤ)^n * (pairCount n + 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := source_count 2 (by decide)
  have hb := h 2 (by decide)
  change _ at hb
  dsimp only [rejected, realize] at hb
  linarith
def family : Registration arena (type_of% @source_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 10, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@source_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.Source.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.Source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Source

namespace Chromatic
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_ : 2 ≤ n), 48 * R.readout () () n = (32:ℤ)^n * (chromaticCount n + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := chromatic_source_count 2 (by decide)
  have hb := h 2 (by decide)
  change _ at hb
  dsimp only [rejected, realize] at hb
  linarith
def family : Registration arena (type_of% @chromatic_source_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨chromatic_source_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 10, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@chromatic_source_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.Chromatic.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.Chromatic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Chromatic

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
