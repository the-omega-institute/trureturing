import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookWeighted
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Topology
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookWeighted.letter_length_le_weight
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ w => Statement.letterWeight w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : List Bool), w.length ≤ Statement.letterWeight w
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : List Bool), w.length ≤ R.readout () () w
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hh' := hh [false]
  norm_num [rejected,realize] at hh' 
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.letter_length_le_weight,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),[],[false],?_⟩
    norm_num [actual,realize,Statement.letterWeight]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.letter_length_le_weight)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ w => Statement.letterWeight w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Coding.letter_length_le_weight.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookWeighted.letter_length_le_weight.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ w => Statement.letterWeight w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookWeighted, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookWeighted.letter_length_le_weight

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookWeighted.codebook_finite
abbrev signature : Signature where
  Params := Unit
  State _ := Set (List Return)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ s => s.Finite) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (anchor : Bool) (K N : ℕ) (d : ℝ), (Statement.codebook anchor K N d).Finite
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (anchor : Bool) (K N : ℕ) (d : ℝ), R.readout () () (Statement.codebook anchor K N d)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh false 0 0 0
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.codebook_finite,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),∅,Set.range (fun n : ℕ => List.replicate n (⟨(1,1),by constructor <;> omega⟩ : Return)),?_⟩
    change Set.Finite ∅ ≠ Set.Finite _
    intro he
    have hf := Eq.mp he (Set.finite_empty : (∅ : Set (List Return)).Finite)
    have hi : Function.Injective (fun n : ℕ => List.replicate n (⟨(1,1),by constructor <;> omega⟩ : Return)) := by
      intro m n hmn
      simpa using congrArg List.length hmn
    exact (Set.infinite_range_of_injective hi) hf
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.codebook_finite)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ s => s.Finite) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Coding.codebook_finite.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookWeighted.codebook_finite.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ s => s.Finite) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookWeighted, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookWeighted.codebook_finite

