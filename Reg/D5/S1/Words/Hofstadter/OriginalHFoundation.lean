import D5.S1.Words.Hofstadter.OriginalHFoundation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open _root_.D5.S1.Words.Hofstadter.OriginalHFoundation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Hofstadter.OriginalHFoundation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Numerical

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => H n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsOriginalH (R.readout false ()) ∧
    ∀ f, IsOriginalH f → f = R.readout true ()

def rejectedAt (i : Bool) : Realization signature :=
  realize signature (fun j _ n => if j = i then 0 else H n) (fun e => nomatch e)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejectedAt i) := by
  intro h
  cases i with
  | false =>
    have he := h.1.2 0
    norm_num [rejectedAt, realize] at he
  | true =>
    have he := congrFun (h.2 H h_characterization.1) 1
    have hn : H 1 ≠ 0 := by decide
    exact hn he

def family : Registration arena (type_of% h_characterization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨h_characterization, rejectedAt false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, rfl, rejected_law i⟩
      intro j hj
      simp [actual, rejectedAt, realize, hj]
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change H 0 ≠ H 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    h_characterization (type_of% actual) (ℕ → ℕ) Unit := {
  unitName := `D5.S1.Words.Hofstadter.OriginalHFoundation.h_characterization.__information_unit,
  realizationName := `Reg.D5.S1.Words.Hofstadter.OriginalHFoundation.Numerical.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.Hofstadter.OriginalHFoundation, definition := none,
    coordinates := #[],
    readouts := #[
      { path := #["fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["arg", "body", "body", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Numerical

namespace InfiniteWord

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output i _ := match i with
    | false => Letter
    | true => List Letter
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ i, ℕ → signature.Output i ()
  | false => word
  | true => block

def actual : Realization signature :=
  realize signature (fun i _ => actualReadout i) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsOriginalWord (R.readout false ()) ∧
    (∀ x, IsOriginalWord x → x = R.readout false ()) ∧
    (∀ k, k + 1 ≤ (R.readout true () k).length) ∧
    (∀ n k, n ≤ (R.readout true () k).length →
      wordPrefix (R.readout false ()) n = (R.readout true () k).take n)

def rejectedValue : ∀ i, ℕ → signature.Output i ()
  | false => fun _ => .one
  | true => fun _ => []

def rejectedAt (i : Bool) : Realization signature :=
  realize signature
    (fun j _ n => if j = i then rejectedValue j n else actualReadout j n)
    (fun e => nomatch e)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejectedAt i) := by
  intro h
  cases i with
  | false =>
    have he := h.1.1
    change Letter.one = Letter.three at he
    cases he
  | true =>
    have he := h.2.2.1 0
    exact (by decide : ¬ (1 ≤ (0 : ℕ))) he

def family : Registration arena (type_of% word_characterization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨word_characterization, rejectedAt false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, rfl, rejected_law i⟩
      intro j hj
      simp [actual, rejectedAt, realize, hj]
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    cases i
    · change word 0 ≠ word 1
      decide
    · change block 0 ≠ block 1
      decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    word_characterization (type_of% actual) (ℕ → Letter) Unit := {
  unitName := `D5.S1.Words.Hofstadter.OriginalHFoundation.word_characterization.__information_unit,
  realizationName := `Reg.D5.S1.Words.Hofstadter.OriginalHFoundation.InfiniteWord.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.Hofstadter.OriginalHFoundation, definition := none,
    coordinates := #[],
    readouts := #[
      { path := #["arg", "arg", "fn", "arg", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end InfiniteWord

namespace PrefixIdentity

abbrev signature : Signature where
  Params := ℕ → Letter
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : Bool → (ℕ → Letter) → ℕ → ℕ
  | false, _, n => H n
  | true, x, n => (wordPrefix x n).count .one

def actual : Realization signature :=
  realize signature actualReadout (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x, IsOriginalWord x → ∀ n,
    R.readout false x n + R.readout true x n = n

def rejectedAt (i : Bool) : Realization signature :=
  realize signature (fun j x n => if j = i then 0 else actualReadout j x n)
    (fun e => nomatch e)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejectedAt i) := by
  intro h
  cases i with
  | false =>
    have he := h word word_characterization.1 1
    have hn : ¬ ((rejectedAt false).readout false word 1 +
      (rejectedAt false).readout true word 1 = 1) := by decide
    exact hn he
  | true =>
    have he := h word word_characterization.1 2
    have hn : ¬ ((rejectedAt true).readout false word 2 +
      (rejectedAt true).readout true word 2 = 2) := by decide
    exact hn he

def family : Registration arena (type_of% original_h_morphic_prefix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_h_morphic_prefix, rejectedAt false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, rfl, rejected_law i⟩
      intro j hj
      simp [actual, rejectedAt, realize, hj]
    · intro e; exact nomatch e
  dependence := by
    intro i
    cases i
    · refine ⟨word, 0, 1, ?_⟩
      decide
    · refine ⟨word, 0, 2, ?_⟩
      decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    original_h_morphic_prefix (type_of% actual) (ℕ → ℕ) Unit := {
  unitName := `D5.S1.Words.Hofstadter.OriginalHFoundation.original_h_morphic_prefix.__information_unit,
  realizationName := `Reg.D5.S1.Words.Hofstadter.OriginalHFoundation.PrefixIdentity.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.Hofstadter.OriginalHFoundation, definition := none,
    coordinates := #[0],
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end PrefixIdentity

end Reg.D5.S1.Words.Hofstadter.OriginalHFoundation
