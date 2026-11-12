import D5.S1.Words.RichWordRecurrence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Whole-word realizations with unbounded natural positions and the complete original laws. -/
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)
open _root_.D5.S1.Words.Complexity (EventuallyPeriodicWord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.RichWordRecurrence

private def spike (m : ℕ) (hm : 2 ≤ m) (t : ℕ) : Fin m :=
  if t = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

private theorem spike_failure (m : ℕ) (hm : 2 ≤ m) :
    ¬ (∀ i n, ∃ B, ∀ q, ∃ j, q ≤ j ∧ j+n ≤ q+B ∧
      factor (spike m hm) j n = factor (spike m hm) i n) := by
  intro h
  obtain ⟨B,hB⟩ := h 0 1
  obtain ⟨j,hj,_,he⟩ := hB 1
  have hjz : j ≠ 0 := by omega
  have hv := congrArg (List.map Fin.val) he
  simpa [factor, spike, hjz] using hv

private theorem nonconstant {m : ℕ} (y : ℕ → Fin m)
    (h : ¬ EventuallyPeriodicWord y) : ∃ i j, y i ≠ y j := by
  by_contra hn
  push_neg at hn
  apply h
  exact ⟨0,1,by omega,by intro t; exact hn _ _⟩

namespace source_uniform_recurrence

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 7
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => _root_.D5.S1.Words.RichWordTypeIOccurrence.word) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ => spike 7 (by omega)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i n, ∃ B, ∀ q, ∃ j, q ≤ j ∧ j+n ≤ q+B ∧
    factor (R.readout () ()) j n = factor (R.readout () ()) i n

private theorem rejected_law : ¬ arena.Law rejected := by
  exact spike_failure 7 (by omega)

def family : Registration arena (type_of% (@_root_.D5.S1.Words.RichWordRecurrence.source_uniform_recurrence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.RichWordRecurrence.source_uniform_recurrence,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    obtain ⟨i,j,hij⟩ := nonconstant _root_.D5.S1.Words.RichWordTypeIOccurrence.word _root_.D5.S1.Words.RichWordRecurrence.source_no_tail
    exact ⟨(),i,j,hij⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.RichWordRecurrence.source_uniform_recurrence) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.RichWordRecurrence.source_uniform_recurrence.__information_unit,
  realizationName := `Reg.D5.S1.Words.RichWordRecurrence.source_uniform_recurrence.family,
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
    owner := `D5.S1.Words.RichWordRecurrence, definition := none,
    coordinates := #[], readouts := #[
      { path := #["body","body","arg","body","body","arg","body","arg","arg","fn","arg","fn","fn","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body","body","arg","body","body","arg","body","arg","arg","arg","fn","fn","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end source_uniform_recurrence

namespace source_no_tail

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 7
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => _root_.D5.S1.Words.RichWordTypeIOccurrence.word) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ => (fun _ => (0 : Fin 7))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ EventuallyPeriodicWord (R.readout () ())

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨0,1,by omega,by intro t; rfl⟩

def family : Registration arena (type_of% (@_root_.D5.S1.Words.RichWordRecurrence.source_no_tail)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.RichWordRecurrence.source_no_tail,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    obtain ⟨i,j,hij⟩ := nonconstant _root_.D5.S1.Words.RichWordTypeIOccurrence.word _root_.D5.S1.Words.RichWordRecurrence.source_no_tail
    exact ⟨(),i,j,hij⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.RichWordRecurrence.source_no_tail) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.RichWordRecurrence.source_no_tail.__information_unit,
  realizationName := `Reg.D5.S1.Words.RichWordRecurrence.source_no_tail.family,
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
    owner := `D5.S1.Words.RichWordRecurrence, definition := none,
    coordinates := #[], readouts := #[
      { path := #["arg","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end source_no_tail

namespace output_uniform_recurrence

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => _root_.D5.S1.Words.RichWordOutputDecoder.x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ => spike 4 (by omega)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i n, ∃ B, ∀ q, ∃ j, q ≤ j ∧ j+n ≤ q+B ∧
    factor (R.readout () ()) j n = factor (R.readout () ()) i n

private theorem rejected_law : ¬ arena.Law rejected := by
  exact spike_failure 4 (by omega)

def family : Registration arena (type_of% (@_root_.D5.S1.Words.RichWordRecurrence.output_uniform_recurrence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.RichWordRecurrence.output_uniform_recurrence,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    obtain ⟨i,j,hij⟩ := nonconstant _root_.D5.S1.Words.RichWordOutputDecoder.x _root_.D5.S1.Words.RichWordRecurrence.output_no_tail
    exact ⟨(),i,j,hij⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.RichWordRecurrence.output_uniform_recurrence) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.RichWordRecurrence.output_uniform_recurrence.__information_unit,
  realizationName := `Reg.D5.S1.Words.RichWordRecurrence.output_uniform_recurrence.family,
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
    owner := `D5.S1.Words.RichWordRecurrence, definition := none,
    coordinates := #[], readouts := #[
      { path := #["body","body","arg","body","body","arg","body","arg","arg","fn","arg","fn","fn","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body","body","arg","body","body","arg","body","arg","arg","arg","fn","fn","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end output_uniform_recurrence

namespace output_no_tail

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => _root_.D5.S1.Words.RichWordOutputDecoder.x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ => (fun _ => (0 : Fin 4))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ EventuallyPeriodicWord (R.readout () ())

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨0,1,by omega,by intro t; rfl⟩

def family : Registration arena (type_of% (@_root_.D5.S1.Words.RichWordRecurrence.output_no_tail)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.RichWordRecurrence.output_no_tail,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    obtain ⟨i,j,hij⟩ := nonconstant _root_.D5.S1.Words.RichWordOutputDecoder.x _root_.D5.S1.Words.RichWordRecurrence.output_no_tail
    exact ⟨(),i,j,hij⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.RichWordRecurrence.output_no_tail) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.RichWordRecurrence.output_no_tail.__information_unit,
  realizationName := `Reg.D5.S1.Words.RichWordRecurrence.output_no_tail.family,
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
    owner := `D5.S1.Words.RichWordRecurrence, definition := none,
    coordinates := #[], readouts := #[
      { path := #["arg","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end output_no_tail

end Reg.D5.S1.Words.RichWordRecurrence
