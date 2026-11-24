import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers (C column_power)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations (Column columnV)

abbrev signature : DependentFamily.Signature where
  Params := Σ _ : Nat, Nat
  State := fun k => Column k.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ k p => ((C k.1)^k.2).mulVec (1 : Column k.1 → Int) p)
    (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (h m : Nat) (p : Column h),
    R.readout () ⟨h, m⟩ p = (columnV m p : Int)

abbrev sourceScope := type_of% (@column_power)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Int)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro bad
  have impossible := bad 0 0 (fun _ => 0)
  change (0 : Int) = (columnV 0 (fun _ : Fin 1 => (0 : Fin 3)) : Int) at impossible
  simp [columnV] at impossible

def constantColumn : Column 1 := fun _ => 0
def mixedColumn : Column 1 := fun i => if i.val = 0 then 0 else 1

theorem constant_count : columnV 1 constantColumn = 4 := by decide +kernel
theorem mixed_count : columnV 1 mixedColumn = 1 := by decide +kernel

theorem power_dependence :
    actual.readout () ⟨1, 1⟩ constantColumn ≠ actual.readout () ⟨1, 1⟩ mixedColumn := by
  change ((C 1)^1).mulVec (1 : Column 1 → Int) constantColumn ≠
    ((C 1)^1).mulVec (1 : Column 1 → Int) mixedColumn
  rw [column_power, column_power, constant_count, mixed_count]
  decide

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp column_power, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j distinct
      exact (distinct (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    exact ⟨⟨1, 1⟩, constantColumn, mixedColumn, power_dependence⟩

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@column_power) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers.column_power.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ k p => ((C k.1)^k.2).mulVec (1 : Column k.1 → Int) p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

open scoped BigOperators
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers
  (column_continuations column_count)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport (stripGraph)
open private tailGood from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations

namespace ColumnContinuations

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (h m : Nat) (p : Column h),
    R.readout () ⟨h, m⟩ p = (Nat.card {f : Fin m → Column h // tailGood p f} : Int)

abbrev sourceScope := type_of% (@column_continuations)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro bad
  let p : Column 0 := fun _ => 0
  have erasedZero := bad 0 0 p
  change (0 : Int) = (Nat.card {f : Fin 0 → Column 0 // tailGood p f} : Int) at erasedZero
  have actualZero := column_continuations 0 0 p
  simp only [pow_zero, Matrix.one_mulVec, Pi.one_apply] at actualZero
  exact Int.zero_ne_one (erasedZero.trans actualZero.symm)

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp column_continuations, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j distinct
      exact (distinct (@Subsingleton.elim Unit _ j i)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro i
    cases i
    exact ⟨⟨1, 1⟩, constantColumn, mixedColumn, power_dependence⟩

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@column_continuations) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers.column_continuations.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers.ColumnContinuations.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ k p => ((C k.1)^k.2).mulVec (1 : Column k.1 → Int) p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ColumnContinuations

namespace ColumnCount

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (h m : Nat),
    (Nat.card ((stripGraph true h m).Coloring (Fin 3)) : Int) =
      ∑ p : Column h, R.readout () ⟨h, m⟩ p

abbrev sourceScope := type_of% (@column_count)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro bad
  have erasedZero := bad 0 0
  change (Nat.card ((stripGraph true 0 0).Coloring (Fin 3)) : Int) =
    ∑ _ : Column 0, (0 : Int) at erasedZero
  have actualZero := column_count 0 0
  simp only [Finset.sum_const_zero] at erasedZero
  simp only [pow_zero, Matrix.one_mulVec, Pi.one_apply] at actualZero
  have sumNonzero : (∑ _ : Column 0, (1 : Int)) ≠ 0 := by decide +kernel
  exact sumNonzero (actualZero.symm.trans erasedZero)

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp column_count, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j distinct
      exact (distinct (@Subsingleton.elim Unit _ j i)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro i
    cases i
    exact ⟨⟨1, 1⟩, constantColumn, mixedColumn, power_dependence⟩

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@column_count) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers.column_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers.ColumnCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ k p => ((C k.1)^k.2).mulVec (1 : Column k.1 → Int) p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ColumnCount

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers
  (Word wordTransfer word_continuations word_count)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport (Row)
open private word_power from
  D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

namespace Words

abbrev signature : DependentFamily.Signature where
  Params := Σ _ : Bool, Σ _ : Nat, Nat
  State := fun k => Word k.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ k p => ((wordTransfer k.1 k.2.1)^k.2.2).mulVec (1 : Word k.2.1 → Int) p)
    (fun e => nomatch e)

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Int)) (fun e => nomatch e)

def returningWord : Word 2 := ⟨![0, 1, 0], by decide +kernel⟩
def distinctWord : Word 2 := ⟨![0, 1, 2], by decide +kernel⟩

theorem returning_count :
    ((wordTransfer false 2)^1).mulVec (1 : Word 2 → Int) returningWord = 5 := by
  rw [word_power]
  decide +kernel

theorem distinct_count :
    ((wordTransfer false 2)^1).mulVec (1 : Word 2 → Int) distinctWord = 4 := by
  rw [word_power]
  decide +kernel

theorem readout_dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨false, 2, 1⟩, returningWord, distinctWord, ?_⟩
  change ((wordTransfer false 2)^1).mulVec (1 : Word 2 → Int) returningWord ≠
    ((wordTransfer false 2)^1).mulVec (1 : Word 2 → Int) distinctWord
  rw [returning_count, distinct_count]
  decide

namespace Continuations

open private tailGood from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (d : Bool) (k m : Nat) (p : Word k),
    R.readout () ⟨d, k, m⟩ p = (Nat.card {f : Fin m → Row k // tailGood d p.val f} : Int)

abbrev sourceScope := type_of% (@word_continuations)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro bad
  have erasedOne := bad false 2 1 returningWord
  have actualOne := word_continuations false 2 1 returningWord
  rw [returning_count] at actualOne
  exact (by decide : (0 : Int) ≠ 5) (erasedOne.trans actualOne.symm)

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp word_continuations, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j distinct
      exact (distinct (@Subsingleton.elim Unit _ j i)).elim
    · intro anchor
      exact nomatch anchor
  dependence := readout_dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@word_continuations) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers.word_continuations.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers.Words.Continuations.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ k p => ((wordTransfer k.1 k.2.1)^k.2.2).mulVec (1 : Word k.2.1 → Int) p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continuations

namespace Count

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (d : Bool) (k m : Nat),
    (Nat.card ((stripGraph d m k).Coloring (Fin 3)) : Int) =
      ∑ p : Word k, R.readout () ⟨d, k, m⟩ p

abbrev sourceScope := type_of% (@word_count)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro bad
  have erasedZero := bad false 0 0
  change (Nat.card ((stripGraph false 0 0).Coloring (Fin 3)) : Int) =
    ∑ _ : Word 0, (0 : Int) at erasedZero
  have actualZero := word_count false 0 0
  simp only [Finset.sum_const_zero] at erasedZero
  simp only [pow_zero, Matrix.one_mulVec, Pi.one_apply] at actualZero
  have sumNonzero : (∑ _ : Word 0, (1 : Int)) ≠ 0 := by decide +kernel
  exact sumNonzero (actualZero.symm.trans erasedZero)

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp word_count, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j distinct
      exact (distinct (@Subsingleton.elim Unit _ j i)).elim
    · intro anchor
      exact nomatch anchor
  dependence := readout_dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@word_count) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers.word_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers.Words.Count.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ k p => ((wordTransfer k.1 k.2.1)^k.2.2).mulVec (1 : Word k.2.1 → Int) p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Count

end Words

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers
