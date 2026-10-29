import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination
import Reg.Support.DependentFamily

/-! Typed audit mirror for the exact symbolic exterior matcher. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation (Term)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
  (SymbolicExterior exteriorFill)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (HoleExterior)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination

abbrev signature : Signature where
  Params := Type
  State X := SymbolicExterior X × HoleExterior × (X → Source)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := Option (List (X × Term X))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s => match s with | ⟨p, u, v⟩ => matchExterior p u)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => none)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type} (p : SymbolicExterior X) (u : HoleExterior)
    (v : X → Source),
      exteriorFill v p = u ↔
        ∃ bs, R.readout () X ⟨p, u, v⟩ = some bs ∧ bindingHolds v bs

private theorem actual_law : arena.Law actual := by
  intro X p u v
  exact exterior_match_exact p u v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : SymbolicExterior Unit := .of (.inl (.inr ()))
  let u : HoleExterior := FreeMagma.map Sum.inl (.of false)
  let v : Unit → Source := fun _ => .of false
  have he : exteriorFill v p = u := by rfl
  obtain ⟨bs, hb, _⟩ := (h p u v).mp he
  change (none : Option (List (Unit × Term Unit))) = some bs at hb
  cases hb

def evidence : Registration arena (type_of% (@exterior_match_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let p : SymbolicExterior Unit := .of (.inl (.inl false))
    let u₁ : HoleExterior := .of (.inl false)
    let u₂ : HoleExterior := .of (.inl true)
    let v : Unit → Source := fun _ => .of false
    refine ⟨Unit, ⟨p, u₁, v⟩, ⟨p, u₂, v⟩, ?_⟩
    change some [] ≠ (none : Option (List (Unit × Term Unit)))
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration
      (@exterior_match_exact)
      (type_of% (realize signature
        (fun _ _ s => match s with | ⟨p, u, v⟩ => matchExterior p u)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination.unit_exterior_match_exact,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ s => match s with | ⟨p, u, v⟩ => matchExterior p u)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination


open _root_.NativeTermUnification (Presentation)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace (Sol Diseq)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting (symbolicRecord)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery (CutPrefixFree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (literalRecord)

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination.CompleteRows

abbrev signature : Signature where
  Params := Type
  State X := Presentation X × Term X × List RawRow × SignedConstraints X × (X → Source)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := Option (RowOutput X)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s => eliminateRows s.1 s.2.1 s.2.2.1 s.2.2.2.1)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => none)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type} (p : Presentation X) (t : Term X)
    (rs : List RawRow) (extra : SignedConstraints X) (v : X → Source),
    (((∀ r ∈ rs, symbolicRecord r.1 t v = r.2) ∧ constraintsHold extra v) ↔
      ∃ o, R.readout () X ⟨p, t, rs, extra, v⟩ = some o ∧ outputHolds o v) ∧
    ∀ (d : Nat) (pat : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.Pattern d)
      (name : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.Frontier pat → X),
      t = _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells.patternTerm pat name →
      (∀ r ∈ rs, CutPrefixFree r.1) →
      (∀ r ∈ rs, ∀ q ∈ r.1, q.length < d) →
      (((∀ r ∈ rs, literalRecord r.1
        (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.fill pat (v ∘ name)) = r.2) ∧
        constraintsHold extra v) ↔
        ∃ o, R.readout () X ⟨p, t, rs, extra, v⟩ = some o ∧ outputHolds o v)

private theorem actual_law : arena.Law actual := by
  intro X p t rs extra v
  exact complete_row_elimination p t rs extra v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p := NativeTermUnification.finPresentation 0
  let t : Term (Fin 0) := .of (.inl false)
  let v : Fin 0 → Source := Fin.elim0
  obtain ⟨o, ho, _⟩ := (h p t [] ([], []) v).1.mp
    (by simp [constraintsHold, Sol, Diseq])
  change (none : Option (RowOutput (Fin 0))) = some o at ho
  cases ho

def evidence : Registration arena (type_of% (@complete_row_elimination)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let p := NativeTermUnification.finPresentation 0
    let t : Term (Fin 0) := .of (.inl false)
    let v : Fin 0 → Source := Fin.elim0
    let bad : RawRow := (∅, .of (.inl true), ∅)
    obtain ⟨o, ho, _⟩ := (complete_row_elimination p t [] ([], []) v).1.mp
      (by simp [constraintsHold, Sol, Diseq])
    refine ⟨Fin 0, ⟨p, t, [], ([], []), v⟩, ⟨p, t, [bad], ([], []), v⟩, ?_⟩
    change eliminateRows p t [] ([], []) ≠ eliminateRows p t [bad] ([], [])
    have hn : eliminateRows p t [bad] ([], []) = none := by
      simp [eliminateRows, compileRows, compileRow, bad, t,
        _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.symbolicExterior,
        matchExterior]
    rw [ho, hn]
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration
      (@complete_row_elimination)
      (type_of% (realize signature
        (fun _ _ s => eliminateRows s.1 s.2.1 s.2.2.1 s.2.2.2.1)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination.unit_complete_row_elimination,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination.CompleteRows.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ s => eliminateRows s.1 s.2.1 s.2.2.1 s.2.2.2.1)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination.CompleteRows
