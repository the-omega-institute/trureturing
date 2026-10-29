import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMaskRowElimination
import Reg.Support.DependentFamily

/-! Typed family evidence for complete masks on original filled prefix patterns. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
  (CutSet CutPrefixFree reachedHoles)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (cutExterior)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern Frontier fill)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells (patternTerm)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation (Term evaluate)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting (symbolicExterior)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace (Sol Diseq)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMaskRowElimination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.NativeTermUnification (Presentation)
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMaskRowElimination

structure Input (X : Type) where
  presentation : Presentation X
  depth : Nat
  pattern : Pattern depth
  name : Frontier pattern → X
  rows : List RawRow
  extra : SignedConstraints X
  valuation : X → Source

abbrev signature : Signature where
  Params := Type
  State X := Input X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := Option (RowOutput X)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s => eliminateRows s.presentation (patternTerm s.pattern s.name) s.rows s.extra)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => none)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type} (p : Presentation X) (d : Nat) (pat : Pattern d)
    (name : Frontier pat → X) (rs : List RawRow) (extra : SignedConstraints X)
    (v : X → Source),
    (∀ r ∈ rs, CutPrefixFree r.1) →
    (∀ r ∈ rs, ∀ q ∈ r.1, q.length < d) →
    (∀ (Q : CutSet) (u w : Source),
      (nativeMask Q [] u = nativeMask Q [] w ∧
        (reachedHoles Q [] u).toFinset = (reachedHoles Q [] w).toFinset) ↔
        cutExterior Q [] u = cutExterior Q [] w) ∧
    (∀ r ∈ rs, evaluate v (maskExpression (symbolicExterior r.1 [] (patternTerm pat name))) =
      nativeMask r.1 [] (fill pat (v ∘ name))) ∧
    (((∀ r ∈ rs, maskRowHolds r (fill pat (v ∘ name))) ∧ constraintsHold extra v) ↔
      ∃ o, R.readout () X ⟨p, d, pat, name, rs, extra, v⟩ = some o ∧ outputHolds o v)

private theorem actual_law : arena.Law actual := by
  intro X p d pat name rs extra v freecuts bound
  exact original_mask_row_elimination p d pat name rs extra v freecuts bound

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p := NativeTermUnification.finPresentation 0
  let pat : Pattern 1 := .inl false
  let name : Frontier pat → Fin 0 := fun x => nomatch x
  let v : Fin 0 → Source := Fin.elim0
  obtain ⟨o, ho, _⟩ := (h p 1 pat name [] ([], []) v (by simp) (by simp)).2.2.mp
    (by simp [constraintsHold, Sol, Diseq])
  change (none : Option (RowOutput (Fin 0))) = some o at ho
  cases ho

def evidence : Registration arena (type_of% (@original_mask_row_elimination)) where
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
    let pat : Pattern 1 := .inl false
    let name : Frontier pat → Fin 0 := fun x => nomatch x
    let v : Fin 0 → Source := Fin.elim0
    let t : Term (Fin 0) := .of (.inl false)
    let bad : RawRow := (∅, .of (.inl true), ∅)
    obtain ⟨o, ho, _⟩ := (complete_row_elimination p t [] ([], []) v).1.mp
      (by simp [constraintsHold, Sol, Diseq])
    refine ⟨Fin 0, ⟨p, 1, pat, name, [], ([], []), v⟩,
      ⟨p, 1, pat, name, [bad], ([], []), v⟩, ?_⟩
    change eliminateRows p (patternTerm pat name) [] ([], []) ≠
      eliminateRows p (patternTerm pat name) [bad] ([], [])
    change eliminateRows p t [] ([], []) ≠ eliminateRows p t [bad] ([], [])
    have hn : eliminateRows p t [bad] ([], []) = none := by
      simp [eliminateRows, compileRows, compileRow, bad, t,
        _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.symbolicExterior,
        matchExterior]
    rw [ho, hn]
    simp

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMaskRowElimination
