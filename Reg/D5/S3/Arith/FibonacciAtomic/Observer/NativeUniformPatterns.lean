import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.Observer
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (Pattern History)
open NativeHistoryCells (Patterns Variables)
open NativeWholeRowService (classList variableList presentation)
open NativeTermUnification (finName)

abbrev patternsSignature : Signature where
  Params := Unit
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List PatternWord
  Anchor := Empty
  finiteAnchor := inferInstance

def patternsActual : Realization patternsSignature := realize patternsSignature
  (fun _ _ => fun d => patternWords d) (fun e => nomatch e)

def patternsRejected : Realization patternsSignature := realize patternsSignature
  (fun _ _ _ => []) (fun e => nomatch e)

abbrev patternsArena : Arena where
  signature := patternsSignature
  Law R := Primrec (R.readout () ()) ∧ ∀ d, R.readout () () d = (NativeWholeRowService.patternList d).map patternWord

private theorem patterns_rejected : ¬ patternsArena.Law patternsRejected := by
  intro h
  have bad := h.2 0
  rw [← uniform_pattern_words.2 0] at bad
  cases bad

def patternsEvidence : Registration patternsArena (patternsArena.Law patternsActual) where
  actual := patternsActual
  bridge := Iff.rfl
  variation := ⟨uniform_pattern_words,patternsRejected,patterns_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨patternsRejected,?_,rfl,patterns_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),0,1,?_⟩
    change patternWords 0 ≠ patternWords 1
    decide

abbrev frontierSignature : Signature where
  Params := Unit
  State := fun _ => PatternWord
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option (List ActualTreeReadoutAcquisition.Address)
  Anchor := Empty
  finiteAnchor := inferInstance

def frontierActual : Realization frontierSignature := realize frontierSignature
  (fun _ _ => fun w => frontierWords w) (fun e => nomatch e)

def frontierRejected : Realization frontierSignature := realize frontierSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev frontierArena : Arena where
  signature := frontierSignature
  Law R := Primrec (R.readout () ()) ∧ ∀ d (p : Pattern d), R.readout () () (patternWord p) = some ((NativeWholeRowService.frontierList p).map (NativeDepthPatterns.frontierAddress p))

private theorem frontier_rejected : ¬ frontierArena.Law frontierRejected := by
  intro h
  have bad := h.2 0 ()
  cases bad

def frontierEvidence : Registration frontierArena (frontierArena.Law frontierActual) where
  actual := frontierActual
  bridge := Iff.rfl
  variation := ⟨uniform_frontier_words,frontierRejected,frontier_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨frontierRejected,?_,rfl,frontier_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),[some (.inr 0)],[some (.inl false)],?_⟩
    change frontierWords [some (.inr 0)] ≠ frontierWords [some (.inl false)]
    decide

abbrev familiesSignature : Signature where
  Params := Unit
  State := fun _ => Nat × Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (List PatternWord)
  Anchor := Empty
  finiteAnchor := inferInstance

def familiesActual : Realization familiesSignature := realize familiesSignature
  (fun _ _ => fun p => vectors (patternWords p.2) p.1) (fun e => nomatch e)

def familiesRejected : Realization familiesSignature := realize familiesSignature
  (fun _ _ _ => []) (fun e => nomatch e)

abbrev familiesArena : Arena where
  signature := familiesSignature
  Law R := Primrec₂ (fun n d => R.readout () () (n,d)) ∧ ∀ C d, R.readout () () ((classList C).length,d) = (NativeWholeRowService.allPatterns C d).map familyWord

private theorem families_rejected : ¬ familiesArena.Law familiesRejected := by
  intro h
  have bad := h.2 (FreeMagma.of (.inl false)) 0
  rw [← uniform_pattern_families.2] at bad
  simp [familiesRejected, realize, classList, NativeCutFibers.labels, vectors] at bad

def familiesEvidence : Registration familiesArena (familiesArena.Law familiesActual) where
  actual := familiesActual
  bridge := Iff.rfl
  variation := ⟨uniform_pattern_families,familiesRejected,families_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨familiesRejected,?_,rfl,families_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),(0,0),(1,0),?_⟩
    change vectors (patternWords 0) 0 ≠ vectors (patternWords 0) 1
    decide

/- The typed whole-family proofs preserve each complete infinite input claim.
   Contract source-selection coordinates and raw occurrence ties remain
   unregistered; these proof records claim no declared_validated status. -/

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns
