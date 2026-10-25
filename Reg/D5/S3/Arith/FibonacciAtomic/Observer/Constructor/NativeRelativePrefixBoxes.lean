import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRelativePrefixBoxes
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRelativePrefixBoxes

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open Observer.NativeConstructorArrays (S)
open Observer.NativeRelativePrefixBoxes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : Nat, Σ _ : Address, Factor
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Factor
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => gamma p.2.1 u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0,false)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : Nat) (q : Address), q.length < d →
    ∀ z : Factor, (∃ u : S d, gamma q u.val = z) →
    level d q z = {u : S d | ∀ v : Address, v.IsPrefix q →
      readout v u.val ∈ projection d q v z} ∧
    Classified d q z ∧
    (∀ (i j : Nat) (b c : Bool), i ≤ q.length → j ≤ q.length → i < j →
      (descriptor q i b = descriptor q j c ↔
        b = false ∧ c = true ∧ j = i+1 ∧ DoubleAt q i)) ∧
    (∀ i : Nat, i ≤ q.length → ∀ b : Bool,
      ∃ u : S d, readout (q.take i) u.val = leafReply b) ∧
    (∃ u : S d, readout q u.val = .branch) ∧
    (∀ u : Source, (gamma q u).2 = true → 2 ≤ (gamma q u).1) ∧
    (∀ u : Source, readout q u = .absent →
      ∃ i : Nat, i < q.length ∧ ∃ b : Bool,
        readout (q.take i) u = leafReply b ∧ R.readout () ⟨d,q,z⟩ u = descriptor q i b)

private theorem positive : arena.Law actual := canonical_factor_levels

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have hr := h 2 [false] (by decide) (2,false)
    ⟨⟨.of false,by trivial⟩,rfl⟩
  obtain ⟨i,hi,b,_,hg⟩ := hr.2.2.2.2.2.2 (.of false) rfl
  have he : i = 0 := by simpa using hi
  subst i
  have bad := congrArg Prod.fst hg
  cases b <;> norm_num [rejected,realize,descriptor,leafFactor,
    Observer.NativeRankedNavigationCompiler.pathCost] at bad

def evidence : Registration arena (type_of% (@canonical_factor_levels)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive,rejected,negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ negative
  dependence := by
    intro i
    refine ⟨⟨1,[],(2,true)⟩,.of true,.of false,?_⟩
    intro bad
    have := congrArg Prod.fst bad
    change 2 = 1 at this
    omega

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_factor_levels) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRelativePrefixBoxes.canonical_factor_levels.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRelativePrefixBoxes.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRelativePrefixBoxes
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","body",
        "arg","arg","arg","arg","arg","arg","body","body",
        "arg","body","arg","arg","body","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRelativePrefixBoxes
