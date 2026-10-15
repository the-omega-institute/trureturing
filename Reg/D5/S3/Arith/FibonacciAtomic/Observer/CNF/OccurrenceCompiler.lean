import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore (Controller)
open D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open StateTransition (EvalsToInTime)

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler

private theorem no_transition {K : Type} (a b : K) (ne : a ≠ b) (m : Nat) :
    ¬ Nonempty (EvalsToInTime (fun _ : K => none) a (some b) m) := by
  rintro ⟨run⟩
  have hs := run.evals_in_steps
  cases hn : run.steps with
  | zero => simp only [hn,Function.iterate_zero_apply,Option.some.injEq] at hs; exact ne hs
  | succ n =>
    have dead : ∀ k : Nat,
        (flip bind (fun _ : K => none))^[k+1] (some a) = none := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
    rw [hn,dead] at hs
    cases hs

private def constant : Controller Unit Bool where
  addr := fun _ => Bank.literal 1 0
  next := fun _ _ => .inr false
  out := fun _ => _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.predecessor 0

private def changing : Controller Unit Bool where
  addr := fun _ => []
  next := fun _ r => .inr (Bank.branchBit r)
  out := constant.out

private def small : Formula 1 := [[(0,true)]]
private def source0 : Source := .of true
private def source1 : Source := .of false

namespace Prefix

abbrev signature : Signature where
  Params := Σ Q : Type, Σ H : Type, Controller Q H
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (p.1 ⊕ p.2.1) → Option (p.1 ⊕ p.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => step p.2.2 u) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} {Q H : Type} (C : Controller Q H)
    (place : Nat → Q ⊕ H) (S F : Q ⊕ H) (u : Source) (f : Formula n),
    Installed C place S F (records 0 f) →
    (records 0 f).length = occurrences f ∧
    (records 0 f).map Prod.fst = List.range (occurrences f) ∧
    Nonempty (EvalsToInTime (R.readout () ⟨Q,H,C⟩ u)
      (resolve place S F (entry 0 f))
      (some (if evaluate f u then S else F)) (occurrences f))

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have installed : Installed constant (fun _ => .inl ()) (.inr false) (.inr false)
      (records 0 small) := by
    intro i r hr
    simp only [small,records,clause,List.append_nil,List.mem_singleton] at hr
    cases hr
    refine ⟨(),rfl,rfl,?_⟩
    intro reply
    simp only [constant,clauseEntry,entry]
    split <;> rfl
  have run := (law constant (fun _ => .inl ()) (.inr false) (.inr false)
    source0 small installed).2.2
  have run' : Nonempty (EvalsToInTime (fun _ : Unit ⊕ Bool => none)
      (.inl ()) (some (.inr false)) 1) := by
    split at run <;>
    simpa only [bad,realize,small,entry,clauseEntry,resolve,occurrences,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,
      List.length_nil,Nat.zero_add,Nat.add_zero,ite_self,Bool.false_eq_true,
      ite_false,ite_true] using run
  exact no_transition (K := Unit ⊕ Bool) (.inl ()) (.inr false) (by intro h; cases h) 1 run'

def proof : Registration arena (type_of% (@installed_prefix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@installed_prefix,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Unit,Bool,changing⟩,source0,source1,?_⟩
    intro eq
    have h := congrFun eq (.inl ())
    have ne : step changing source0 (.inl ()) ≠ step changing source1 (.inl ()) := by
      decide +kernel
    exact ne h

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@installed_prefix) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler.Prefix.installed_prefix
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler.Prefix.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => step p.2.2 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler
    definition := none
    coordinates := #[1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "arg","arg","arg","fn","fn","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Prefix

namespace Native

abbrev signature : Signature where
  Params := Σ _f : PredictiveThermodynamic.Conventional.Formula,
    Σ Q : Type, Σ H : Type, Σ _S : Q ⊕ H, Q ⊕ H
  State p := Controller p.2.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Controller
    (Fin (records 0 (PredictiveThermodynamic.BinaryNames.denseFormula p.1)).length ⊕ p.2.1)
    p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p C => plug (records 0 (PredictiveThermodynamic.BinaryNames.denseFormula p.1))
    C p.2.2.2.1 p.2.2.2.2) (fun e => nomatch e)

def bad : Realization signature := realize signature
  (fun _ p C => { actual.readout () p C with addr := fun _ => [] }) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f : PredictiveThermodynamic.Conventional.Formula)
    {Q H : Type} (C : Controller Q H) (S F : Q ⊕ H) (u : Source),
    let dense := PredictiveThermodynamic.BinaryNames.denseFormula f
    let rs := records 0 dense
    let linked := R.readout () ⟨f,Q,H,S,F⟩ C
    rs.length = (PredictiveThermodynamic.Conventional.occurrences f).length ∧
    rs.map Prod.fst = List.range rs.length ∧
    Valid (entry 0 dense) rs ∧
    Function.Injective (fun i : Fin rs.length => placement rs F i.val) ∧
    Installed linked (placement rs F) (embed S) (embed F) rs ∧
    (∀ q, linked.addr (.inr q) = C.addr q ∧
      ∀ r, linked.next (.inr q) r = embed (C.next q r)) ∧
    linked.out = C.out ∧
    Nonempty (EvalsToInTime (step linked u)
      (resolve (placement rs F) (embed S) (embed F) (entry 0 dense))
      (some (embed (if PredictiveThermodynamic.Conventional.evaluate f
        (sourceAssignment f u) then S else F)))
      (PredictiveThermodynamic.Conventional.occurrences f).length)

private def C0 : Controller Unit Bool := { constant with addr := fun _ => [] }
private def C1 : Controller Unit Bool := { constant with addr := fun _ => [false] }

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have h := ((law [] C1 (.inr false) (.inr false) source0).2.2.2.2.2.1 ()).1
  change ([] : List Bool) = [false] at h
  cases h

def proof : Registration arena (type_of% (@native_occurrence_compiler)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_occurrence_compiler,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨[],Unit,Bool,.inr false,.inr false⟩,C0,C1,?_⟩
    intro eq
    have h := congrArg (fun C => C.addr (.inr ())) eq
    change ([] : List Bool) = [false] at h
    cases h

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_occurrence_compiler) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler.Native.native_occurrence_compiler
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler.Native.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p C => plug (records 0 (PredictiveThermodynamic.BinaryNames.denseFormula p.1))
      C p.2.2.2.1 p.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler
    definition := none
    coordinates := #[0,1,2,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Native

#print axioms Prefix.proof
#print axioms Native.proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler
