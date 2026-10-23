import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
import Reg.Support.DependentFamily
import Mathlib.Computability.Halting

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Computability.PreorderTreeEvaluation
open D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput (replyPrimcodable)
open Nat.Partrec (Code)

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree

abbrev replySignature : Signature where
  Params := Unit
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source → Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def replyActual : Realization replySignature :=
  realize replySignature (fun _ _ q => readout q) (fun e => nomatch e)

abbrev replyArena : Arena where
  signature := replySignature
  Law R := Primrec₂ (fun q u => R.readout () () q u)

noncomputable def replyRejected : Realization replySignature := by
  classical
  exact realize replySignature (fun _ _ q => fun _ =>
    if (Code.eval (Denumerable.ofNat Code q.length) 0).Dom then .alpha else .beta)
    (fun e => nomatch e)

private theorem reply_rejected_law : ¬ replyArena.Law replyRejected := by
  classical
  intro h
  have hr : Primrec (fun n : Nat => List.replicate n false) := by
    exact (Primrec.nat_rec₁ ([] : Address)
      (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂).of_eq
      (fun n => by induction n <;> simp [*, List.replicate_succ])
  have hf := h.comp (hr.comp (Primrec.encode (α := Code))) (Primrec.const (FreeMagma.of true : Source))
  have hp := Primrec.eq.comp hf (Primrec.const Reply.alpha)
  apply ComputablePred.halting_problem 0
  exact hp.computablePred.of_eq (fun c => by simp [replyRejected,realize,Denumerable.ofNat_encode])

def replyProof : Registration replyArena (type_of% (@readout_prim)) where
  actual := replyActual
  bridge := Iff.rfl
  variation := ⟨readout_prim, replyRejected, reply_rejected_law⟩
  sensitivity := ⟨fun i => ⟨replyRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, reply_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), [], [false], ?_⟩
    intro h
    have hh := congrFun h (.of true)
    change (Reply.alpha : Reply) = Reply.absent at hh
    cases hh

abbrev substitutionSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def substitutionActual : Realization substitutionSignature :=
  realize substitutionSignature (fun _ _ u => substitution u) (fun e => nomatch e)

abbrev substitutionArena : Arena where
  signature := substitutionSignature
  Law R := Primrec (fun u => R.readout () () u)

def chain : Nat → Source
  | 0 => .of true
  | n+1 => .mul (chain n) (.of true)

def measure (u : Source) : Nat := (word u).length / 2

private theorem measure_chain (n : Nat) : measure (chain n) = n := by
  have hw : ∀ n, (word (chain n)).length = 2*n+1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [chain,word,ih]; omega
  simp only [measure,hw]
  omega

private theorem chain_prim : Primrec chain := by
  exact (Primrec.nat_rec₁ (FreeMagma.of true : Source)
    (tree_mul_prim.comp Primrec.snd (Primrec.const (FreeMagma.of true : Source))).to₂).of_eq
    (fun n => by
      induction n with
      | zero => rfl
      | succ n ih => exact congrArg (fun t : Source => t.mul (.of true)) ih)

noncomputable def substitutionRejected : Realization substitutionSignature := by
  classical
  exact realize substitutionSignature (fun _ _ u =>
    if (Code.eval (Denumerable.ofNat Code (measure u)) 0).Dom
    then .of true else .of false) (fun e => nomatch e)

private theorem substitution_rejected_law : ¬ substitutionArena.Law substitutionRejected := by
  classical
  intro h
  have hc := chain_prim.comp (Primrec.encode (α := Code))
  have hf := readout_prim.comp (Primrec.const ([] : Address)) (h.comp hc)
  have hp := Primrec.eq.comp hf (Primrec.const Reply.alpha)
  apply ComputablePred.halting_problem 0
  exact hp.computablePred.of_eq (fun c => by
    simp [substitutionRejected,realize,measure_chain,Denumerable.ofNat_encode,readout]
    split <;> simp_all <;> decide)

def substitutionProof : Registration substitutionArena (type_of% (@substitution_prim)) where
  actual := substitutionActual
  bridge := Iff.rfl
  variation := ⟨substitution_prim, substitutionRejected, substitution_rejected_law⟩
  sensitivity := ⟨fun i => ⟨substitutionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, substitution_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro h; cases h

noncomputable def readout_prim_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@readout_prim) (Realization replySignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis.readout_prim.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree.replyProof
  realizationSource := none
  generated := false
  arena := .source ⟨replyArena⟩
  objectArena := .source ⟨replyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source replyArena ⟨replyProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize replySignature (fun _ _ q => readout q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms replyProof
#print axioms readout_prim_registration

noncomputable def substitution_prim_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@substitution_prim) (Realization substitutionSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis.substitution_prim.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree.substitutionProof
  realizationSource := none
  generated := false
  arena := .source ⟨substitutionArena⟩
  objectArena := .source ⟨substitutionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source substitutionArena ⟨substitutionProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize substitutionSignature (fun _ _ u => substitution u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms substitutionProof
#print axioms substitution_prim_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree
