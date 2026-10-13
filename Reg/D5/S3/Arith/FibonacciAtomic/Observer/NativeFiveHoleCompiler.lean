import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (literalRecord)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler

private def emptyHistory : History := ⟨[],by simp [Supported]⟩
private theorem present (side : Bool) : Stratum side emptyHistory (source side (.of true) (.of false)) :=
  (raw_stratum_iff side emptyHistory _).mpr ⟨.of true,.of false,rfl,
    by unfold Distinct F; decide +kernel,by simp [Protected,emptyHistory]⟩
private theorem absent (side : Bool) : ¬ Stratum side emptyHistory (.of true) := by
  intro h
  obtain ⟨x,y,z,h⟩ := (raw_fiber_iff _).mp h.1.1
  cases h

namespace StratumCompile
abbrev signature : Signature where
  Params := Σ side : Bool, History
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p u => Stratum p.1 p.2 u) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (side : Bool) (H : History) (u : Source),
    R.readout () ⟨side,H⟩ u ↔ ∃ t : Fin 2 → Source,
      u = source side (t 0) (t 1) ∧ Negatives side H t
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact (h false emptyHistory _).mpr ((stratum_compile_iff false emptyHistory _).mp (present false))
def proof : Registration arena (type_of% (@stratum_compile_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stratum_compile_iff,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨false,emptyHistory⟩,source false (.of true) (.of false),.of true,?_⟩
    intro eq
    exact absent false (eq.mp (present false))

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@stratum_compile_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler.StratumCompile.stratum_compile_iff
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler.StratumCompile.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => Stratum p.1 p.2 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end StratumCompile

namespace Separator
open D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization (uniformSeparator)
abbrev signature : Signature where
  Params := Σ side : Bool, History
  State _ := Fin 2 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p t => Negatives p.1 p.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ t => t 0 = .of true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (side : Bool) (H : History),
    R.readout () ⟨side,H⟩ (uniformSeparator (table side H)) ↔
      ∃ t : Fin 2 → Source, R.readout () ⟨side,H⟩ t
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have no := (h false emptyHistory).mpr ⟨tuple (.of true) (.of false),rfl⟩
  have root : uniformSeparator (table false emptyHistory) 0 ≠ .of true := by decide +kernel
  exact root no

def proof : Registration arena (type_of% (@separator_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separator_exact,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨false,emptyHistory⟩,tuple (.of true) (.of false),tuple (.of true) (.of true),?_⟩
    intro eq
    have yes : Negatives false emptyHistory (tuple (.of true) (.of false)) := by decide +kernel
    have no := eq.mp yes (Y,Z) (by simp [table,six,four])
    exact no rfl

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@separator_exact) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler.Separator.separator_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler.Separator.proof
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
    (fun _ p t => Negatives p.1 p.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","arg","arg","body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Separator

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
