import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
open _root_.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
  (WordRepresentation wordBehavior integerFieldTask)
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum

universe u v

/-- The complete coefficient-field telescope, including its characteristic law. -/
abbrev Params := Σ K : Type u, {inst : Field K // @CharP K inst.toAddMonoidWithOne 2}

abbrev signature : Signature where
  Params := Params.{u}
  State _ := List Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p w => @integerFieldTask p.1 p.2.1 w) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; (0, 0)) (fun e => nomatch e)

/-- Intervene on the actual two-channel task, keeping the complete rank and
universal representation-minimality statement. -/
@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [inst : Field K] [hc : CharP K 2],
    (∀ w : List Window,
      wordBehavior (fourDimensional K) w = R.readout () ⟨K, inst, hc⟩ w) ∧
    FiniteDimensional K (jointHankelSpace K (integerFieldTask K)) ∧
    Module.finrank K (jointHankelSpace K (integerFieldTask K)) = 4 ∧
    Module.finrank K (BlockState K) = 4 ∧
    (∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (R : WordRepresentation K Window V (K × K)),
      (∀ w : List Window, wordBehavior R w = integerFieldTask K w) →
        4 ≤ Module.finrank K V)

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have impossible := (h (ULift.{u} (ZMod 2))).1 []
  have first := congrArg Prod.fst impossible
  change (1 : ULift.{u} (ZMod 2)) = 0 at first
  exact one_ne_zero first

def familyRegistration : Registration arena.{u,v} (type_of% (@result.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    refine ⟨⟨ULift.{u} (ZMod 2), inferInstance, inferInstance⟩,
      ([] : List Window), ([.middle] : List Window), ?_⟩
    intro heq
    have second := congrArg Prod.snd heq
    change (0 : ULift.{u} (ZMod 2)) = 1 at second
    exact zero_ne_one second

noncomputable def registration : Contract.Registration (@result.{u,v})
    (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum.result
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p w => @integerFieldTask p.1 p.2.1 w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
