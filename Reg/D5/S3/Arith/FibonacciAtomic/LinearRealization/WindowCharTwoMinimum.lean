import D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! # Family evidence for the characteristic-two joint window theorem

The complete field-dependent law, equivalence bridge, variation, sensitivity and
observational dependence have kernel proofs. Outer source binding remains open:
https://github.com/the-omega-institute/trureturing/issues/29781.
-/

open _root_.D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
open _root_.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
  (WordRepresentation wordBehavior integerFieldTask)
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

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

end Reg.D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
