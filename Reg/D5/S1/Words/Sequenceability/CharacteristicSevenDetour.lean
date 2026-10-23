import D5.S1.Words.Sequenceability.CharacteristicSevenDetour
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! Faithful source-bound registration for the six-column lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
namespace Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour

open _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev LiftParams := Σ K : Type u, Σ f : Field K, @Units K f.toMonoid × K

abbrev liftSignature : Signature where
  Params := LiftParams.{u}
  State p := Fin 6 × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def liftActual : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p v => by
    letI := p.2.1
    exact edgeLabel p.2.2.1 p.2.2.2 v) (fun e => nomatch e)

def liftBad : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p _ => by
    letI := p.2.1
    exact (0, 0)) (fun e => nomatch e)

abbrev liftArena : Arena where
  signature := liftSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 7] (c : K),
    ∃ r : Kˣ, (r : K) + 1 ≠ 0 ∧
      (∀ v w : Fin 6 × K, (lift r c).SameCycle v w ↔
        (initialRow v = c ↔ initialRow w = c)) ∧
      Set.BijOn (R.readout () ⟨K, f, r, c⟩) Set.univ {v | v.1 ≠ 0} ∧
      Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} ∧
      (∀ h : K, (lift r c ^ 6) (0, h) = (0, rowReturn r c h))

private theorem lift_bad_law : ¬ liftArena.{u}.Law liftBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨r, _, _, hlabel, _, _⟩ := h K 0
  exact hlabel.1 (show (0, (0 : K)) ∈ Set.univ from trivial) rfl

def liftFamily : Registration liftArena.{u}
    (type_of% (@exists_characteristic_seven_lift.{u})) where
  actual := liftActual
  bridge := Iff.rfl
  variation := ⟨exists_characteristic_seven_lift, liftBad, lift_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨liftBad, ?_, rfl, lift_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance, 1, 0⟩, (0, 0), (1, 0), ?_⟩
    intro he
    have h := congrArg Prod.fst he
    have h' : (2 : ZMod 7) - 1 = 6 - 3 := by
      simpa [liftActual, realize, edgeLabel, lift, vertex, column] using h
    exact (by decide : (2 : ZMod 7) - 1 ≠ 6 - 3) h'

def liftAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_seven_lift.{u}) (Realization liftSignature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.exists_characteristic_seven_lift.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.liftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena⟩
  objectArena := .source ⟨liftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena ⟨liftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize liftSignature liftActual.readout liftActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour
