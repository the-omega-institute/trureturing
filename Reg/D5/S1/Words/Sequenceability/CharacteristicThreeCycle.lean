import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.Sequenceability.CharacteristicThreeCycle
import Mathlib.Algebra.Field.ULift

/-! Source-bound family for the actual additive vertex readout in the cycle inventory. -/

namespace Reg.D5.S1.Words.Sequenceability.CharacteristicThreeCycle

open Function
open _root_.D5.S1.Words.Sequenceability.CharacteristicThreeCycle
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

structure Inputs where
  K : Type u
  field : Field K
  fintype : Fintype K
  char : @CharP K field.toAddMonoidWithOne 3

abbrev State (P : Inputs.{u}) : Type u := letI := P.field; P.Kˣ × ZMod 3

abbrev signature : Signature where
  Params := Inputs.{u}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.K × ZMod 3
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ P z => by letI := P.field; exact vertex z) (fun e => nomatch e)

noncomputable def rejected : Realization signature.{u} :=
  realize signature (fun _ P _ => by letI := P.field; exact (0 : P.K × ZMod 3)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.field
    letI := P.fintype
    letI := P.char
    let L := Fintype.card P.K - 1
    ∃ (a : P.Kˣ) (ha : (a : P.K) ≠ 1),
      orderOf a = L ∧ 2 ≤ L ∧ Even L ∧
      ∃ e : Fin (3 * L) ≃ P.Kˣ × ZMod 3,
        (∀ i, e i = (step a)^[i.val] (1, 0)) ∧
        (step a)^[3 * L] (1, 0) = (1, 0) ∧
        Bijective (fun i => label a ha (e i)) ∧
        (∀ z, vertex (step a z) - vertex z = R.readout () P (label a ha z))

abbrev sourceScope := type_of% (@exists_cycle_inventory.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := by
  constructor
  · intro h P
    letI := P.field
    letI := P.fintype
    letI := P.char
    exact @h P.K P.field P.fintype P.char
  · intro h K field fintype char
    exact h ⟨K, field, fintype, char⟩

private theorem actual_law : arena.{u}.Law actual :=
  source_bridge.mp (@exists_cycle_inventory.{u})

abbrev sample : Inputs.{u} := ⟨ULift.{u} (ZMod 3), inferInstance, inferInstance, inferInstance⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨a, ha, _, _, _, e, _, _, _, hd⟩ := h sample
  have hz := hd (1, 0)
  have he : (a : ULift.{u} (ZMod 3)) - 1 = 0 := by
    simpa [vertex, step, rejected, realize] using congrArg Prod.fst hz
  exact ha (sub_eq_zero.mp he)

noncomputable def family : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨sample, (1, 0), (1, 1), ?_⟩
    intro h
    have he : (0 : ZMod 3) = 1 := congrArg Prod.snd h
    exact zero_ne_one he

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_cycle_inventory.{u}) (Realization signature.{u}) (type_of% (@vertex.{u})) Unit where
  unitName := `Reg.D5.S1.Words.Sequenceability.CharacteristicThreeCycle.unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicThreeCycle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ P z => by letI := P.field; exact vertex z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicThreeCycle
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "arg", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 8
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S1.Words.Sequenceability.CharacteristicThreeCycle
