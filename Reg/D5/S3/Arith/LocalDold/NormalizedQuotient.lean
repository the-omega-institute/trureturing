import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.LocalDold.NormalizedQuotient

/-! Faithful whole-family source reconstruction for the actual quotient coefficient observation. -/

namespace Reg.D5.S3.Arith.LocalDold.NormalizedQuotient
open LeanInformationAudit Function
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.LocalDold.NormalizedQuotient
noncomputable section

abbrev signature : Signature where
  Params := LinearRecurrence ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ E : LinearRecurrence ℤ, 0 < E.order → ∀ n : ℕ,
    R.readout () E n = impulse E n

def actual : Realization signature :=
  realize signature (fun _ E n => observation E ((AdjoinRoot.root E.charPoly)^n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ E n => observation E ((AdjoinRoot.root E.charPoly)^n)+1) (fun e => nomatch e)

abbrev sourceScope := type_of% (@observation_eq_impulse)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let E : LinearRecurrence ℤ := ⟨1,fun _ => 1⟩
  have hc := h E (by decide) 0
  change observation E ((AdjoinRoot.root E.charPoly)^0)+1 = impulse E 0 at hc
  have he := observation_eq_impulse E (by decide) 0
  omega

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@observation_eq_impulse), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let E : LinearRecurrence ℤ := ⟨2,fun _ => 1⟩
    refine ⟨E,0,1,?_⟩
    intro he
    change observation E ((AdjoinRoot.root E.charPoly)^0) =
      observation E ((AdjoinRoot.root E.charPoly)^1) at he
    rw [observation_eq_impulse E (by decide),observation_eq_impulse E (by decide)] at he
    norm_num [impulse,LinearRecurrence.mkSol,E] at he

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@observation_eq_impulse) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.LocalDold.NormalizedQuotient.observation_eq_impulse.__information_unit
  realizationName := `Reg.D5.S3.Arith.LocalDold.NormalizedQuotient.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ E n => observation E ((AdjoinRoot.root E.charPoly)^n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.LocalDold.NormalizedQuotient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Arith.LocalDold.NormalizedQuotient
