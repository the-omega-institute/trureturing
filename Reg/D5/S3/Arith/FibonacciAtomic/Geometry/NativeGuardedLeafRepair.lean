import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
import Reg.Support.DependentFamily

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition (material)
open D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def cardSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def cardActual : Realization cardSignature :=
  realize cardSignature
    (fun role _ t => if role then (material t).length else (material t).toFinset.card)
    (fun e => nomatch e)

@[reducible] def cardArena : Arena where
  signature := cardSignature
  Law R := ∀ t : Source, R.readout false () t = R.readout true () t

def cardBadLeft : Realization cardSignature :=
  realize cardSignature (fun role _ t => if role then (material t).length else 0)
    (fun e => nomatch e)

def cardBadRight : Realization cardSignature :=
  realize cardSignature (fun role _ t => if role then 0 else (material t).toFinset.card)
    (fun e => nomatch e)

private theorem badLeft : ¬ cardArena.Law cardBadLeft := by
  intro h
  have he := h (.of true)
  norm_num [cardBadLeft, realize, cardArena, material] at he

private theorem badRight : ¬ cardArena.Law cardBadRight := by
  intro h
  have he := h (.of true)
  norm_num [cardBadRight, realize, cardArena, material] at he

def cardFamily : Registration cardArena
    (∀ t : Source, (material t).toFinset.card = (material t).length) := {
  actual := cardActual
  bridge := Iff.rfl
  variation := ⟨material_card, cardBadLeft, badLeft⟩
  sensitivity := ⟨by
    intro role
    cases role
    · refine ⟨cardBadLeft, ?_, rfl, badLeft⟩
      intro j hj
      cases j
      · exact False.elim (hj rfl)
      · rfl
    · refine ⟨cardBadRight, ?_, rfl, badRight⟩
      intro j hj
      cases j
      · rfl
      · exact False.elim (hj rfl), fun e => nomatch e⟩
  dependence := by
    intro role
    refine ⟨(), .of true, .of false, ?_⟩
    cases role <;> decide }

noncomputable def cardRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@material_card)
    (type_of% (realize cardSignature cardActual.readout cardActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair.material_card
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair.cardFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cardArena⟩
  objectArena := .source ⟨cardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cardArena ⟨cardFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardSignature cardActual.readout cardActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg", "arg", "arg"], booleanPredicate := false }, {
      path := #["body", "arg"]
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms cardRegistration
end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
