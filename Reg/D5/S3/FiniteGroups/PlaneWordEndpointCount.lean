import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.PlaneWordEndpointCount
import Reg.Support.DependentFamily

/-! A single full-telescope source-family and outer four-slot attempt.
The selected readout is the actual Nat.card occurrence on the endpoint
subtype, not the theorem's truth value.  Source selection records its exact
application argument as the state.  No successful discovery or
declared_validated status is claimed before a real scoped assessment.
-/

namespace Reg.D5.S3.FiniteGroups.PlaneWordEndpointCount

open _root_.D5.S3.FiniteGroups.PlaneWordEndpointCount
open _root_.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect (endpoint)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev endpointSignature : Signature where
  Params := Unit
  State _ := Type
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actualEndpoint : Realization endpointSignature :=
  realize endpointSignature (fun _ _ α => Nat.card α) (fun e => nomatch e)

noncomputable def rejectedEndpoint : Realization endpointSignature :=
  realize endpointSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev endpointArena : Arena where
  signature := endpointSignature
  Law R := ∀ (L a b : ℕ) (x y : ℤ)
    (hx : (L : ℤ) - 2 * (a : ℤ) = x + y)
    (hy : (L : ℤ) - 2 * (b : ℤ) = x - y),
    R.readout () () {w : Fin L → Fin 4 // endpoint w = ![x,y]} =
      Nat.choose L a * Nat.choose L b

private theorem actual_law : endpointArena.Law actualEndpoint := by
  exact endpoint_card

private theorem rejected_law : ¬ endpointArena.Law rejectedEndpoint := by
  intro h
  have hh := h 0 0 0 0 0 (by norm_num) (by norm_num)
  norm_num [rejectedEndpoint, realize] at hh

noncomputable def endpointSource : Registration endpointArena
    (type_of% endpoint_card) where
  actual := actualEndpoint
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedEndpoint, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedEndpoint, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), Empty, Unit, ?_⟩
    change Nat.card Empty ≠ Nat.card Unit
    norm_num [Nat.card_eq_fintype_card]

noncomputable def endpointRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@endpoint_card)
      (Realization endpointSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.PlaneWordEndpointCount.endpoint_card.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.PlaneWordEndpointCount.endpointSource
  realizationSource := none
  generated := false
  arena := .source ⟨endpointArena⟩
  objectArena := .source ⟨endpointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source endpointArena ⟨endpointSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize endpointSignature
    (fun _ _ α => Nat.card α) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.PlaneWordEndpointCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.PlaneWordEndpointCount
