import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.EndpointShuffleSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S1.Words.EndpointShuffleSupport
open _root_.D5.S1.Words.EndpointShuffleSupport
open _root_.D5.S1.Words.UnaryGapWords
open _root_.D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace endpointOutput_mem
abbrev signature := Reg.Support.SingleDependentReadout.signature (Σ _ : Nat, Nat)
  (fun _ => Nat) (fun _ => List Bool)
def actual : Realization signature :=
  realize signature (fun _ p c => endpointOutput p.1 p.2 c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m a c : Nat, a ≤ m → c ≤ m → R.readout () ⟨m,a⟩ c ∈ ordinaryShuffles (endpointWord m) (endpointWord m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0 (by omega) (by omega)
  change [] ∈ ordinaryShuffles (endpointWord 0) (endpointWord 0) at hh
  simpa [endpointWord,ordinaryShuffles] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,0⟩,0,1,?_⟩
  change endpointOutput 1 0 0 ≠ endpointOutput 1 0 1
  simp [endpointOutput,gap]
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.endpointOutput_mem)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.endpointOutput_mem,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.endpointOutput_mem) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.endpointOutput_mem.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.endpointOutput_mem.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end endpointOutput_mem

namespace endpointFamily_card
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ m => (endpointFamily m).card) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat, R.readout () () m = (m+1)^2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change 0 = (0+1)^2 at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (endpointFamily 0).card ≠ (endpointFamily 1).card
  rw [_root_.D5.S1.Words.EndpointShuffleSupport.endpointFamily_card,
    _root_.D5.S1.Words.EndpointShuffleSupport.endpointFamily_card]
  decide
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.endpointFamily_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.endpointFamily_card,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.endpointFamily_card) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.endpointFamily_card.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.endpointFamily_card.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end endpointFamily_card

namespace endpoint_self_shuffle_card_lower
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ m => ((ordinaryShuffles (endpointWord m) (endpointWord m)).toFinset).card) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat, (m+1)^2 ≤ R.readout () () m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change (0+1)^2 ≤ 0 at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change ((ordinaryShuffles (endpointWord 0) (endpointWord 0)).toFinset).card ≠
    ((ordinaryShuffles (endpointWord 1) (endpointWord 1)).toFinset).card
  rw [_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card,
    _root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card]
  decide
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card_lower)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card_lower,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card_lower) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card_lower.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card_lower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end endpoint_self_shuffle_card_lower

namespace endpoint_support_exhaustion
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => List (List Bool))
def actual : Realization signature :=
  realize signature (fun _ _ m => ordinaryShuffles (endpointWord m) (endpointWord m)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => [[]]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : Nat) (w : List Bool), w ∈ R.readout () () m → ∃ a ≤ m, ∃ c ≤ m, w = endpointOutput m a c
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a,ha,c,hc,he⟩ := h 0 [] (by simp [rejected,realize])
  simp [endpointOutput,gap] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hh := congrArg (fun ws : List (List Bool) => ws.toFinset.card) h
  change ((ordinaryShuffles (endpointWord 0) (endpointWord 0)).toFinset).card =
    ((ordinaryShuffles (endpointWord 1) (endpointWord 1)).toFinset).card at hh
  rw [_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card,
    _root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card] at hh
  norm_num at hh
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_support_exhaustion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_support_exhaustion,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_support_exhaustion) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.endpoint_support_exhaustion.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.endpoint_support_exhaustion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","domain","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end endpoint_support_exhaustion

namespace endpoint_support_eq
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => Finset (List Bool))
def actual : Realization signature :=
  realize signature (fun _ _ m => (ordinaryShuffles (endpointWord m) (endpointWord m)).toFinset) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat, R.readout () () m = endpointFamily m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg Finset.card (h 0)
  change (∅ : Finset (List Bool)).card = (endpointFamily 0).card at hh
  rw [_root_.D5.S1.Words.EndpointShuffleSupport.endpointFamily_card] at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hh := congrArg Finset.card h
  change ((ordinaryShuffles (endpointWord 0) (endpointWord 0)).toFinset).card =
    ((ordinaryShuffles (endpointWord 1) (endpointWord 1)).toFinset).card at hh
  rw [_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card,
    _root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card] at hh
  norm_num at hh
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_support_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_support_eq,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_support_eq) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.endpoint_support_eq.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.endpoint_support_eq.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end endpoint_support_eq

namespace endpoint_self_shuffle_card
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ m => ((ordinaryShuffles (endpointWord m) (endpointWord m)).toFinset).card) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat, R.readout () () m = (m+1)^2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change 0 = (0+1)^2 at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change ((ordinaryShuffles (endpointWord 0) (endpointWord 0)).toFinset).card ≠
    ((ordinaryShuffles (endpointWord 1) (endpointWord 1)).toFinset).card
  rw [_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card,
    _root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card]
  decide
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end endpoint_self_shuffle_card

namespace binaryWord_pow_add_one
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => List Bool)
def actual : Realization signature :=
  realize signature (fun _ _ n => binaryWord n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Nat, 1 ≤ k → R.readout () () (2^k+1) = endpointWord (k-1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by omega)
  change [] = endpointWord (1-1) at hh
  simp [endpointWord] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),3,5,?_⟩
  change binaryWord 3 ≠ binaryWord 5
  have h1 := _root_.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one 1 (by omega)
  have h2 := _root_.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one 2 (by omega)
  norm_num at h1 h2
  rw [h1,h2]
  simp [endpointWord]
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end binaryWord_pow_add_one

namespace result
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ n => distinctSelfShuffleCount n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∃ K : Nat, 1 ≤ K ∧ ∀ k : Nat, K ≤ k → R.readout () () (2^k+1) = k^2
private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨K,hK,h⟩
  have hh := h K (by omega)
  change 0 = K^2 at hh
  have hp : 0 < K^2 := Nat.pow_pos (by omega)
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),3,5,?_⟩
  change distinctSelfShuffleCount 3 ≠ distinctSelfShuffleCount 5
  have h1 := _root_.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one 1 (by omega)
  have h2 := _root_.D5.S1.Words.EndpointShuffleSupport.binaryWord_pow_add_one 2 (by omega)
  norm_num at h1 h2
  unfold distinctSelfShuffleCount
  rw [h1,h2,_root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card,
    _root_.D5.S1.Words.EndpointShuffleSupport.endpoint_self_shuffle_card]
  decide
def family : Registration arena (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.result,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.result) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.result.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","arg","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end result

namespace prefix_left
universe u
abbrev signature : Signature where
  Params := Σ A : Type u, List A
  State q := List q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := List (List q.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ q p => ordinaryShuffles p q.2) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} (p u v z : List A), z ∈ ordinaryShuffles u v →
    p ++ z ∈ R.readout () ⟨A,v⟩ (p ++ u)
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} Bool) [] [] [] [] (by simp [ordinaryShuffles])
  change [] ∈ ([] : List (List (ULift.{u} Bool))) at hh
  simp at hh
private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} Bool,[]⟩,[],[ULift.up true],?_⟩
  change ordinaryShuffles ([] : List (ULift.{u} Bool)) [] ≠ ordinaryShuffles [ULift.up true] []
  simp [ordinaryShuffles]
private theorem sensitive : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected.{u},?_,?_,rejected_law.{u}⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def family : Registration arena.{u} (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.prefix_left.{u})) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.prefix_left.{u},rejected.{u},rejected_law.{u}⟩
  sensitivity := sensitive.{u}
  dependence := dependence.{u}
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.prefix_left.{u}) (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.prefix_left.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.prefix_left.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ q p => ordinaryShuffles p q.2) actual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end prefix_left


namespace prefix_right
universe u
abbrev signature : Signature where
  Params := Σ A : Type u, List A
  State q := List q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := List (List q.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ q p => ordinaryShuffles q.2 p) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} (p u v z : List A), z ∈ ordinaryShuffles u v →
    p ++ z ∈ R.readout () ⟨A,u⟩ (p ++ v)
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} Bool) [] [] [] [] (by simp [ordinaryShuffles])
  change [] ∈ ([] : List (List (ULift.{u} Bool))) at hh
  simp at hh
private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} Bool,[]⟩,[],[ULift.up true],?_⟩
  change ordinaryShuffles ([] : List (ULift.{u} Bool)) [] ≠ ordinaryShuffles [] [ULift.up true]
  simp [ordinaryShuffles]
private theorem sensitive : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected.{u},?_,?_,rejected_law.{u}⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def family : Registration arena.{u} (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.prefix_right.{u})) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.prefix_right.{u},rejected.{u},rejected_law.{u}⟩
  sensitivity := sensitive.{u}
  dependence := dependence.{u}
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.prefix_right.{u}) (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.prefix_right.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.prefix_right.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ q p => ordinaryShuffles q.2 p) actual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end prefix_right


namespace mem_swap
universe u
abbrev signature : Signature where
  Params := Σ A : Type u, List A
  State q := List q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := List (List q.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ q p => ordinaryShuffles p q.2) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} (u v w : List A), w ∈ ordinaryShuffles u v →
    w ∈ R.readout () ⟨A,u⟩ v
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} Bool) [] [] [] (by simp [ordinaryShuffles])
  change [] ∈ ([] : List (List (ULift.{u} Bool))) at hh
  simp at hh
private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} Bool,[]⟩,[],[ULift.up true],?_⟩
  change ordinaryShuffles ([] : List (ULift.{u} Bool)) [] ≠ ordinaryShuffles [ULift.up true] []
  simp [ordinaryShuffles]
private theorem sensitive : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected.{u},?_,?_,rejected_law.{u}⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def family : Registration arena.{u} (type_of% (@_root_.D5.S1.Words.EndpointShuffleSupport.mem_swap.{u})) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.EndpointShuffleSupport.mem_swap.{u},rejected.{u},rejected_law.{u}⟩
  sensitivity := sensitive.{u}
  dependence := dependence.{u}
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.EndpointShuffleSupport.mem_swap.{u}) (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S1.Words.EndpointShuffleSupport.mem_swap.__information_unit
  realizationName := `Reg.D5.S1.Words.EndpointShuffleSupport.mem_swap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ q p => ordinaryShuffles p q.2) actual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EndpointShuffleSupport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end mem_swap

end Reg.D5.S1.Words.EndpointShuffleSupport
