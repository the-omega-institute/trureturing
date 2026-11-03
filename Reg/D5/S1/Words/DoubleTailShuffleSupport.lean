import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.DoubleTailShuffleSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S1.Words.DoubleTailShuffleSupport
open _root_.D5.S1.Words.DoubleTailShuffleSupport
open _root_.D5.S1.Words.EndpointShuffleSupport
open _root_.D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace self_shuffle_card
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ m => ((ordinaryShuffles (root m) (root m)).toFinset).card) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat, R.readout () () m = (m+2)*(m+1)/2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change 0 = (0+2)*(0+1)/2 at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change ((ordinaryShuffles (root 0) (root 0)).toFinset).card ≠
    ((ordinaryShuffles (root 1) (root 1)).toFinset).card
  rw [_root_.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card,
    _root_.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card]
  decide
def family : Registration arena (type_of% (@_root_.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card.__information_unit
  realizationName := `Reg.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card.family
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
    owner := `D5.S1.Words.DoubleTailShuffleSupport
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
end self_shuffle_card

namespace binary_root_original
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => List Bool)
def actual : Realization signature :=
  realize signature (fun _ _ n => binaryWord n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Nat, 3 ≤ k → R.readout () () (2^k-4) = root (k-2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 (by omega)
  change [] = root (3-2) at hh
  simp [root] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),4,12,?_⟩
  change binaryWord 4 ≠ binaryWord 12
  have h1 := _root_.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original 3 (by omega)
  have h2 := _root_.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original 4 (by omega)
  norm_num at h1 h2
  rw [h1,h2]
  simp [root,List.replicate_succ]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.DoubleTailShuffleSupport.binary_root_original.__information_unit
  realizationName := `Reg.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original.family
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
    owner := `D5.S1.Words.DoubleTailShuffleSupport
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
end binary_root_original

namespace result
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => Nat) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ n => distinctSelfShuffleCount n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∃ K : Nat, 3 ≤ K ∧ ∀ k : Nat, K ≤ k → R.readout () () (2^k-4) = k*(k-1)/2
private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨K,hK,h⟩
  have hh := h K (by omega)
  change 0 = K*(K-1)/2 at hh
  have hp : 3*2 ≤ K*(K-1) := Nat.mul_le_mul hK (by omega)
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),4,12,?_⟩
  change distinctSelfShuffleCount 4 ≠ distinctSelfShuffleCount 12
  have h1 := _root_.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original 3 (by omega)
  have h2 := _root_.D5.S1.Words.DoubleTailShuffleSupport.binary_root_original 4 (by omega)
  norm_num at h1 h2
  unfold distinctSelfShuffleCount
  rw [h1,h2,_root_.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card,
    _root_.D5.S1.Words.DoubleTailShuffleSupport.self_shuffle_card]
  decide

def family : Registration arena (type_of% (@_root_.D5.S1.Words.DoubleTailShuffleSupport.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.DoubleTailShuffleSupport.result,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.DoubleTailShuffleSupport.result) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.DoubleTailShuffleSupport.result.__information_unit
  realizationName := `Reg.D5.S1.Words.DoubleTailShuffleSupport.result.family
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
    owner := `D5.S1.Words.DoubleTailShuffleSupport
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

end Reg.D5.S1.Words.DoubleTailShuffleSupport
