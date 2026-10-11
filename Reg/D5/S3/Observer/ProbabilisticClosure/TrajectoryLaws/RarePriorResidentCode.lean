import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x => bitCode x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨2,(0 : Fin 2),(1 : Fin 2),?_⟩
  intro h
  have he : (0 : Fin 2) = 1 := bit_code_injective h
  cases he

def lengthArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (x : Fin n), (R.readout () n x).length = n

private theorem length_rejected : ¬ lengthArena.Law rejected := by
  intro h
  have he := @h 1 0
  norm_num [rejected,realize] at he

def lengthRecord : Registration lengthArena (type_of% (@bit_code_length)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bit_code_length,rejected,length_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,length_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def lengthRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bit_code_length) (type_of% (realize signature
      (fun _ _ x => bitCode x) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorResidentCode.bit_code_length.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode.lengthRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨lengthArena⟩, objectArena := .source ⟨lengthArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source lengthArena ⟨lengthRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => bitCode x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def injectiveArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, Function.Injective (R.readout () n)

private theorem injective_rejected : ¬ injectiveArena.Law rejected := by
  intro h
  have he : (0 : Fin 2) = 1 := @h 2 (0 : Fin 2) (1 : Fin 2) rfl
  cases he

def injectiveRecord : Registration injectiveArena (type_of% (@bit_code_injective)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bit_code_injective,rejected,injective_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,injective_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def injectiveRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bit_code_injective) (type_of% (realize signature
      (fun _ _ x => bitCode x) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorResidentCode.bit_code_injective.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode.injectiveRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨injectiveArena⟩, objectArena := .source ⟨injectiveArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source injectiveArena ⟨injectiveRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => bitCode x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
