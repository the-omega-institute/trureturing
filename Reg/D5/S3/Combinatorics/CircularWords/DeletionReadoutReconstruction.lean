import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound registrations for circular deletion reconstruction and faithfulness. -/

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport

namespace Reg.D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
universe u

namespace reconstruction
abbrev signature : Signature where
  Params := Type u
  State α := Cycle α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := Cycle α
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ C => C) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => Cycle.nil) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law f := ∀ {α : Type u} [DecidableEq α] {A : Finset α} (_hA : 4 ≤ A.card)
    {C D : Cycle α}, C.Nodup → D.Nodup → C.toFinset = A → D.toFinset = A →
    (∀ x ∈ A, delete x C = delete x D) → C = f.readout () α D

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let L : List (ULift.{u} (Fin 4)) := [ULift.up 0,ULift.up 1,ULift.up 2,ULift.up 3]
  have hn : (L : Cycle (ULift.{u} (Fin 4))).Nodup := by simp [L]
  have hc : 4 ≤ (L : Cycle (ULift.{u} (Fin 4))).toFinset.card := by simp [L]
  have hh := h hc hn hn rfl rfl (fun _ _ => rfl)
  have he := congrArg Cycle.length hh
  simp [actual, rejected, realize, L] at he

def family : Registration arena.{u} (type_of% (@reconstruct.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reconstruct, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, Cycle.nil, ([ULift.up ()] : List _), ?_⟩
    intro h
    have he := congrArg Cycle.length h
    simp [actual, realize] at he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reconstruct.{u}) (type_of% actual.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.reconstruct.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.reconstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end reconstruction
namespace kernelThreshold
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

abbrev signature : Signature where
  Params := Type u
  State α := Finset α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ A => A.card)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 4) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law f := ∀ {α : Type u} [DecidableEq α] (A : Finset α) (_hA : 3 ≤ A.card),
    jointKernel (deletionReadout A) = diagonal (SupportedCircle A) ↔ 4 ≤ f.readout () α A

private def supportThree : Finset (ULift.{u} (Fin 4)) :=
  {ULift.up 0,ULift.up 1,ULift.up 2}
private def supportFour : Finset (ULift.{u} (Fin 4)) :=
  {ULift.up 0,ULift.up 1,ULift.up 2,ULift.up 3}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h3 : 3 ≤ supportThree.{u}.card := by simp [supportThree]
  have hh := (h supportThree h3).mpr (Nat.le_refl 4)
  have impossible := (deletion_joint_kernel_iff supportThree h3).mp hh
  norm_num [supportThree] at impossible

def family : Registration arena.{u} (type_of% (@deletion_joint_kernel_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deletion_joint_kernel_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨ULift.{u} (Fin 4),supportThree,supportFour,?_⟩
    simp [actual, realize, supportThree, supportFour]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deletion_joint_kernel_iff.{u}) (type_of% actual.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.deletion_joint_kernel_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.kernelThreshold.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","arg","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end kernelThreshold
end Reg.D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
