import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41
noncomputable section
universe u_1
open BranchStorage Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ B => 2^(B+1)-1) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type u_1} {n k H : ℕ}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ M,
      ReachThrough action initialConfiguration (OperationRecord o b .closed) M c})
    (cuts : (Fin n → Bool) → Frame Configuration Label) (stem : List Label)
    (joint : Function.Injective (fun z => ((cuts z).state,(cuts z).output)))
    (bounded : ∀ z, (cuts z).output.length ≤ k)
    (output : ∀ z, (cuts z).output = stem.take (cuts z).output.length)
    (reached : ∀ z, ReachThrough action initialConfiguration (OperationRecord o b .closed) H (cuts z).state)
    (B : ℕ) (peak : Peak action initialConfiguration (OperationRecord o b .closed) encoding H ≤ (B : WithTop ℕ)) ,
    2^n ≤ r.readout () () B*(k+1)


theorem rejected_law : ¬ sourceArena.{u_1}.Law rejected := by
  intro h
  let C := ULift.{u_1} Unit
  let c : C := ⟨()⟩
  let action : C → Op C Color Label := fun _ => .stopped
  let cuts : (Fin 0 → Bool) → Frame C Label := fun _ => ⟨c, 0, []⟩
  obtain ⟨b, _, _, strict⟩ := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.empty_strict_supply (fun _ => false)
  have closed : ActualPairSupply .original (fun _ => false) b .closed [] := by
    intro j
    obtain ⟨err, bound, rest⟩ := strict j
    exact ⟨err, fun p => (bound p).le, rest⟩
  have record := (operation_pair_membership .original (fun _ => false) b .closed [] closed .high).1
  have reached : ∀ z, ReachThrough action c (OperationRecord (fun _ => false) b .closed) 0 (cuts z).state := by
    intro z
    exact ⟨_, _, ⟨c, 0, []⟩, record, ⟨_, .refl⟩, le_rfl, rfl⟩
  have peak : Peak action c (OperationRecord (fun _ => false) b .closed) (fun _ => []) 0 ≤ (0 : WithTop ℕ) := by
    exact iSup_le fun _ => iSup_le fun _ => le_rfl
  have impossible := @h C 0 0 0 action c (fun _ => false) b (fun _ => [])
    (by intro x hx y hy eq; exact Subsingleton.elim x y) cuts []
    (by intro x y eq; exact Subsingleton.elim x y)
    (by intro z; exact le_rfl) (by intro z; rfl) reached 0 peak
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena.{u_1} (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.common_stem_code_capacity.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.common_stem_code_capacity.{u_1}, rejected, rejected_law⟩
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
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def common_stem_code_capacity_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.common_stem_code_capacity.{u_1})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ B => 2^(B+1)-1) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u_1}⟩
  objectArena := .source ⟨sourceArena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u_1} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ B => 2^(B+1)-1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms common_stem_code_capacity_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41
