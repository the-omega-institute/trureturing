import D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope audit of the native improper-matrix image criterion. -/

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
open _root_.D5.S3.Combinatorics.InversionSeq.InversionSeqDefs

namespace Reg.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage

abbrev signature : Signature where
  Params := ℕ
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature := realize signature
  (fun _ n e => ∃ (k : ℕ) (P : NativePM n k), Improper P ∧
    fixedPi P = fun t : Fin n => e.getD t.val 0)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (hn : 0 < n) (e : List ℕ) (hlen : e.length = n)
    (he : IsInversionSeq e),
    r.readout () n e ↔ Phi (fun t : Fin n => e.getD t.val 0)

private theorem inv_one : IsInversionSeq [0] := by
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst i
  decide

private theorem inv_three_zero : IsInversionSeq [0,0,0] := by
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by
    simp only [List.length_cons,List.length_nil] at hi
    omega
  rcases h with h | h | h <;> subst i <;> decide

private theorem inv_three_gap : IsInversionSeq [0,0,1] := by
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by
    simp only [List.length_cons,List.length_nil] at hi
    omega
  rcases h with h | h | h <;> subst i <;> decide

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) [0] rfl inv_one
  exact hh.mpr (by unfold Phi; decide)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hp : actual.readout i 3 [0,0,0] :=
    (_root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result
      3 (by decide) [0,0,0] rfl inv_three_zero).mpr (by unfold Phi; decide)
  have hq : ¬ actual.readout i 3 [0,0,1] := by
    intro hh
    have := (_root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result
      3 (by decide) [0,0,1] rfl inv_three_gap).mp hh
    exact (by unfold Phi; decide : ¬ Phi (fun t : Fin 3 => ([0,0,1] : List ℕ).getD t.val 0)) this
  refine ⟨3,[0,0,0],[0,0,1],?_⟩
  intro heq
  rw [heq] at hp
  exact hq hp

noncomputable def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.family
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
  escapeFrom := some (List ℕ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
