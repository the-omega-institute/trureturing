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
  State n := Fin n → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  exact realize signature
    (fun _ _ f => @decide (Phi f) (by unfold Phi; infer_instance))
    (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (hn : 0 < n) (e : List ℕ) (hlen : e.length = n)
    (he : IsInversionSeq e),
    (∃ (k : ℕ) (P : NativePM n k), Improper P ∧
      fixedPi P = fun t : Fin n => e.getD t.val 0) ↔
      r.readout () n (fun t : Fin n => e.getD t.val 0) = true

private theorem inv_one : IsInversionSeq [0] := by
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst i
  decide

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) [0] rfl inv_one
  have himage := (_root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result
    1 (by decide) [0] rfl inv_one).mpr (by unfold Phi; decide)
  exact Bool.noConfusion (hh.mp himage)

private theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  intro i
  have hp : actual.readout i 3 (fun _ => 0) = true := by
    simp only [actual,realize,decide_eq_true_eq]
    unfold Phi
    decide
  have hq : actual.readout i 3
      (fun t => ([0,0,1] : List ℕ).getD t.val 0) = false := by
    simp only [actual,realize,decide_eq_false_iff_not]
    unfold Phi
    decide
  refine ⟨3,(fun _ => 0),(fun t => ([0,0,1] : List ℕ).getD t.val 0),?_⟩
  rw [hp,hq]
  intro h
  cases h

noncomputable def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result)) where
  actual := actual
  bridge := by
    classical
    simp only [actual,realize,decide_eq_true_eq]
  variation := ⟨by
    classical
    intro n hn e hlen he
    simpa only [actual,realize,decide_eq_true_eq] using
      _root_.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage.result n hn e hlen he,
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
    (Realization signature) Unit Unit where
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
