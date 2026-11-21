import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Kozlov.TransferEndpoints

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Kozlov

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Kozlov.TransferEndpoints

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def makeReadout (count : ℕ → ℕ → ℕ) : Realization signature :=
  realize signature (fun _ n r => count n r) (fun e _ => e.elim)

abbrev properArena : Arena where
  signature := signature
  Law obs := ∀ {n : ℕ} (hn : 1 ≤ n) (r : ℕ), obs.readout () n r =
    (properTransfer hn ^ (r + 2)) (firstState hn) (lastState hn)

abbrev latticeArena : Arena where
  signature := signature
  Law obs := ∀ {n : ℕ} (hn : 1 ≤ n) (r : ℕ), obs.readout () n r =
    (latticeTransfer hn ^ (r + 2)) (firstState hn) (lastState hn)

private def proper (n r : ℕ) : ℕ := (properSumset n (r + 1)).ncard
private def lattice (n r : ℕ) : ℕ := (dilateLattice n (r + 1)).ncard

private theorem powers_two_by_two (T : Matrix (Fin 2) (Fin 2) ℕ)
    (hdiag : ∀ i, T i i = 1) (hzero : T 1 0 = 0) (hcorner : T 0 1 = 1) :
    (T ^ 2) 0 1 = 2 ∧ (T ^ 3) 0 1 = 3 := by
  have h00 : (T ^ 2) 0 0 = 1 := by
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hdiag, hzero]
  have h01 : (T ^ 2) 0 1 = 2 := by
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hdiag, hcorner]
  refine ⟨h01, ?_⟩
  rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
    h00, h01, hdiag 1, hcorner]
  decide

private theorem proper_two : proper 2 0 = 2 ∧ proper 2 1 = 3 := by
  have hn : 1 ≤ (2 : ℕ) := by decide
  have ht := properTransfer_unitriangular hn
  have hcorner : properTransfer hn 0 1 = 1 :=
    transfer_last_column hn (properVectors 2)
      (fun _ hf => SnF_bounded (mem_properVectors.mp hf))
      (fun _ hf => SnF_fixed hn (mem_properVectors.mp hf))
      (fun _ hk => mem_properVectors.mpr (skeleton_mem_SnF hk))
      (fun _ hf => SnF_terminal (mem_properVectors.mp hf)) 0
  unfold proper
  rw [proper_count_as_entry hn, proper_count_as_entry hn]
  exact powers_two_by_two _ ht.2 (ht.1 1 0 (by decide)) hcorner

private theorem lattice_two : lattice 2 0 = 2 ∧ lattice 2 1 = 3 := by
  have hn : 1 ≤ (2 : ℕ) := by decide
  have ht := latticeTransfer_unitriangular hn
  have hcorner : latticeTransfer hn 0 1 = 1 :=
    transfer_last_column hn (latticeVectors hn)
      (fun _ hf => normalized_one_bounded hn ((mem_latticeVectors hn).mp hf))
      (fun _ hf => normalized_one_fixed hn ((mem_latticeVectors hn).mp hf))
      (fun _ hk => skeleton_mem_latticeVectors hn hk)
      (fun _ hf => lattice_terminal hn hf) 0
  unfold lattice
  rw [lattice_count_as_entry hn, lattice_count_as_entry hn]
  exact powers_two_by_two _ ht.2 (ht.1 1 0 (by decide)) hcorner

private theorem depends_on_rank {count : ℕ → ℕ → ℕ}
    (h : count 2 0 = 2 ∧ count 2 1 = 3) :
    ObservationalDependence signature (makeReadout count) := by
  intro _
  refine ⟨2, 0, 1, ?_⟩
  change count 2 0 ≠ count 2 1
  rw [h.1, h.2]
  decide

private def offset (count : ℕ → ℕ → ℕ) : Realization signature :=
  makeReadout fun n r => count n r + 1

private theorem proper_offset_fails : ¬ properArena.Law (offset proper) := by
  intro h
  have h0 := proper_count_as_entry (n := 1) le_rfl 0
  have h' := h (n := 1) le_rfl 0
  change proper 1 0 + 1 = _ at h'
  change proper 1 0 = _ at h0
  omega

private theorem lattice_offset_fails : ¬ latticeArena.Law (offset lattice) := by
  intro h
  have h0 := lattice_count_as_entry (n := 1) le_rfl 0
  have h' := h (n := 1) le_rfl 0
  change lattice 1 0 + 1 = _ at h'
  change lattice 1 0 = _ at h0
  omega

def properSource : Registration properArena (type_of% (@proper_count_as_entry)) where
  actual := realize signature (fun _ n r => (properSumset n (r + 1)).ncard) (fun e _ => e.elim)
  bridge := Iff.rfl
  variation := ⟨@proper_count_as_entry, offset proper, proper_offset_fails⟩
  sensitivity := by
    refine ⟨fun i => ⟨offset proper, ?_, rfl, proper_offset_fails⟩, fun e => e.elim⟩
    intro j h
    exact (h (Subsingleton.elim j i)).elim
  dependence := depends_on_rank proper_two

def latticeSource : Registration latticeArena (type_of% (@lattice_count_as_entry)) where
  actual := realize signature (fun _ n r => (dilateLattice n (r + 1)).ncard) (fun e _ => e.elim)
  bridge := Iff.rfl
  variation := ⟨@lattice_count_as_entry, offset lattice, lattice_offset_fails⟩
  sensitivity := by
    refine ⟨fun i => ⟨offset lattice, ?_, rfl, lattice_offset_fails⟩, fun e => e.elim⟩
    intro j h
    exact (h (Subsingleton.elim j i)).elim
  dependence := depends_on_rank lattice_two

def properRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@proper_count_as_entry) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Kozlov.proper_count_as_entry.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Kozlov.TransferEndpoints.properSource
  realizationSource := none
  generated := false
  arena := .source ⟨properArena⟩
  objectArena := .source ⟨properArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source properArena ⟨properSource⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => (properSumset n (r + 1)).ncard) (fun e _ => e.elim))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Kozlov.TransferEndpoints
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

def latticeRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@lattice_count_as_entry) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Kozlov.lattice_count_as_entry.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Kozlov.TransferEndpoints.latticeSource
  realizationSource := none
  generated := false
  arena := .source ⟨latticeArena⟩
  objectArena := .source ⟨latticeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source latticeArena ⟨latticeSource⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => (dilateLattice n (r + 1)).ncard) (fun e _ => e.elim))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Kozlov.TransferEndpoints
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Kozlov.TransferEndpoints
