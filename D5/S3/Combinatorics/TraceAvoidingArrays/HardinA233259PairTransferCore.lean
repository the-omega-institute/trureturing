/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.finite_certificate
   digest: Core definitions for the four-row one-sided pair transfer. -/
/-
admission_basis: open-problem-resolution (#28807; Proved)
escape_witness: none
direct_frozen_dependencies (raw compiled type/value edges, union over this module):
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Col
    statement_id: sha256:58a96b00c700fdc2e97a60f41346130ba89366c81c08a686797df427656983c2
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column
    statement_id: sha256:4ce9aae1f7889d98efb177000bdd5001f59a8f6dc7b63fee53ea3e2c52ee8dc6
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.cls
    statement_id: sha256:c3077252f291946d2b7b564604c605d22a44010fe93d7f5d5ba8942e5d9bb419
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.representatives
    statement_id: sha256:2067f4c2cdcabcf8935a46363352f15a911bd40b5940776cc4c9ae101d987369
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.relabel
    statement_id: sha256:88389d32894c39de84bddac27d8616d8e252a5def677b3daa530bb191313d97a
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.gridEquiv
    statement_id: sha256:f9e4b8b07e31a38f83f46de0213688dae683ba0a7a828eab02e6212deccb1748
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_grid
    statement_id: sha256:68cd26e474b822bca602484f4f63cbe173ffd3258de0d3745a9e328d671cef3d
  D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_relabel
    statement_id: sha256:c5015d866b36983cd7bccd75417c814d35b5e5c73c7b5075679455ee599212aa
reused_unfrozen: TransferMatrix.good_iff_local
Col: proof_shape=bind-only; consumers=column, cls, representatives, relabel, compatible
column: proof_shape=bind-only; consumers=compatible, compatible_relabel
cls: proof_shape=bind-only; consumers=Q, representatives
representatives: proof_shape=bind-only; consumers=Q, class_rep
relabel: proof_shape=bind-only; consumers=compatible_relabel, class_rep
compatible: proof_shape=bind-only; consumers=compatible_relabel, representative_rows, quotient_rows, initial_weights, grid_good, count_transfer
Q: proof_shape=bind-only; consumers=representative_rows, quotient_rows, count_transfer, table_steps, powers_table, power_polynomial
weights: proof_shape=bind-only; consumers=initial_weights, count_transfer, initial_values
compatible_relabel: proof_shape=bind-only; consumers=quotient_rows
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore

abbrev Col := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col
abbrev column := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.column
abbrev cls := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.cls
abbrev representatives := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.representatives
abbrev relabel := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.relabel
abbrev gridEquiv := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.gridEquiv
abbrev column_grid := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.column_grid

def compatible (a b : Col) : Prop :=
  ∀ r s : Fin 4, (r = s ∨ r.val + 1 = s.val) → column a s ≠ column b r

instance instDecidableCompatible (a b : Col) : Decidable (compatible a b) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _))

def Proper {n : ℕ} (P : Fin 4 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 4),
    (r = s ∨ r.val + 1 = s.val) →
    P (s, j) ≠ P (r, ⟨j.val + 1, h⟩)

private instance instDecidableProper {n : ℕ} (P : Fin 4 × Fin n → Fin 3) :
    Decidable (Proper P) := inferInstanceAs (Decidable (∀ _ _ _ _, _ → _))

def L (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Fin 4 × Fin n → Fin 3 => Proper P)).card

theorem grid_good (n : ℕ) (P : Fin 4 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good compatible (fun _ _ _ => True)
      (List.ofFn (gridEquiv n P)) := by
  rw [TransferMatrix.good_iff_local]
  simp only [List.length_ofFn, implies_true, and_true]
  constructor
  · intro h
    intro j hj
    change ∀ r s : Fin 4, (r = s ∨ r.val + 1 = s.val) →
      column ((List.ofFn (gridEquiv n P)).getD j default) s ≠
        column ((List.ofFn (gridEquiv n P)).getD (j + 1) default) r
    intro r s hrs
    have hj0 : j < n := by omega
    have hh := h ⟨j, hj0⟩ hj r s hrs
    simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj0, hj,
      compatible, column_grid] using hh
  · intro h j hj r s hrs
    have hh := h j.val hj
    change ∀ r s : Fin 4, (r = s ∨ r.val + 1 = s.val) →
      column ((List.ofFn (gridEquiv n P)).getD j.val default) s ≠
        column ((List.ofFn (gridEquiv n P)).getD (j.val + 1) default) r at hh
    have hh := hh r s hrs
    simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, hj,
      compatible, column_grid] using hh

def Q : Matrix (Fin 14) (Fin 14) ℤ :=
  ![![2,2,2,2,0,2,2,0,2,2,0,0,0,0],
    ![1,1,0,1,1,1,0,1,0,1,1,0,0,0],
    ![1,1,0,0,0,0,0,0,1,1,0,0,0,0],
    ![1,1,1,1,0,0,0,0,0,1,1,0,1,1],
    ![0,0,0,1,1,0,0,0,0,0,0,1,0,1],
    ![1,1,1,1,0,0,0,0,0,0,0,0,0,0],
    ![1,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,1,1,0,0,0,0,0,0,0,0,0],
    ![1,1,0,0,0,1,0,1,0,0,0,0,0,0],
    ![1,1,1,1,0,1,1,0,1,1,0,0,0,0],
    ![0,0,0,1,1,0,0,0,0,1,1,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,1,0,1],
    ![0,0,0,0,0,0,0,0,1,1,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,1,1,0,1,1]]

def weights : Fin 14 → ℤ := ![48,48,24,48,24,24,12,12,24,48,24,12,12,24]

theorem compatible_relabel (e : Equiv.Perm (Fin 3)) (a b : Col) :
    compatible (relabel e a) (relabel e b) ↔ compatible a b := by
  simp only [compatible,
    _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.column_relabel,
    e.injective.ne_iff]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
