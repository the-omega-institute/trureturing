/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Core definitions for the four-row one-sided pair transfer. -/
/-
admission_basis: open-problem-resolution (#28807; Proved)
admission_consumers: HardinA233259PairTransferCount.count_transfer, HardinA233259PairTransferRep.quotient_rows, HardinA233259Strip.counting_bridge
The matrix and weights are definitions; the predicate transports certify no numeric inputs.
All declarations are structural setup, with no bounded enumeration, checker, numeric reduction
or certified instance; utility kind=none.
escape_witness: none (consumed setup; grid_good and compatible_relabel transport the literal one-sided predicate)
compatible: proof_shape=bind-only; consumers=instDecidableCompatible, grid_good, compatible_relabel, HardinA233259PairTransferRep.representative_rows, HardinA233259PairTransferInitial.initial_weights, HardinA233259PairTransferCount.count_transfer
instDecidableCompatible: proof_shape=bind-only; consumers=HardinA233259PairTransferRep.representative_rows, HardinA233259PairTransferInitial.initial_weights, HardinA233259PairTransferRep.quotient_rows, HardinA233259PairTransferCount.count_transfer
Proper: proof_shape=bind-only; consumers=instDecidableProper, L, grid_good, HardinA233259Strip.legal_iff
instDecidableProper: proof_shape=bind-only; consumers=L
L: proof_shape=bind-only; consumers=HardinA233259PairTransferCount.count_transfer, HardinA233259Strip.L_card
grid_good: proof_shape=bind-only; consumers=HardinA233259PairTransferCount.count_transfer
Q: proof_shape=bind-only; consumers=HardinA233259PairTransferRep.representative_rows, HardinA233259PairTransferCount.count_transfer, HardinA233259PairTransferPowers.table_steps, HardinA233259PairTransferPowers.power_polynomial
weights: proof_shape=bind-only; consumers=HardinA233259PairTransferInitial.initial_weights, HardinA233259PairTransferCount.count_transfer
compatible_relabel: proof_shape=bind-only; consumers=HardinA233259PairTransferRep.quotient_rows
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore

open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer (Col column relabel gridEquiv column_grid)

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
