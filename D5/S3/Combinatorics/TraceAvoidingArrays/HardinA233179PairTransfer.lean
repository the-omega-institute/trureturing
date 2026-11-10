/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.finite_certificate
   digest: Six-row raw-column transfer have a fourteen-class column transfer and sextic tail. -/
/-
admission_basis: open-problem-resolution (#28449; Proved)
escape_witness: none
direct_frozen_dependencies (raw compiled type/value edges, union over this module): []
The transfer and power iteration instantiate existing TransferMatrix results;
the finite column tables and product/subtype transports add only normalization.
Proper: proof_shape=bind-only; consumers=L, grid_good
instDecidableProper: proof_shape=bind-only; consumers=L
L: proof_shape=bind-only; consumers=count_transfer
Col: proof_shape=bind-only; consumers=compatible, gridEquiv
column: proof_shape=bind-only; consumers=compatible, gridEquiv
compatible: proof_shape=bind-only; consumers=quotient_rows, grid_good
instDecidableCompatible: proof_shape=bind-only; consumers=quotient_rows
cls: proof_shape=bind-only; consumers=quotient_rows
Q: proof_shape=bind-only; consumers=count_transfer, powers_table
weights: proof_shape=bind-only; consumers=count_transfer
representatives: proof_shape=bind-only; consumers=class_rep, representative_rows
relabel: proof_shape=bind-only; consumers=column_relabel, class_rep
column_relabel: proof_shape=bind-only; consumers=compatible_relabel
compatible_relabel: proof_shape=bind-only; consumers=quotient_rows
class_relabel: proof_shape=bind-only; consumers=quotient_rows
class_rep: proof_shape=bind-only; consumers=quotient_rows
representative_rows: proof_shape=bind-only; consumers=quotient_rows
quotient_rows: proof_shape=bind-only; consumers=count_transfer
initial_weights: proof_shape=bind-only; consumers=count_transfer
gridEquiv: proof_shape=bind-only; consumers=grid_good, count_transfer
column_grid: proof_shape=bind-only; consumers=grid_good
tail_iff: proof_shape=bind-only; consumers=good_iff
good_iff: proof_shape=bind-only; consumers=grid_good
grid_good: proof_shape=bind-only; consumers=count_transfer
count_transfer: proof_shape=bind-only; consumers=initial_values, sextic
W: proof_shape=bind-only; consumers=powers_table
coefficients: proof_shape=bind-only; consumers=power_polynomial, sextic
table_zero: proof_shape=bind-only; consumers=powers_table
table_steps: proof_shape=bind-only; consumers=powers_table
powers_table: proof_shape=bind-only; consumers=power_polynomial, initial_values
power_polynomial: proof_shape=bind-only; consumers=sextic
initial_values: proof_shape=bind-only; consumers=HardinA233177Ladder.finite_certificate
sextic: proof_shape=bind-only; consumers=recurrence
recurrence: proof_shape=bind-only; consumers=HardinA233177Ladder.result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransferData
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! Pair labels alone determine the column transfer. -/
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays

def Proper {n : ℕ} (P : Fin 6 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 6),
    (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
    P (r, j) ≠ P (s, ⟨j.val + 1, h⟩)
private instance instDecidableProper {n : ℕ} (P : Fin 6 × Fin n → Fin 3) :
    Decidable (Proper P) := inferInstanceAs (Decidable (∀ _ _ _ _, _ → _))
def L (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Fin 6 × Fin n → Fin 3 => Proper P)).card

private def gridEquiv (n : ℕ) : (Fin 6 × Fin n → Fin 3) ≃ (Fin n → Col) where
  toFun P j := (P (0,j), P (1,j), P (2,j), P (3,j), P (4,j), P (5,j))
  invFun f p := column (f p.2) p.1
  left_inv P := by funext p; rcases p with ⟨r,j⟩; fin_cases r <;> rfl
  right_inv f := rfl
private theorem column_grid (n : ℕ) (P : Fin 6 × Fin n → Fin 3)
    (j : Fin n) (r : Fin 6) : column (gridEquiv n P j) r = P (r,j) := by
  fin_cases r <;> rfl
private theorem tail_iff (a b : Col) (xs : List Col) :
    TransferMatrix.tailGood compatible (fun _ _ _ => True) a b xs ↔
      (b :: xs).IsChain compatible := by
  induction xs generalizing a b with
  | nil => simp [TransferMatrix.tailGood]
  | cons c xs ih => simp [TransferMatrix.tailGood, List.isChain_cons_cons, ih]
private theorem good_iff (xs : List Col) :
    TransferMatrix.good compatible (fun _ _ _ => True) xs ↔ xs.IsChain compatible := by
  cases xs with
  | nil => simp [TransferMatrix.good]
  | cons a xs =>
    cases xs with
    | nil => simp [TransferMatrix.good]
    | cons b xs => simp [TransferMatrix.good, tail_iff, List.isChain_cons_cons]
private theorem grid_good (n : ℕ) (P : Fin 6 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good compatible (fun _ _ _ => True)
      (List.ofFn (gridEquiv n P)) := by
  rw [good_iff, List.isChain_ofFn]
  simp only [Proper, compatible, column_grid]
  constructor
  · intro h j hj; exact h ⟨j, by omega⟩ hj
  · intro h j hj; exact h j.val hj
private theorem count_transfer (n : ℕ) :
    (L (n+2) : ℤ) = dotProduct weights ((T^n).mulVec (1 : Col → ℤ)) := by
  classical
  let he : {P : Fin 6 × Fin (n+2) → Fin 3 // Proper P} ≃
      {f : Fin (n+2) → Col //
        TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} :=
    Equiv.subtypeEquiv (gridEquiv (n+2)) (fun P => grid_good (n+2) P)
  have hc : L (n+2) = Nat.card {f : Fin (n+2) → Col //
      TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} := by
    rw [← Nat.card_congr he]
    simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  refine TransferMatrix.cardMatrix compatible (fun _ _ _ => True) (fun _ b => b)
    T weights ?_ ?_ n
  · intro a b _ s
    rw [Finset.sum_eq_single s]
    · simp [T]
    · intro c _ hcs
      simp [hcs]
    · simp
  · intro s
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_eq_single s]
    · simp
    · intro b hb hbs
      simp [hbs]
    · simp
private theorem table_zero : W 0 = (1 : Col → ℤ) := by
  native_decide
private theorem table_steps : ∀ k : Fin 24, W k.succ = T.mulVec (W k.castSucc) := by
  native_decide
private theorem powers_table : ∀ k : Fin 25,
    (T^k.val).mulVec (1 : Col → ℤ) = W k :=
  TransferMatrix.tabulatedPowers T 24 W table_zero table_steps
private theorem power_polynomial : (T^24).mulVec (1 : Col → ℤ) =
    ∑ j : Fin 24, coefficients j • (T^j.val).mulVec (1 : Col → ℤ) := by
  change W 24 = ∑ j : Fin 24, coefficients j • (T^j.val).mulVec (1 : Col → ℤ)
  have hh (j : Fin 24) : (T^j.val).mulVec (1 : Col → ℤ) = W ⟨j.val, by omega⟩ := powers_table ⟨j.val, by omega⟩
  simp_rw [hh]
  native_decide
private theorem recurrence_core (n : ℕ) : (L (n+26) : ℤ) + 6 =
    ∑ j : Fin 24, coefficients j * ((L (n+j.val+2) : ℤ) + 6) := by
  have h := TransferMatrix.scalarRelationShift T weights 24 0 coefficients power_polynomial n
  have ht (k : ℕ) : dotProduct weights ((T^k).mulVec (1 : Col → ℤ)) = (L (k+2) : ℤ) := (count_transfer k).symm
  simp_rw [ht] at h
  norm_num [coefficients, Fin.sum_univ_succ, Nat.add_assoc] at h ⊢
  linear_combination h
theorem recurrence (n : ℕ) : (L (n+26) : ℤ) + 6 =
    7 * ((L (n+25) : ℤ) + 6) + 103 * ((L (n+24) : ℤ) + 6) - 365 * ((L (n+23) : ℤ) + 6) - 2896 * ((L (n+22) : ℤ) + 6) + 7168 * ((L (n+21) : ℤ) + 6) + 32291 * ((L (n+20) : ℤ) + 6) - 75471 * ((L (n+19) : ℤ) + 6) - 161805 * ((L (n+18) : ℤ) + 6) + 426135 * ((L (n+17) : ℤ) + 6) + 333692 * ((L (n+16) : ℤ) + 6) - 1225001 * ((L (n+15) : ℤ) + 6) - 155206 * ((L (n+14) : ℤ) + 6) + 1850161 * ((L (n+13) : ℤ) + 6) - 363389 * ((L (n+12) : ℤ) + 6) - 1524689 * ((L (n+11) : ℤ) + 6) + 557502 * ((L (n+10) : ℤ) + 6) + 690388 * ((L (n+9) : ℤ) + 6) - 312941 * ((L (n+8) : ℤ) + 6) - 166928 * ((L (n+7) : ℤ) + 6) + 81406 * ((L (n+6) : ℤ) + 6) + 19997 * ((L (n+5) : ℤ) + 6) - 9672 * ((L (n+4) : ℤ) + 6) - 906 * ((L (n+3) : ℤ) + 6) + 420 * ((L (n+2) : ℤ) + 6) := by
  have h := recurrence_core n
  norm_num [coefficients, Fin.sum_univ_succ, Nat.add_assoc] at h
  linear_combination h
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
