/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Literal three-state strips admit a width-generic row counting and quotient bridge. -/

/-
admission_basis: open-problem-resolution (#29204; Proved)
escape_witness: none
The bridges transport literal functions through currying and the existing
TransferMatrix.cardMatrix theorem. They contain no numerical computation.
All declarations have proof_shape=bind-only and are consumed by the three columns.
Row: proof_shape=bind-only; consumers=rowLegal, compatible, decidableRowLegal, decidableCompatible, decode, row_sum, row_sequence_bridge, pair, good_iff, count_transfer
rowLegal: proof_shape=bind-only; consumers=decidableRowLegal, Legal, legalCodes, row_sum, row_sequence_bridge, pair, good_iff, count_transfer
compatible: proof_shape=bind-only; consumers=decidableCompatible, Legal, row_sequence_bridge, pair, good_iff, count_transfer
decidableRowLegal: proof_shape=bind-only; consumers=legalCodes, decidableLegal
decidableCompatible: proof_shape=bind-only; consumers=decidableLegal
Legal: proof_shape=bind-only; consumers=decidableLegal, T
decidableLegal: proof_shape=bind-only; consumers=T
T: proof_shape=bind-only; consumers=row_sequence_bridge, count_transfer
decode: proof_shape=bind-only; consumers=legalCodes, row_sum
legalCodes: proof_shape=bind-only; consumers=row_sum
row_sum: proof_shape=bind-only; consumers=HardinA233152Column.row_counts, HardinA233153Column.row_counts, HardinA233154Column.row_counts
row_sequence_bridge: proof_shape=bind-only; consumers=count_transfer
pair: proof_shape=bind-only; consumers=good_iff, count_transfer
good_iff: proof_shape=bind-only; consumers=count_transfer
count_transfer: proof_shape=bind-only; consumers=HardinA233152Column.counting_bridge, HardinA233153Column.counting_bridge, HardinA233154Column.counting_bridge
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic

/-! Row coordinates preserve the literal horizontal and antidiagonal constraints. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open scoped BigOperators

abbrev Row (k : ℕ) := Fin k → Fin 3

def rowLegal {k : ℕ} (r : Row k) : Prop :=
  ∀ (j : Fin k) (h : j.val + 1 < k),
    (r j).val + (r ⟨j.val + 1, h⟩).val ≠ 2

def compatible {k : ℕ} (r s : Row k) : Prop :=
  ∀ (j : Fin k) (h : j.val + 1 < k),
    (r ⟨j.val + 1, h⟩).val + (s j).val ≠ 2

private instance decidableRowLegal {k : ℕ} (r : Row k) : Decidable (rowLegal r) :=
  inferInstanceAs (Decidable (∀ _ _, _))
private instance decidableCompatible {k : ℕ} (r s : Row k) : Decidable (compatible r s) :=
  inferInstanceAs (Decidable (∀ _ _, _))

def Legal {k n : ℕ} (f : Fin n × Fin k → Fin 3) : Prop :=
  (∀ i, rowLegal (fun j => f (i, j))) ∧
  (∀ (i : Fin n) (h : i.val + 1 < n),
    compatible (fun j => f (i, j)) (fun j => f (⟨i.val + 1, h⟩, j)))

private instance decidableLegal {k n : ℕ} (f : Fin n × Fin k → Fin 3) :
    Decidable (Legal f) := inferInstanceAs (Decidable (_ ∧ _))

def T (k n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n × Fin k → Fin 3 => Legal f)).card

def decode (k : ℕ) (c : Fin (3 ^ k)) : Row k := finFunctionFinEquiv.symm c

def legalCodes (k : ℕ) : List (Fin (3 ^ k)) :=
  (List.finRange (3 ^ k)).filter (fun c => decide (rowLegal (decode k c)))

theorem row_sum (k : ℕ) (F : Row k → ℤ) :
    (∑ r : Row k, if rowLegal r then F r else 0) =
      ((legalCodes k).map (fun c => F (decode k c))).sum := by
  rw [← (finFunctionFinEquiv (m := 3) (n := k)).symm.sum_comp]
  change (∑ c : Fin (3 ^ k), if rowLegal (decode k c) then F (decode k c) else 0) = _
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  unfold legalCodes
  generalize List.finRange (3 ^ k) = l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : rowLegal (decode k c) <;> simp [h, ih]

theorem row_sequence_bridge (k n : ℕ) :
    T k (n + 1) = Nat.card {r : Fin (n + 1) → Row k //
      (∀ i, rowLegal (r i)) ∧
      (∀ (i : Fin (n + 1)) (h : i.val + 1 < n + 1),
        compatible (r i) (r ⟨i.val + 1, h⟩))} := by
  classical
  rw [T, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.curry (Fin (n + 1)) (Fin k) (Fin 3)) (fun _ => Iff.rfl))

private def pair {k : ℕ} (a b : Row k) : Prop :=
  rowLegal a ∧ rowLegal b ∧ compatible a b

private theorem good_iff (k n : ℕ) (f : Fin (n + 2) → Row k) :
    TransferMatrix.good pair (fun _ _ _ => True) (List.ofFn f) ↔
      (∀ i, rowLegal (f i)) ∧
      (∀ (i : Fin (n + 2)) (h : i.val + 1 < n + 2),
        compatible (f i) (f ⟨i.val + 1, h⟩)) := by
  rw [TransferMatrix.good_iff_local]
  simp only [List.length_ofFn, implies_true, and_true]
  have get (i : ℕ) (hi : i < n + 2) :
      (List.ofFn f).getD i default = f ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
  constructor
  · intro h
    constructor
    · intro i
      by_cases hi : i.val + 1 < n + 2
      · have hp := h i.val hi
        rw [get _ (by omega), get _ hi] at hp
        exact hp.1
      · have hp := h n (by omega)
        rw [get n (by omega), get (n + 1) (by omega)] at hp
        have he : i = (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          change i.val = n + 1
          omega
        simpa only [he] using hp.2.1
    · intro i hi
      have hp := h i.val hi
      rw [get _ (by omega), get _ hi] at hp
      exact hp.2.2
  · rintro ⟨hr, hc⟩ i hi
    rw [get _ (by omega), get _ hi]
    exact ⟨hr _, hr _, hc _ hi⟩

/-- A quotient with certified row fibres counts every positive strip after its first row. -/
theorem count_transfer (k q : ℕ) (cls : Row k → Fin q)
    (Q : Matrix (Fin q) (Fin q) ℤ) (w : Fin q → ℤ)
    (hQ : ∀ r, rowLegal r → ∀ s,
      (∑ c : Row k, if rowLegal c ∧ compatible r c ∧ cls c = s then (1 : ℤ) else 0) =
        Q (cls r) s)
    (hw : ∀ s, (∑ r : Row k, if rowLegal r ∧ cls r = s then (1 : ℤ) else 0) = w s)
    (n : ℕ) :
    (T k (n + 2) : ℤ) = dotProduct w ((Q ^ (n + 1)).mulVec (1 : Fin q → ℤ)) := by
  classical
  let v : Fin q → ℤ := fun s => ∑ t, w t * Q t s
  have ht : ∀ a b, pair a b → ∀ s,
      (∑ c : Row k, if pair b c ∧ True ∧ cls c = s then (1 : ℤ) else 0) = Q (cls b) s := by
    intro a b hab s
    simpa [pair, hab.2.1, and_assoc] using hQ b hab.2.1 s
  have hv : ∀ s, (∑ a : Row k, ∑ b : Row k,
      if pair a b ∧ cls b = s then (1 : ℤ) else 0) = v s := by
    intro s
    calc
      _ = ∑ a : Row k, if rowLegal a then Q (cls a) s else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : rowLegal a
        · simpa [pair, ha, and_assoc] using hQ a ha s
        · simp [pair, ha]
      _ = ∑ t : Fin q, w t * Q t s := by
        simp_rw [← hw, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : rowLegal a <;> simp [ha]
  have hcard : (T k (n + 2) : ℤ) =
      (Nat.card {f : Fin (n + 2) → Row k //
        TransferMatrix.good pair (fun _ _ _ => True) (List.ofFn f)} : ℤ) := by
    have hb := row_sequence_bridge k (n + 1)
    rw [show n + 1 + 1 = n + 2 by omega] at hb
    rw [hb]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun f => (good_iff k n f).symm))
  have hm := @TransferMatrix.cardMatrix (Row k) (Fin q) inferInstance inferInstance
    inferInstance pair (fun _ _ _ => True) (fun _ b => cls b) Q v
    (by intro a b hab s; simpa only [true_and] using ht a b hab s)
    (by intro s; exact hv s) n
  rw [hcard, hm]
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  change (∑ s, (∑ t, w t * Q t s) * ((Q ^ n).mulVec 1) s) =
    ∑ t, w t * (∑ s, Q t s * ((Q ^ n).mulVec 1) s)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
