/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Column quotients count literal three-state strips of length at least two. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: grid_good -> TransferMatrix.good_iff_local (W1: arbitrary-list locality);
count_transfer -> TransferMatrix.cardMatrix -> TransferMatrix.cont_matrix (W2: induction
over every continuation length). TransferMatrix is unfrozen on the protected baseline;
successor_sum, quotient_rows and properEquiv are bind-only.
columnCompatible: proof_shape=bind-only; consumers=successorClasses, count_transfer
instDecidableColumnCompatible: proof_shape=bind-only; consumers=successorClasses
relabel: proof_shape=bind-only; consumers=compatible_relabel, quotient_rows
complement_bond: proof_shape=bind-only; consumers=alternating_legal
alternatingEquiv: proof_shape=bind-only; consumers=alternating_legal, properEquiv
alternating_legal: proof_shape=bind-only; consumers=properEquiv
properEquiv: proof_shape=bind-only; consumers=HardinA233156Row.counting_bridge, HardinA233157Row.counting_bridge, HardinA233158Row.counting_bridge
twist: proof_shape=bind-only; consumers=compatible_relabel, quotient_rows
bond_relabel: proof_shape=bind-only; consumers=compatible_relabel
compatible_relabel: proof_shape=bind-only; consumers=quotient_rows
successorClasses: proof_shape=bind-only; consumers=successor_sum, quotient_rows
successor_sum: proof_shape=bind-only; consumers=quotient_rows
quotient_rows: proof_shape=bind-only; consumers=HardinA233159RowCertificate.row_counts
grid_good: proof_shape=content; consumers=count_transfer
count_transfer: proof_shape=content; consumers=HardinA233159Row.counting_bridge
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-! Horizontal and antidiagonal bonds connect successive unrestricted columns. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators

def columnCompatible {k : ℕ} (r s : Row k) : Prop :=
  (∀ i, (r i).val + (s i).val ≠ 2) ∧
  (∀ (i : Fin k) (h : i.val + 1 < k),
    (s i).val + (r ⟨i.val + 1, h⟩).val ≠ 2)
private instance instDecidableColumnCompatible {k : ℕ} (r s : Row k) :
    Decidable (columnCompatible r s) := inferInstanceAs (Decidable (_ ∧ _))

def relabel {k : ℕ} (e : Equiv.Perm (Fin 3)) : Row k ≃ Row k :=
  Equiv.arrowCongr (Equiv.refl _) e
private theorem complement_bond : ∀ x y : Fin 3,
    x ≠ (Fin.revPerm (n := 3)) y ↔ x.val + y.val ≠ 2 := by decide +kernel

/-- Complement labels in each odd column, preserving every labelled array. -/
private def alternatingEquiv (k n : ℕ) :
    (Fin k × Fin n → Fin 3) ≃ (Fin k × Fin n → Fin 3) :=
  Equiv.piCongrRight (fun p => (Fin.revPerm (n := 3)) ^ p.2.val)

private theorem alternating_legal (k n : ℕ) (f : Fin k × Fin n → Fin 3) :
    Legal f ↔ ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin k),
      (r = s ∨ r.val = s.val + 1) →
      alternatingEquiv k n f (r, j) ≠
        alternatingEquiv k n f (s, ⟨j.val + 1, h⟩) := by
  have bond (j : ℕ) (x y : Fin 3) :
      ((Fin.revPerm (n := 3)) ^ j) x ≠ ((Fin.revPerm (n := 3)) ^ (j + 1)) y ↔ x.val + y.val ≠ 2 := by
    rw [pow_succ, Equiv.Perm.mul_apply, ((Fin.revPerm (n := 3)) ^ j).injective.ne_iff]
    exact complement_bond x y
  change Legal f ↔ ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin k),
    (r = s ∨ r.val = s.val + 1) →
      ((Fin.revPerm (n := 3)) ^ j.val) (f (r, j)) ≠
        ((Fin.revPerm (n := 3)) ^ (j.val + 1)) (f (s, ⟨j.val + 1, h⟩))
  constructor
  · intro hf j hj r s hrs
    apply (bond _ _ _).2
    rcases hrs with rfl | hrs
    · exact hf.1 r j hj
    · have hs : s.val + 1 < k := by omega
      have hr : r = ⟨s.val + 1, hs⟩ := Fin.ext hrs
      simpa only [hr, Nat.add_comm] using hf.2 s hs j hj
  · intro hf
    constructor
    · intro r j hj
      exact (bond _ _ _).1 (hf j hj r r (Or.inl rfl))
    · intro s hs j hj
      have hb := (bond _ _ _).1 (hf j hj ⟨s.val + 1, hs⟩ s (Or.inr rfl))
      simpa only [Nat.add_comm] using hb

/-- The alternating permutation carries sum exclusion exactly to proper colouring. -/
def properEquiv (k n : ℕ) :
    {f : Fin k × Fin n → Fin 3 // Legal f} ≃
    {P : Fin k × Fin n → Fin 3 //
      ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin k),
        (r = s ∨ r.val = s.val + 1) → P (r, j) ≠ P (s, ⟨j.val + 1, h⟩)} :=
  Equiv.subtypeEquiv (alternatingEquiv k n) (alternating_legal k n)

private def twist (e : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) :=
  (Fin.revPerm (n := 3)).permCongr e
private theorem bond_relabel : ∀ (e : Equiv.Perm (Fin 3)) (x y : Fin 3),
    (e x).val + (twist e y).val ≠ 2 ↔ x.val + y.val ≠ 2 := by decide +kernel
private theorem compatible_relabel {k : ℕ} (e : Equiv.Perm (Fin 3)) (r s : Row k) :
    columnCompatible (relabel e r) (relabel (twist e) s) ↔ columnCompatible r s := by
  change columnCompatible (fun i => e (r i)) (fun i => twist e (s i)) ↔ _
  simp only [columnCompatible, Nat.add_comm (twist e _).val, bond_relabel]
  simp only [Nat.add_comm]


def successorClasses {k q : ℕ} (cls : Row k → Fin q) (r : Row k) : List (Fin q) :=
  (((List.finRange (3 ^ k)).filter (fun c => decide (columnCompatible r (decode k c)))).map
    (fun c => cls (decode k c)))
private theorem successor_sum {k q : ℕ} (cls : Row k → Fin q) (r : Row k) (s : Fin q) :
    (∑ c : Row k, if columnCompatible r c ∧ cls c = s then (1 : ℤ) else 0) =
      ((successorClasses cls r).map (fun j => if j = s then (1 : ℤ) else 0)).sum := by
  rw [← (finFunctionFinEquiv (m := 3) (n := k)).symm.sum_comp]
  change (∑ c : Fin (3 ^ k), if columnCompatible r (decode k c) ∧
    cls (decode k c) = s then (1 : ℤ) else 0) = _
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  unfold successorClasses
  simp only [List.map_map, Function.comp_def, ite_and]
  rw [List.sum_map_ite]
  simp

theorem quotient_rows (k q : ℕ) (cls : Row k → Fin q) (rep : Fin q → Row k)
    (Q : Matrix (Fin q) (Fin q) ℤ)
    (hcls : ∀ (e : Equiv.Perm (Fin 3)) r, cls (relabel e r) = cls r)
    (hrep : ∀ r, ∃ e : Equiv.Perm (Fin 3), relabel e r = rep (cls r))
    (htable : ∀ i s, ((successorClasses cls (rep i)).map
      (fun j => if j = s then (1 : ℤ) else 0)).sum = Q i s)
    (r : Row k) (s : Fin q) :
    (∑ c : Row k, if columnCompatible r c ∧ cls c = s then (1 : ℤ) else 0) =
      Q (cls r) s := by
  obtain ⟨e, he⟩ := hrep r
  calc
    _ = ∑ c : Row k, if columnCompatible (relabel e r) (relabel (twist e) c) ∧
        cls (relabel (twist e) c) = s then (1 : ℤ) else 0 := by
      simp only [compatible_relabel, hcls]
    _ = ∑ c : Row k, if columnCompatible (rep (cls r)) c ∧ cls c = s
        then (1 : ℤ) else 0 := by
      rw [he]
      exact (relabel (twist e)).sum_comp (fun c : Row k =>
        if columnCompatible (rep (cls r)) c ∧ cls c = s then (1 : ℤ) else 0)
    _ = _ := (successor_sum cls _ s).trans (htable _ _)

private theorem grid_good (k n : ℕ) (f : Fin k × Fin (n + 2) → Fin 3) :
    Legal f ↔ TransferMatrix.good columnCompatible (fun _ _ _ => True)
      (List.ofFn (fun j i => f (i, j))) := by
  rw [TransferMatrix.good_iff_local]
  simp only [List.length_ofFn, implies_true, and_true]
  have get (i : ℕ) (hi : i < n + 2) :
      (List.ofFn (fun j r => f (r, j))).getD i default = fun r => f (r, ⟨i, hi⟩) := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
  constructor
  · intro h j hj
    rw [get _ (by omega), get _ hj]
    exact ⟨fun i => h.1 i ⟨j, by omega⟩ hj,
      fun i hi => h.2 i hi ⟨j, by omega⟩ hj⟩
  · intro h
    constructor
    · intro i j hj
      have hh := h j.val hj
      rw [get _ (by omega), get _ hj] at hh
      exact hh.1 i
    · intro i hi j hj
      have hh := h j.val hj
      rw [get _ (by omega), get _ hj] at hh
      exact hh.2 i hi

theorem count_transfer (k q : ℕ) (cls : Row k → Fin q)
    (Q : Matrix (Fin q) (Fin q) ℤ) (w : Fin q → ℤ)
    (hQ : ∀ r s, (∑ c : Row k, if columnCompatible r c ∧ cls c = s
      then (1 : ℤ) else 0) = Q (cls r) s)
    (hw : ∀ s, (∑ r : Row k, if cls r = s then (1 : ℤ) else 0) = w s)
    (n : ℕ) :
    (T (n + 2) k : ℤ) = dotProduct w ((Q ^ (n + 1)).mulVec (1 : Fin q → ℤ)) := by
  classical
  let v : Fin q → ℤ := fun s => ∑ t, w t * Q t s
  have hv : ∀ s, (∑ a : Row k, ∑ b : Row k,
      if columnCompatible a b ∧ cls b = s then (1 : ℤ) else 0) = v s := by
    intro s
    simp_rw [hQ]
    change (∑ a : Row k, Q (cls a) s) = ∑ t, w t * Q t s
    simp_rw [← hw, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  let e : (Fin k × Fin (n + 2) → Fin 3) ≃ (Fin (n + 2) → Row k) :=
    (Equiv.arrowCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans (Equiv.curry _ _ _)
  have hc : T (n + 2) k = Nat.card {g : Fin (n + 2) → Row k //
      TransferMatrix.good columnCompatible (fun _ _ _ => True) (List.ofFn g)} := by
    rw [T, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquiv e (fun f => grid_good k n f))
  have hm := @TransferMatrix.cardMatrix (Row k) (Fin q) inferInstance inferInstance
    inferInstance columnCompatible (fun _ _ _ => True) (fun _ b => cls b) Q v
    (by intro a b _ s; simpa only [true_and] using hQ b s)
    (by
      intro s
      apply Eq.trans ?_ (hv s)
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : columnCompatible a b ∧ cls b = s <;> simp [h]) n
  rw [hc, hm, pow_succ', ← Matrix.mulVec_mulVec]
  change (∑ s, (∑ t, w t * Q t s) * ((Q ^ n).mulVec 1) s) =
    ∑ t, w t * (∑ s, Q t s * ((Q ^ n).mulVec 1) s)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
