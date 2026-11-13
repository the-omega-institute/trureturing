/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.finite_certificate
   digest: Four-row pair patterns have a fourteen-class column transfer and sextic tail. -/
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
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

/-! Pair labels alone determine the column transfer. -/
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays

def Proper {n : ℕ} (P : Fin 4 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 4),
    (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
    P (r, j) ≠ P (s, ⟨j.val + 1, h⟩)
private instance instDecidableProper {n : ℕ} (P : Fin 4 × Fin n → Fin 3) :
    Decidable (Proper P) := inferInstanceAs (Decidable (∀ _ _ _ _, _ → _))
def L (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Fin 4 × Fin n → Fin 3 => Proper P)).card

abbrev Col := Fin 3 × Fin 3 × Fin 3 × Fin 3
def column (c : Col) : Fin 4 → Fin 3 := ![c.1, c.2.1, c.2.2.1, c.2.2.2]
private def compatible (a b : Col) : Prop :=
  ∀ r s : Fin 4, (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) → column a r ≠ column b s
private instance instDecidableCompatible (a b : Col) : Decidable (compatible a b) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _))
def cls (c : Col) : Fin 14 :=
  let a := c.1; let b := c.2.1; let d := c.2.2.1; let e := c.2.2.2
  if a = b then
    if a = d then (if a = e then 0 else 1)
    else if a = e then 2 else if d = e then 3 else 4
  else if a = d then
    (if a = e then 5 else if b = e then 6 else 7)
  else if b = d then
    (if a = e then 8 else if b = e then 9 else 10)
  else if a = e then 11 else if b = e then 12 else 13
private def Q : Matrix (Fin 14) (Fin 14) ℤ :=
  ![![2,2,2,2,0,2,2,0,2,2,0,0,0,0],
    ![1,0,0,1,0,1,0,0,0,1,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,1,0,0,0,0],
    ![1,1,0,0,0,0,0,0,0,1,1,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,1,1,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,1,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def weights : Fin 14 → ℤ := ![48,24,12,24,0,12,6,0,6,24,6,0,0,0]

def representatives : Fin 14 → Col :=
  ![(0,0,0,0), (0,0,0,1), (0,0,1,0), (0,0,1,1), (0,0,1,2), (0,1,0,0),
    (0,1,0,1), (0,1,0,2), (0,1,1,0), (0,1,1,1), (0,1,1,2), (0,1,2,0),
    (0,1,2,1), (0,1,2,2)]
def relabel (e : Equiv.Perm (Fin 3)) : Col ≃ Col :=
  Equiv.prodCongr e (Equiv.prodCongr e (Equiv.prodCongr e e))
theorem column_relabel (e : Equiv.Perm (Fin 3)) (c : Col) (r : Fin 4) :
    column (relabel e c) r = e (column c r) := by
  fin_cases r <;> rfl
private theorem compatible_relabel (e : Equiv.Perm (Fin 3)) (a b : Col) :
    compatible (relabel e a) (relabel e b) ↔ compatible a b := by
  simp only [compatible, column_relabel, e.injective.ne_iff]
set_option maxRecDepth 100000 in
theorem class_relabel : ∀ e : Equiv.Perm (Fin 3), ∀ c : Col,
    cls (relabel e c) = cls c := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem class_rep : ∀ c : Col, ∃ e : Equiv.Perm (Fin 3),
    relabel e c = representatives (cls c) := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Exhaustively check the fourteen representative rows with the Lean kernel.
private theorem representative_rows : ∀ i s : Fin 14,
    (∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0) =
      Q i s := by
  have h : List.ofFn (fun i : Fin 14 => List.ofFn (fun s : Fin 14 =>
      ∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0)) =
      List.ofFn (fun i : Fin 14 => List.ofFn (fun s : Fin 14 => Q i s)) := by
    decide +kernel
  intro i s
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp h) i)) s
private theorem quotient_rows (b : Col) (s : Fin 14) :
    (∑ c : Col, if compatible b c ∧ cls c = s then (1 : ℤ) else 0) = Q (cls b) s := by
  obtain ⟨e, he⟩ := class_rep b
  calc
    _ = ∑ c : Col, if compatible (relabel e b) (relabel e c) ∧
        cls (relabel e c) = s then (1 : ℤ) else 0 := by
      simp only [compatible_relabel, class_relabel]
    _ = ∑ c : Col, if compatible (representatives (cls b)) c ∧
        cls c = s then (1 : ℤ) else 0 := by
      rw [he]
      exact (relabel e).sum_comp (fun c =>
        if compatible (representatives (cls b)) c ∧ cls c = s then (1 : ℤ) else 0)
    _ = _ := representative_rows _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Exhaustively check finite column compatibility with the Lean kernel.
private theorem initial_weights : ∀ s : Fin 14,
    (∑ a : Col, ∑ b : Col,
      if compatible a b ∧ cls b = s then (1 : ℤ) else 0) = weights s := by
  decide +kernel

def gridEquiv (n : ℕ) : (Fin 4 × Fin n → Fin 3) ≃ (Fin n → Col) where
  toFun P j := (P (0,j), P (1,j), P (2,j), P (3,j))
  invFun f p := column (f p.2) p.1
  left_inv P := by funext p; rcases p with ⟨r,j⟩; fin_cases r <;> rfl
  right_inv f := rfl

theorem column_grid (n : ℕ) (P : Fin 4 × Fin n → Fin 3)
    (j : Fin n) (r : Fin 4) : column (gridEquiv n P j) r = P (r,j) := by
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
private theorem grid_good (n : ℕ) (P : Fin 4 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good compatible (fun _ _ _ => True)
      (List.ofFn (gridEquiv n P)) := by
  rw [good_iff, List.isChain_ofFn]
  simp only [Proper, compatible, column_grid]
  constructor
  · intro h j hj
    exact h ⟨j, by omega⟩ hj
  · intro h j hj
    exact h j.val hj

section CountBridge
attribute [local irreducible] compatible cls Q weights

private theorem count_transfer (n : ℕ) :
    (L (n+2) : ℤ) = dotProduct weights ((Q^n).mulVec (1 : Fin 14 → ℤ)) := by
  classical
  let he : {P : Fin 4 × Fin (n+2) → Fin 3 // Proper P} ≃
      {f : Fin (n+2) → Col //
        TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} :=
    Equiv.subtypeEquiv (gridEquiv (n+2)) (fun P => grid_good (n+2) P)
  have hc : L (n+2) = Nat.card {f : Fin (n+2) → Col //
      TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} := by
    rw [← Nat.card_congr he]
    simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  refine TransferMatrix.cardMatrix compatible (fun _ _ _ => True) (fun _ b => cls b)
    Q weights ?_ ?_ n
  · intro a b _ s
    rw [← quotient_rows b s]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : compatible b c <;> by_cases hs : cls c = s <;> simp [h, hs]
  · intro s
    rw [← initial_weights s]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : compatible a b ∧ cls b = s <;> simp [h]

end CountBridge

private def W : Fin 8 → Fin 14 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![16, 4, 2, 4, 0, 2, 1, 0, 1, 4, 1, 0, 0, 0],
    ![68, 26, 20, 25, 0, 20, 16, 0, 16, 26, 4, 0, 0, 0],
    ![434, 139, 94, 124, 0, 94, 68, 0, 68, 139, 25, 0, 0, 0],
    ![2320, 791, 573, 737, 0, 573, 434, 0, 434, 791, 124, 0, 0, 0],
    ![13306, 4421, 3111, 4026, 0, 3111, 2320, 0, 2320, 4421, 737, 0, 0, 0],
    ![74072, 24864, 17727, 22885, 0, 17727, 13306, 0, 13306, 24864, 4026, 0, 0, 0],
    ![417502, 139548, 98936, 127826, 0, 98936, 74072, 0, 74072, 139548, 22885, 0, 0, 0]]

private def coefficients : Fin 6 → ℤ := ![4, 2, -25, -3, 16, 3]
private theorem table_zero : W 0 = (1 : Fin 14 → ℤ) := by
  exact List.ofFn_inj.mp rfl
private theorem table_steps : ∀ k : Fin 7, W k.succ = Q.mulVec (W k.castSucc) := by
  intro k
  fin_cases k <;> exact List.ofFn_inj.mp rfl
private theorem powers_table : ∀ k : Fin 8,
    (Q^k.val).mulVec (1 : Fin 14 → ℤ) = W k :=
  TransferMatrix.tabulatedPowers Q 7 W table_zero table_steps
private theorem power_polynomial : (Q^(1+6)).mulVec (1 : Fin 14 → ℤ) =
    ∑ j : Fin 6, coefficients j • (Q^(1+j.val)).mulVec (1 : Fin 14 → ℤ) := by
  rw [show 1+6 = (7 : Fin 8).val from rfl, powers_table]
  have hh (j : Fin 6) : (Q^(1+j.val)).mulVec (1 : Fin 14 → ℤ) =
      W ⟨1+j.val, by omega⟩ := powers_table ⟨1+j.val, by omega⟩
  simp_rw [hh]
  exact List.ofFn_inj.mp rfl

theorem initial_values : ∀ k : Fin 8, (L (k.val+2) : ℤ) =
    ![162, 1122, 5808, 33702, 186720, 1054446, 5907444, 33206862] k := by
  intro k
  rw [count_transfer, powers_table]
  fin_cases k <;> rfl

private theorem sextic (n : ℕ) : (L (n+9) : ℤ) =
    3 * (L (n+8) : ℤ) + 16 * (L (n+7) : ℤ) - 3 * (L (n+6) : ℤ) -
      25 * (L (n+5) : ℤ) + 2 * (L (n+4) : ℤ) + 4 * (L (n+3) : ℤ) := by
  have h := TransferMatrix.scalarRelationShift Q weights 6 1 coefficients power_polynomial n
  have ht (k : ℕ) : dotProduct weights ((Q^(k+1)).mulVec (1 : Fin 14 → ℤ)) =
      (L (k+3) : ℤ) := (count_transfer (k+1)).symm
  have hh (j : Fin 6) : n+1+j.val = (n+j.val)+1 := by omega
  simp_rw [hh] at h
  rw [show n+1+6 = (n+6)+1 from by omega] at h
  simp_rw [ht] at h
  norm_num [coefficients, Fin.sum_univ_succ, Nat.add_assoc] at h
  linear_combination h

theorem recurrence (n : ℕ) : (L (n+10) : ℤ) + 6 =
    4 * ((L (n+9) : ℤ) + 6) + 13 * ((L (n+8) : ℤ) + 6) -
      19 * ((L (n+7) : ℤ) + 6) - 22 * ((L (n+6) : ℤ) + 6) +
      27 * ((L (n+5) : ℤ) + 6) + 2 * ((L (n+4) : ℤ) + 6) -
      4 * ((L (n+3) : ℤ) + 6) := by
  have h1 := sextic (n+1)
  have h0 := sextic n
  simp only [Nat.add_assoc] at h1
  linear_combination h1 - h0

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
