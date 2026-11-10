/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.finite_certificate
   digest: Five column orbits count three-row horizontal and antidiagonal pair patterns. -/
/-
admission_basis: open-problem-resolution (#28806; Proved)
escape_witness: none
All declarations are bind-only: finite class and orbit decisions, table sums,
product/subtype transports and applications of the existing transfer theorems.
direct_frozen_dependencies: []
reused_unfrozen: TransferMatrix.cardMatrix, TransferMatrix.good_iff_local,
  TransferMatrix.tabulatedPowers, TransferMatrix.scalarRelationShift
Proper: proof_shape=bind-only; consumers=instDecidableProper, L, grid_good
instDecidableProper: proof_shape=bind-only; consumers=L
L: proof_shape=bind-only; consumers=count_transfer, initial_values, recurrence_core, recurrence
Col: proof_shape=bind-only; consumers=column, compatible, instDecidableCompatible, cls, representatives, relabel, column_relabel, compatible_relabel, class_relabel, class_rep, representative_rows, quotient_rows, initial_weights, gridEquiv, count_transfer
column: proof_shape=bind-only; consumers=compatible, column_relabel, gridEquiv, column_grid
compatible: proof_shape=bind-only; consumers=instDecidableCompatible, compatible_relabel, representative_rows, quotient_rows, initial_weights, grid_good, count_transfer
instDecidableCompatible: proof_shape=bind-only; consumers=representative_rows, initial_weights
cls: proof_shape=bind-only; consumers=class_relabel, class_rep, representative_rows, quotient_rows, initial_weights, count_transfer
Q: proof_shape=bind-only; consumers=representative_rows, quotient_rows, count_transfer, table_steps, powers_table, power_polynomial, recurrence_core
weights: proof_shape=bind-only; consumers=initial_weights, count_transfer, initial_values, recurrence_core
representatives: proof_shape=bind-only; consumers=class_rep, representative_rows, quotient_rows
relabel: proof_shape=bind-only; consumers=column_relabel, compatible_relabel, class_relabel, class_rep, quotient_rows
column_relabel: proof_shape=bind-only; consumers=compatible_relabel
compatible_relabel: proof_shape=bind-only; consumers=quotient_rows
class_relabel: proof_shape=bind-only; consumers=quotient_rows
class_rep: proof_shape=bind-only; consumers=quotient_rows
representative_rows: proof_shape=bind-only; consumers=quotient_rows
quotient_rows: proof_shape=bind-only; consumers=count_transfer
initial_weights: proof_shape=bind-only; consumers=count_transfer
gridEquiv: proof_shape=bind-only; consumers=column_grid, grid_good, count_transfer
column_grid: proof_shape=bind-only; consumers=grid_good
grid_good: proof_shape=bind-only; consumers=count_transfer
count_transfer: proof_shape=bind-only; consumers=initial_values, recurrence_core
W: proof_shape=bind-only; consumers=table_zero, table_steps, powers_table, power_polynomial, initial_values
coefficients: proof_shape=bind-only; consumers=power_polynomial, recurrence_core
table_zero: proof_shape=bind-only; consumers=powers_table
table_steps: proof_shape=bind-only; consumers=powers_table
powers_table: proof_shape=bind-only; consumers=power_polynomial, initial_values
power_polynomial: proof_shape=bind-only; consumers=recurrence_core
initial_values: proof_shape=bind-only; consumers=recurrence, HardinA233258Strip.finite_certificate, HardinA233258Strip.initial
recurrence_core: proof_shape=bind-only; consumers=recurrence
recurrence: proof_shape=bind-only; consumers=HardinA233258Strip.recurrence
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic

/-! Relabelling orbits and exact continuation vectors for three-row strips. -/
set_option maxRecDepth 100000
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays

def Proper {n : ℕ} (P : Fin 3 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 3),
    (r = s ∨ r.val = s.val + 1) → P (r, j) ≠ P (s, ⟨j.val + 1, h⟩)
private instance instDecidableProper {n : ℕ} (P : Fin 3 × Fin n → Fin 3) :
    Decidable (Proper P) := inferInstanceAs (Decidable (∀ _ _ _ _, _ → _))
def L (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Fin 3 × Fin n → Fin 3 => Proper P)).card

private abbrev Col := Fin 3 × Fin 3 × Fin 3
private def column (c : Col) : Fin 3 → Fin 3 := ![c.1, c.2.1, c.2.2]
private def compatible (a b : Col) : Prop :=
  ∀ r s : Fin 3, (r = s ∨ r.val = s.val + 1) → column a r ≠ column b s
private instance instDecidableCompatible (a b : Col) : Decidable (compatible a b) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _))
private def cls (c : Col) : Fin 5 :=
  if c.1 = c.2.1 then (if c.1 = c.2.2 then 0 else 1)
  else if c.1 = c.2.2 then 2 else if c.2.1 = c.2.2 then 3 else 4
private def Q : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![2,2,2,2,0], ![1,1,0,1,1], ![1,1,0,0,0], ![1,1,1,1,0], ![0,0,0,1,1]]
private def weights : Fin 5 → ℤ := ![24,24,12,24,12]
private def representatives : Fin 5 → Col :=
  ![(0,0,0), (0,0,1), (0,1,0), (0,1,1), (0,1,2)]
private def relabel (e : Equiv.Perm (Fin 3)) : Col ≃ Col :=
  Equiv.prodCongr e (Equiv.prodCongr e e)
private theorem column_relabel (e : Equiv.Perm (Fin 3)) (c : Col) (r : Fin 3) :
    column (relabel e c) r = e (column c r) := by
  fin_cases r <;> rfl
private theorem compatible_relabel (e : Equiv.Perm (Fin 3)) (a b : Col) :
    compatible (relabel e a) (relabel e b) ↔ compatible a b := by
  simp only [compatible, column_relabel, e.injective.ne_iff]
set_option maxRecDepth 100000 in
private theorem class_relabel : ∀ e : Equiv.Perm (Fin 3), ∀ c : Col,
    cls (relabel e c) = cls c := by decide +kernel
set_option maxRecDepth 100000 in
private theorem class_rep : ∀ c : Col, ∃ e : Equiv.Perm (Fin 3),
    relabel e c = representatives (cls c) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Count all 27 successors of each of the five orbit representatives.
private theorem representative_rows : ∀ i s : Fin 5,
    (∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0) =
      Q i s := by
  have h : List.ofFn (fun i : Fin 5 => List.ofFn (fun s : Fin 5 =>
      ∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0)) =
      List.ofFn (fun i : Fin 5 => List.ofFn (fun s : Fin 5 => Q i s)) := by
    decide +kernel
  intro i s
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp h) i)) s
private theorem quotient_rows (b : Col) (s : Fin 5) :
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
-- Count the 729 ordered pairs of columns by their final orbit.
private theorem initial_weights : ∀ s : Fin 5,
    (∑ a : Col, ∑ b : Col,
      if compatible a b ∧ cls b = s then (1 : ℤ) else 0) = weights s := by
  decide +kernel

private def gridEquiv (n : ℕ) : (Fin 3 × Fin n → Fin 3) ≃ (Fin n → Col) where
  toFun P j := (P (0,j), P (1,j), P (2,j))
  invFun f p := column (f p.2) p.1
  left_inv P := by funext p; rcases p with ⟨r,j⟩; fin_cases r <;> rfl
  right_inv f := rfl
private theorem column_grid (n : ℕ) (P : Fin 3 × Fin n → Fin 3)
    (j : Fin n) (r : Fin 3) : column (gridEquiv n P j) r = P (r,j) := by
  fin_cases r <;> rfl
private theorem grid_good (n : ℕ) (P : Fin 3 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good compatible (fun _ _ _ => True)
      (List.ofFn (gridEquiv n P)) := by
  rw [TransferMatrix.good_iff_local]
  simp only [List.length_ofFn, implies_true, and_true]
  constructor
  · intro h j hj
    have hj0 : j < n := by omega
    simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj0, hj,
      compatible, column_grid]
      using h ⟨j, hj0⟩ hj
  · intro h j hj
    have hh := h j.val hj
    simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, hj,
      compatible, column_grid]
      using hh

section CountBridge
attribute [local irreducible] compatible cls Q weights
private theorem count_transfer (n : ℕ) :
    (L (n+2) : ℤ) = dotProduct weights ((Q^n).mulVec (1 : Fin 5 → ℤ)) := by
  classical
  let he : {P : Fin 3 × Fin (n+2) → Fin 3 // Proper P} ≃
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

attribute [local irreducible] L
private def W : Fin 6 → Fin 5 → ℤ :=
  ![![1,1,1,1,1], ![8,4,2,4,2], ![36,18,12,18,6],
    ![168,78,54,84,24], ![768,354,246,384,108], ![3504,1614,1122,1752,492]]
private def coefficients : Fin 3 → ℤ := ![2,-7,6]
private theorem table_zero : W 0 = (1 : Fin 5 → ℤ) := by decide +kernel
set_option maxRecDepth 100000 in
private theorem table_steps : ∀ k : Fin 5, W k.succ = Q.mulVec (W k.castSucc) := by
  decide +kernel
private theorem powers_table (k : Fin 6) : (Q^k.val).mulVec (1 : Fin 5 → ℤ) = W k :=
  TransferMatrix.tabulatedPowers Q 5 W table_zero table_steps k
private theorem power_polynomial :
    (Q^(2+3)).mulVec (1 : Fin 5 → ℤ) =
      ∑ j : Fin 3, coefficients j • (Q^(2+j.val)).mulVec (1 : Fin 5 → ℤ) := by
  have h : W 5 = ∑ j : Fin 3, coefficients j • W ⟨2+j.val, by omega⟩ := by
    decide +kernel
  rw [powers_table ⟨5, by decide⟩]
  have hh (j : Fin 3) : (Q^(2+j.val)).mulVec (1 : Fin 5 → ℤ) =
      W ⟨2+j.val, by omega⟩ := powers_table ⟨2+j.val, by omega⟩
  simp_rw [hh]
  exact h

theorem initial_values (k : Fin 6) :
    (L (k.val+2) : ℤ) = ![96,432,1944,8856,40392,184248] k := by
  rw [count_transfer, powers_table]
  fin_cases k <;> norm_num [weights, W, dotProduct, Fin.sum_univ_succ]

private theorem recurrence_core (n : ℕ) :
    (L (n+7) : ℤ) = 6 * (L (n+6) : ℤ) - 7 * (L (n+5) : ℤ) + 2 * (L (n+4) : ℤ) := by
  have h := TransferMatrix.scalarRelationShift Q weights 3 2 coefficients power_polynomial n
  simp only [coefficients, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ] at h
  simp only [← count_transfer] at h
  norm_num [Nat.add_assoc] at h
  linarith

theorem recurrence (n : ℕ) :
    (L (n+6) : ℤ) + 6 =
      6 * ((L (n+5) : ℤ) + 6) - 7 * ((L (n+4) : ℤ) + 6) +
        2 * ((L (n+3) : ℤ) + 6) := by
  cases n with
  | zero =>
    have h0 := initial_values 1
    have h1 := initial_values 2
    have h2 := initial_values 3
    have h3 := initial_values 4
    norm_num at h0 h1 h2 h3 ⊢
    omega
  | succ n =>
    have h := recurrence_core n
    simp only [Nat.add_assoc] at h ⊢
    linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
