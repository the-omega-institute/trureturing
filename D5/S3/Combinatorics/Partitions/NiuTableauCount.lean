/- GID: D5/S3/Combinatorics/Partitions/NiuTableauCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/NiuTableauCount
   mirror-E: none(waiver:finite-tableau-count-algebra)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: The shifted Vandermonde formula satisfies the one-cell deletion recurrence. -/

module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring

/-! The shifted Vandermonde formula for straight shapes, including zero-length rows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open scoped BigOperators
open Polynomial

namespace D5.S3.Combinatorics.Partitions.NiuTableauCount

/-- Coefficients of the shift by `-1` from the Hasse derivative at `-1`. -/
private theorem coeff_shift (p : ℚ[X]) (n r : ℕ) (h : p.natDegree ≤ n + r) :
    (taylor (-1) p).coeff n =
      ∑ j ∈ Finset.range (r + 1),
        ((j + n).choose n : ℚ) * p.coeff (j + n) * (-1 : ℚ) ^ j := by
  rw [taylor_coeff]
  have hdegree : (hasseDeriv n p).natDegree ≤ r := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [hasseDeriv_coeff, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j + n),
      mul_zero]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdegree)]
  simp only [hasseDeriv_coeff]

/-- The weighted shifted-Vandermonde identity for distinct rational nodes. -/
private theorem weighted_shifted_vandermonde {k : ℕ} (hk : 2 ≤ k) (b : Fin k → ℚ)
    (hb : Function.Injective b) :
    (∑ i : Fin k, b i * ∏ j ∈ (Finset.univ.erase i), (b i - 1 - b j) / (b i - b j)) =
      (∑ i : Fin k, b i) - (k.choose 2 : ℚ) := by
  let s : Finset (Fin k) := Finset.univ
  have hs : s.card = k := by simp [s]
  let P := Lagrange.nodal s b
  -- These two nodal products have roots `b j` and `b j + 1`, respectively.
  let Q := taylor (-1) P
  let G := X * (P - Q) - C (k : ℚ) * P
  have hPdeg : P.natDegree = k := (Lagrange.natDegree_nodal).trans hs
  have hQdeg : Q.natDegree = k := by simpa [Q] using hPdeg
  have hPtop : P.coeff k = 1 := by
    rw [← hPdeg]
    exact Lagrange.nodal_monic
  have hQtop : Q.coeff k = 1 := by
    change (taylor (-1) P).coeff k = 1
    rw [← hPdeg, coeff_taylor_natDegree]
    exact Lagrange.nodal_monic
  have hPnext : P.coeff (k - 1) = -∑ i ∈ s, b i := by
    simpa only [P, Lagrange.nodal_eq, hs] using
      prod_X_sub_C_coeff_card_pred s b (by omega)
  have hsucc : k - 1 + 1 = k := by omega
  have hsucc₂ : k - 2 + 1 = k - 1 := by omega
  have htwo : k - 2 + 2 = k := by omega
  have hchooseOne : k.choose (k - 1) = k := by
    rw [Nat.choose_symm (by omega : 1 ≤ k), Nat.choose_one_right]
  have hchooseTwo : k.choose (k - 2) = k.choose 2 := Nat.choose_symm hk
  have hQnext : Q.coeff (k - 1) = P.coeff (k - 1) - (k : ℚ) := by
    dsimp only [Q]
    rw [coeff_shift P (k - 1) 1 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, Nat.add_comm 1 (k - 1), hsucc, Nat.choose_self,
      hchooseOne, Nat.cast_one, one_mul, mul_one, hPtop]
    ring
  have hQthird : Q.coeff (k - 2) =
      P.coeff (k - 2) - ((k - 1 : ℕ) : ℚ) * P.coeff (k - 1) + (k.choose 2 : ℚ) := by
    have hchooseNext : (k - 1).choose (k - 2) = k - 1 := by
      simpa only [hsucc₂] using Nat.choose_succ_self_right (k - 2)
    dsimp only [Q]
    rw [coeff_shift P (k - 2) 2 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, Nat.add_comm 1 (k - 2), Nat.add_comm 2 (k - 2),
      hsucc₂, htwo, Nat.choose_self, hchooseNext, hchooseTwo, Nat.cast_one, one_mul,
      mul_one, hPtop]
    ring
  have hGcoeff (n : ℕ) : G.coeff (n + 1) =
      P.coeff n - Q.coeff n - (k : ℚ) * P.coeff (n + 1) := by
    simp only [G, coeff_sub, coeff_X_mul, coeff_C_mul]
  -- The coefficient in degree `k` cancels, and all higher ones vanish.
  have hGdeg : G.degree < (s.card : WithBot ℕ) := by
    rw [hs, degree_lt_iff_coeff_zero]
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hGcoeff]
    by_cases hn : n + 1 = k
    · have h : n = k - 1 := by omega
      rw [hn, h, hQnext, hPtop]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 1), mul_zero, sub_zero]
      by_cases hn' : n = k
      · rw [hn', hPtop, hQtop, sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n),
            coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n), sub_self]
  have hGnext : G.coeff (s.card - 1) = (∑ i ∈ s, b i) - (k.choose 2 : ℚ) := by
    rw [hs, ← hsucc₂, hGcoeff, hQthird, hsucc₂, hPnext, Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_one]
    ring
  -- At node `b i` the factor indexed by `i` in `Q` is `-1`.
  have heval (i : Fin k) (hi : i ∈ s) :
      G.eval (b i) = b i * ∏ j ∈ s.erase i, (b i - 1 - b j) := by
    have hPi : P.eval (b i) = 0 := Lagrange.eval_nodal_at_node hi
    have hQi : Q.eval (b i) = ∏ j ∈ s, (b i - 1 - b j) := by
      dsimp only [Q]
      rw [taylor_apply, eval_comp, eval_add, eval_X, eval_C, ← sub_eq_add_neg]
      exact Lagrange.eval_nodal
    have hsplit :
        (∏ j ∈ s, (b i - 1 - b j)) = (∏ j ∈ s.erase i, (b i - 1 - b j)) * (-1) := by
      rw [← Finset.prod_erase_mul s (fun j => b i - 1 - b j) hi]
      congr 1
      ring
    simp only [G, eval_sub, eval_mul, eval_X, eval_C, hPi, hQi, hsplit]
    ring
  have hinterp := Lagrange.coeff_eq_sum hb.injOn hGdeg
  rw [hGnext] at hinterp
  change (∑ i ∈ s, b i * ∏ j ∈ s.erase i, (b i - 1 - b j) / (b i - b j)) = _
  calc
    _ = ∑ i ∈ s, G.eval (b i) / ∏ j ∈ s.erase i, (b i - b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [heval i hi, Finset.prod_div_distrib, mul_div_assoc]
    _ = _ := hinterp.symm

/-- Delete the rightmost cell of row `i`, preserving the number of row slots. -/
def deleteRow {k : ℕ} (rows : Fin k → ℕ) (i : Fin k) : Fin k → ℕ :=
  Function.update rows i (rows i - 1)

/-- A positive row is removable if all rows below it are strictly shorter. -/
def RemovableRow {k : ℕ} (rows : Fin k → ℕ) (i : Fin k) : Prop :=
  0 < rows i ∧ ∀ j, i < j → rows j < rows i

/-- Add the number of row slots below the selected row to its length. -/
def shiftedNode {k : ℕ} (rows : Fin k → ℕ) (i : Fin k) : ℕ :=
  rows i + (Fin.rev i).val

private theorem shiftedNode_strictAnti {k : ℕ} {rows : Fin k → ℕ} (hrows : Antitone rows) :
    StrictAnti (shiftedNode rows) := by
  intro i j hij
  have hle := hrows hij.le
  have hrev : (Fin.rev j).val < (Fin.rev i).val := by
    simp only [Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    omega
  exact Nat.add_lt_add_of_le_of_lt hle hrev

/-- The ordered pair product of differences of the row nodes. -/
def vandermonde {k : ℕ} (b : Fin k → ℚ) : ℚ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (b i - b j)

/-- The rational count formula for weakly decreasing row lengths with zero padding. -/
def shiftedCount {k : ℕ} (rows : Fin k → ℕ) : ℚ :=
  (∑ i, rows i).factorial * vandermonde (fun i => (shiftedNode rows i : ℚ)) /
    ∏ i, ((shiftedNode rows i).factorial : ℚ)

private theorem vandermonde_update {k : ℕ} {b : Fin k → ℚ}
    (hb : Function.Injective b) (i : Fin k) (x : ℚ) :
    vandermonde (Function.update b i x) =
      vandermonde b * ∏ j ∈ Finset.univ.erase i, (x - b j) / (b i - b j) := by
  let r := fun j => (x - b j) / (b i - b j)
  have hfactor (a j : Fin k) (haj : j ∈ Finset.Ioi a) :
      Function.update b i x a - Function.update b i x j =
        (b a - b j) * ((if a = i then r j else 1) * (if j = i then r a else 1)) := by
    have haj' : a < j := Finset.mem_Ioi.mp haj
    by_cases ha : a = i
    · subst a
      have hj := haj'.ne.symm
      have hd : b i - b j ≠ 0 := sub_ne_zero.mpr (hb.ne haj'.ne)
      rw [Function.update_self, Function.update_of_ne hj, ite_eq_left rfl, ite_eq_right hj,
        mul_one]
      exact (mul_div_cancel₀ (x - b j) hd).symm
    · by_cases hj : j = i
      · subst j
        have hd : b i - b a ≠ 0 := sub_ne_zero.mpr (hb.ne (Ne.symm ha))
        simp [ha, r]
        field_simp
        ring
      · simp [ha, hj]
  have hsplit : Finset.Ioi i ∪ Finset.Iio i = Finset.univ.erase i := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Ioi, Finset.mem_Iio, Finset.mem_erase,
      Finset.mem_univ, and_true]
    exact (ne_comm.trans ne_iff_lt_or_gt).symm
  have hdisjoint : Disjoint (Finset.Ioi i) (Finset.Iio i) :=
    Finset.disjoint_left.mpr fun _ hj hj' =>
      (Finset.mem_Ioi.mp hj).not_gt (Finset.mem_Iio.mp hj')
  calc
    _ = ∏ a : Fin k, ∏ j ∈ Finset.Ioi a,
        (b a - b j) * ((if a = i then r j else 1) * (if j = i then r a else 1)) := by
      exact Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl (hfactor a)
    _ = vandermonde b * ((∏ j ∈ Finset.Ioi i, r j) * ∏ j ∈ Finset.Iio i, r j) := by
      simp only [vandermonde, Finset.prod_mul_distrib, Finset.prod_ite_irrel, Finset.prod_const_one]
      rw [Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ i)]
      congr 1
      congr 1
      have hfilter : Finset.Iio i = Finset.univ.filter (fun a => a < i) := by
        ext a
        simp
      rw [hfilter, Finset.prod_filter]
      simp only [Finset.prod_ite_eq', Finset.mem_Ioi]
    _ = _ := by rw [← Finset.prod_union hdisjoint, hsplit]

private theorem sum_shiftedNode {k : ℕ} (rows : Fin k → ℕ) :
    (∑ i, shiftedNode rows i) = (∑ i, rows i) + k.choose 2 := by
  simp only [shiftedNode, Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin k, (Fin.rev i).val) = ∑ i : Fin k, i.val :=
      Equiv.sum_comp Fin.revPerm Fin.val
    _ = ∑ n ∈ Finset.range k, n := by
      rw [Finset.sum_fin_eq_sum_range]
      exact Finset.sum_congr rfl fun _ hn => dite_eq_left (Finset.mem_range.mp hn)
    _ = _ := by rw [Finset.sum_range_id, Nat.choose_two_right]

private theorem empty_vandermonde_row {k : ℕ} (i : Fin k) :
    (∏ j ∈ Finset.Ioi i, (((Fin.rev i).val : ℚ) - (Fin.rev j).val)) =
      ((Fin.rev i).val.factorial : ℚ) := by
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
  refine Finset.prod_bij (fun j _ => j.val - i.val - 1) ?_ ?_ ?_ ?_
  · intro j hj
    have hij : i.val < j.val := (Finset.mem_Ioi.mp hj : i < j)
    have hi := i.isLt
    have hj' := j.isLt
    simp only [Finset.mem_range, Fin.val_rev]
    omega
  · intro j hj j' hj' h
    apply Fin.ext
    have hij : i.val < j.val := (Finset.mem_Ioi.mp hj : i < j)
    have hij' : i.val < j'.val := (Finset.mem_Ioi.mp hj' : i < j')
    omega
  · intro n hn
    simp only [Finset.mem_range, Fin.val_rev] at hn
    refine ⟨⟨i.val + n + 1, by omega⟩, Finset.mem_Ioi.mpr ?_, ?_⟩
    · change i.val < i.val + n + 1
      omega
    · change i.val + n + 1 - i.val - 1 = n
      omega
  · intro j hj
    have hij : i.val < j.val := (Finset.mem_Ioi.mp hj : i < j)
    have hi := i.isLt
    have hj' := j.isLt
    have h : (Fin.rev i).val = (Fin.rev j).val + (j.val - i.val - 1 + 1) := by
      simp only [Fin.val_rev]
      omega
    rw [h, Nat.cast_add, add_sub_cancel_left]

/-- The empty diagram has rational count one for every ambient row count. -/
theorem shiftedCount_empty (k : ℕ) : shiftedCount (fun _ : Fin k => 0) = 1 := by
  simp only [shiftedCount, shiftedNode, zero_add, Finset.sum_const_zero, Nat.factorial_zero,
    Nat.cast_one, one_mul, vandermonde]
  rw [Finset.prod_congr rfl (fun i _ => empty_vandermonde_row i), div_self]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast Nat.factorial_ne_zero _

private def deletionWeight {k : ℕ} (b : Fin k → ℚ) (i : Fin k) : ℚ :=
  b i * ∏ j ∈ Finset.univ.erase i, (b i - 1 - b j) / (b i - b j)

private theorem deletionWeight_eq_zero {k : ℕ} {rows : Fin k → ℕ}
    (hrows : Antitone rows) {i : Fin k} (hi : ¬ RemovableRow rows i) :
    deletionWeight (fun j => (shiftedNode rows j : ℚ)) i = 0 := by
  by_cases hzero : shiftedNode rows i = 0
  · simp [deletionWeight, hzero]
  have hex : ∃ j : Fin k, i < j ∧ rows j = rows i := by
    by_contra! h
    apply hi
    refine ⟨?_, fun j hij => lt_of_le_of_ne (hrows hij.le) (h j hij)⟩
    by_contra! hrow
    have hrev : 0 < (Fin.rev i).val := by
      simp only [shiftedNode] at hzero
      omega
    have hs : i.val + 1 < k := by
      simp only [Fin.val_rev] at hrev
      omega
    let j : Fin k := ⟨i.val + 1, hs⟩
    have hij : i < j := by change i.val < i.val + 1; omega
    have hle := hrows hij.le
    exact h j hij (by omega)
  obtain ⟨j, hij, heq⟩ := hex
  let next : Fin k := ⟨i.val + 1, lt_of_le_of_lt hij j.isLt⟩
  have hin : i < next := Nat.lt_succ_self _
  have hnj : next ≤ j := hij
  have hy : rows next = rows i := le_antisymm (hrows hin.le) (heq ▸ hrows hnj)
  have hnode : shiftedNode rows i = shiftedNode rows next + 1 := by
    simp only [shiftedNode, hy, Fin.val_rev, next]
    have hn := j.isLt
    have hij' : i.val < j.val := hij
    omega
  have hz : (shiftedNode rows i : ℚ) - 1 - (shiftedNode rows next : ℚ) = 0 := by
    rw [hnode, Nat.cast_add, Nat.cast_one]
    ring
  unfold deletionWeight
  rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hin.ne.symm, Finset.mem_univ next⟩)
    (by rw [hz, zero_div]), mul_zero]

private theorem shiftedCount_deleteRow {k : ℕ} {rows : Fin k → ℕ}
    (hrows : Antitone rows) {i : Fin k} (hi : RemovableRow rows i) :
    shiftedCount (deleteRow rows i) =
      ((∑ j, rows j).pred.factorial : ℚ) *
        vandermonde (fun j => (shiftedNode rows j : ℚ)) /
        (∏ j, ((shiftedNode rows j).factorial : ℚ)) *
        deletionWeight (fun j => (shiftedNode rows j : ℚ)) i := by
  let n := ∑ j, rows j
  let b := fun j => (shiftedNode rows j : ℚ)
  have hnode (j : Fin k) :
      shiftedNode (deleteRow rows i) j =
        Function.update (shiftedNode rows) i (shiftedNode rows i - 1) j := by
    by_cases hj : j = i
    · subst j
      simp only [shiftedNode, deleteRow, Function.update_self]
      have := hi.1
      omega
    · simp [shiftedNode, deleteRow, Function.update_of_ne hj]
  have hpos : 0 < shiftedNode rows i := by
    simp only [shiftedNode]
    have := hi.1
    omega
  have hbupdate : (fun j => (shiftedNode (deleteRow rows i) j : ℚ)) =
      Function.update b i (b i - 1) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [hnode, Function.update_self, b, Nat.cast_sub hpos, Nat.cast_one]
    · simp [hnode, b, Function.update_of_ne hj]
  have hn : (∑ j, deleteRow rows i j) = n.pred := by
    rw [deleteRow, Finset.sum_update_of_mem (Finset.mem_univ i)]
    have he := Finset.sum_erase_add Finset.univ rows (Finset.mem_univ i)
    have := hi.1
    change _ = (∑ j, rows j).pred
    rw [Nat.pred_eq_sub_one, Finset.sdiff_singleton_eq_erase]
    omega
  have hdenom : (∏ j, ((shiftedNode rows (j : Fin k)).factorial : ℚ)) =
      b i * ∏ j, ((shiftedNode (deleteRow rows i) j).factorial : ℚ) := by
    rw [← Finset.prod_erase_mul Finset.univ (fun j => ((shiftedNode rows j).factorial : ℚ))
      (Finset.mem_univ i), ← Finset.prod_erase_mul Finset.univ
      (fun j => ((shiftedNode (deleteRow rows i) j).factorial : ℚ)) (Finset.mem_univ i)]
    simp only [hnode, Function.update_self]
    have htail : (∏ j ∈ Finset.univ.erase i,
        (↑(Function.update (shiftedNode rows) i (shiftedNode rows i - 1) j).factorial : ℚ)) =
        ∏ j ∈ Finset.univ.erase i, ((shiftedNode rows j).factorial : ℚ) :=
      Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [htail, show shiftedNode rows i = (shiftedNode rows i - 1) + 1 by omega,
      Nat.factorial_succ, Nat.cast_mul]
    simp only [b]
    rw [show shiftedNode rows i - 1 + 1 = shiftedNode rows i by omega]
    ring
  have hd : (∏ j, ((shiftedNode (deleteRow rows i) j).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
  have hbi : b i ≠ 0 := by
    change (shiftedNode rows i : ℚ) ≠ 0
    exact_mod_cast hpos.ne'
  have hb : Function.Injective b := fun a j h => (shiftedNode_strictAnti hrows).injective
    (Nat.cast_injective h)
  rw [shiftedCount, hn, hbupdate, vandermonde_update hb, hdenom]
  change _ = (n.pred.factorial : ℚ) * vandermonde b / _ * deletionWeight b i
  unfold deletionWeight
  field_simp [hbi, hd]

instance {k : ℕ} (rows : Fin k → ℕ) (i : Fin k) : Decidable (RemovableRow rows i) := by
  unfold RemovableRow
  infer_instance

/-- The rational count for a nonempty diagram is the sum after each possible one-cell deletion. -/
theorem shiftedCount_recurrence {k : ℕ} (hk : 2 ≤ k) (rows : Fin k → ℕ)
    (hrows : Antitone rows) (hn : 0 < ∑ j, rows j) :
    shiftedCount rows =
      ∑ i ∈ Finset.univ.filter (RemovableRow rows), shiftedCount (deleteRow rows i) := by
  classical
  let b := fun j => (shiftedNode rows j : ℚ)
  let n := ∑ j, rows j
  let factor : ℚ := (n.pred.factorial : ℚ) * vandermonde b /
    (∏ j, ((shiftedNode rows j).factorial : ℚ))
  have hb : Function.Injective b := fun a j h => (shiftedNode_strictAnti hrows).injective
    (Nat.cast_injective h)
  have hw : (∑ i, deletionWeight b i) = (n : ℚ) := by
    simpa only [deletionWeight, b, ← Nat.cast_sum, sum_shiftedNode, Nat.cast_add,
      add_sub_cancel_right, n] using weighted_shifted_vandermonde hk b hb
  have hf : shiftedCount rows = factor * n := by
    have hfac : n.factorial = n * n.pred.factorial := by
      have hnp : n.pred.succ = n := Nat.succ_pred_eq_of_pos hn
      calc
        n.factorial = n.pred.succ.factorial := congrArg Nat.factorial hnp.symm
        _ = n * n.pred.factorial := by rw [Nat.factorial_succ, ← Nat.succ_eq_add_one, hnp]
    dsimp only [shiftedCount, factor]
    change (n.factorial : ℚ) * vandermonde b / _ = _
    rw [hfac, Nat.cast_mul]
    ring
  calc
    shiftedCount rows = factor * ∑ i, deletionWeight b i := hf.trans (by rw [hw])
    _ = ∑ i, factor * deletionWeight b i := Finset.mul_sum ..
    _ = ∑ i ∈ Finset.univ.filter (RemovableRow rows), shiftedCount (deleteRow rows i) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : RemovableRow rows i
      · rw [ite_eq_left hi, shiftedCount_deleteRow hrows hi]
      · rw [ite_eq_right hi, deletionWeight_eq_zero hrows hi, mul_zero]

end D5.S3.Combinatorics.Partitions.NiuTableauCount
