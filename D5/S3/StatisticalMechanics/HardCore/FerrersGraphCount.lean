/- GID: D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/FerrersGraphCount
   mirror-E: none(waiver:symbolic-independent-set-enumeration)
   anchors: []
   utility: none
   digest: Least-row enumeration of the independence polynomial of the actual Ferrers graph. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
import OmegaBuild.Commands

/-!
# The Ferrers independence polynomial

Count independent subsets by the least selected row or by the column-only case.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.FerrersGraphCount

open Finset Polynomial
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open scoped BigOperators

variable {n m : ℕ}

abbrev Vertex (n m : ℕ) := Fin n ⊕ Fin m

/-- The finite Ferrers graph with zero-based row and column indices. -/
def graph (m : ℕ) (rowLength : Fin n → ℕ) : SimpleGraph (Vertex n m) where
  Adj
    | .inl i, .inr j => j.val < rowLength i
    | .inr j, .inl i => j.val < rowLength i
    | _, _ => False
  symm := ⟨by
    intro a b
    cases a <;> cases b <;> exact id⟩
  loopless := ⟨by
    intro a
    cases a <;> exact id⟩

instance (rowLength : Fin n → ℕ) : DecidableRel (graph m rowLength).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [graph] <;> infer_instance

@[simp] private theorem graph_adj_row_col (rowLength : Fin n → ℕ) (i : Fin n) (j : Fin m) :
    (graph m rowLength).Adj (Sum.inl i) (Sum.inr j) ↔ j.val < rowLength i :=
  Iff.rfl

private def rowsFrom (n k : ℕ) : Finset (Fin n) := univ.filter fun i => k ≤ i.val

private def tail (n m k : ℕ) : Finset (Vertex n m) :=
  (rowsFrom n k).disjSum univ

private def freeVertices (m : ℕ) (rowLength : Fin n → ℕ) (i : Fin n) :
    Finset (Vertex n m) :=
  (Ioi i).disjSum (univ.filter fun j : Fin m => rowLength i ≤ j.val)

private theorem tail_zero : tail n m 0 = univ := by
  ext v
  cases v <;> simp [tail, rowsFrom]

private theorem tail_erase (i : Fin n) :
    (tail n m i.val).erase (Sum.inl i) = tail n m (i.val + 1) := by
  ext v
  rw [Finset.mem_erase]
  cases v with
  | inl j =>
    simp only [tail, inl_mem_disjSum, rowsFrom, Finset.mem_filter, mem_univ, true_and]
    rw [Ne, Sum.inl.injEq, Fin.ext_iff]
    omega
  | inr j => simp [tail]

private theorem closedComplement_tail (rowLength : Fin n → ℕ) (i : Fin n) :
    closedComplement (graph m rowLength) (tail n m i.val) (Sum.inl i) =
      freeVertices m rowLength i := by
  unfold closedComplement
  rw [tail_erase]
  ext v
  rw [Finset.mem_filter]
  cases v with
  | inl j =>
    change (Sum.inl j ∈ tail n m (i.val + 1) ∧ ¬False) ↔
      Sum.inl j ∈ freeVertices m rowLength i
    simp only [tail, rowsFrom, inl_mem_disjSum, Finset.mem_filter, mem_univ, true_and,
      not_false_eq_true, and_true, freeVertices, mem_Ioi, Fin.lt_def]
    omega
  | inr j =>
    change (Sum.inr j ∈ tail n m (i.val + 1) ∧ ¬j.val < rowLength i) ↔
      Sum.inr j ∈ freeVertices m rowLength i
    simp [tail, freeVertices, not_lt]

private theorem card_colsFrom (m k : ℕ) :
    (univ.filter fun j : Fin m => k ≤ j.val).card = m - k := by
  by_cases h : k < m
  · have hIci : (univ.filter fun j : Fin m => k ≤ j.val) = Ici (⟨k, h⟩ : Fin m) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_Ici]
      rfl
    rw [hIci, Fin.card_Ici]
  · have hempty : (univ.filter fun j : Fin m => k ≤ j.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hkj := (mem_filter.mp hj).2
      have hjm := j.isLt
      omega
    rw [hempty, card_empty, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]

private theorem card_freeVertices (rowLength : Fin n → ℕ) (i : Fin n) :
    (freeVertices m rowLength i).card = (n - 1 - i.val) + (m - rowLength i) := by
  simp only [freeVertices, card_disjSum, Fin.card_Ioi, card_colsFrom]

private theorem freeVertices_independent (rowLength : Fin n → ℕ)
    (hrow : Antitone rowLength) (i : Fin n) :
    (graph m rowLength).IsIndepSet (freeVertices m rowLength i : Set (Vertex n m)) := by
  intro a ha b hb _
  change a ∈ freeVertices m rowLength i at ha
  change b ∈ freeVertices m rowLength i at hb
  cases a with
  | inl j =>
    cases b with
    | inl k => exact id
    | inr k =>
      have hj : i < j := by simpa [freeVertices] using ha
      have hk : rowLength i ≤ k.val := by simpa [freeVertices] using hb
      exact Nat.not_lt.mpr ((hrow hj.le).trans hk)
  | inr k =>
    cases b with
    | inl j =>
      have hj : i < j := by simpa [freeVertices] using hb
      have hk : rowLength i ≤ k.val := by simpa [freeVertices] using ha
      exact Nat.not_lt.mpr ((hrow hj.le).trans hk)
    | inr l => exact id

private theorem independent_domain_polynomial (rowLength : Fin n → ℕ)
    (V : Finset (Vertex n m)) (hV : (graph m rowLength).IsIndepSet (V : Set (Vertex n m))) :
    independencePolynomial (graph m rowLength) V = (1 + X) ^ V.card := by
  have hconfig : configurations (graph m rowLength) V = V.powerset := by
    ext S
    simp only [configurations, mem_filter, mem_powerset, and_iff_left_iff_imp]
    intro hS
    exact hV.mono hS
  rw [independencePolynomial, partition, hconfig, ← Finset.prod_one_add]
  simp

private theorem rowsFrom_end : rowsFrom n n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact (Nat.not_le_of_lt i.isLt) (mem_filter.mp hi).2

private theorem tail_end_polynomial (rowLength : Fin n → ℕ) :
    independencePolynomial (graph m rowLength) (tail n m n) = (1 + X) ^ m := by
  have hind : (graph m rowLength).IsIndepSet (tail n m n : Set (Vertex n m)) := by
    intro a ha b hb _
    change a ∈ tail n m n at ha
    change b ∈ tail n m n at hb
    cases a with
    | inl i => simp [tail, rowsFrom_end] at ha
    | inr j =>
      cases b with
      | inl i => simp [tail, rowsFrom_end] at hb
      | inr k => exact id
  rw [independent_domain_polynomial rowLength _ hind]
  simp [tail, rowsFrom_end]

private theorem rowsFrom_insert (i : Fin n) :
    rowsFrom n i.val = insert i (rowsFrom n (i.val + 1)) := by
  ext j
  simp only [rowsFrom, mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

/-- Deleting rows in increasing order partitions the independent sets by their least row.
At the step for row `i`, inclusion of that row leaves an edgeless domain of later rows
and columns outside its neighborhood. The final term accounts for column-only sets. -/
private theorem tail_polynomial (rowLength : Fin n → ℕ) (hrow : Antitone rowLength)
    (k : ℕ) (hk : k ≤ n) :
    independencePolynomial (graph m rowLength) (tail n m k) =
      (1 + X) ^ m + X * ∑ i ∈ rowsFrom n k,
        (1 + X) ^ ((n - 1 - i.val) + (m - rowLength i)) := by
  induction hk using Nat.decreasingInduction with
  | of_succ k hk ih =>
    let i : Fin n := ⟨k, hk⟩
    change independencePolynomial (graph m rowLength) (tail n m i.val) = _
    have hi : Sum.inl i ∈ tail n m i.val := by simp [tail, rowsFrom]
    have hdelete := partition_delete (graph m rowLength) (tail n m i.val) (Sum.inl i) hi
      (fun _ => (X : Polynomial ℤ))
    change independencePolynomial (graph m rowLength) (tail n m i.val) =
      independencePolynomial (graph m rowLength) ((tail n m i.val).erase (Sum.inl i)) +
      X * independencePolynomial (graph m rowLength)
        (closedComplement (graph m rowLength) (tail n m i.val) (Sum.inl i)) at hdelete
    have hnot : i ∉ rowsFrom n (i.val + 1) := by simp [rowsFrom]
    change _ = (1 + X) ^ m + X * ∑ j ∈ rowsFrom n i.val,
      (1 + X) ^ ((n - 1 - j.val) + (m - rowLength j))
    rw [hdelete, tail_erase, closedComplement_tail,
      independent_domain_polynomial _ _ (freeVertices_independent rowLength hrow i),
      card_freeVertices, ih, rowsFrom_insert i, sum_insert hnot, mul_add]
    dsimp only [i, Fin.val_mk]
    ring
  | self =>
    simp [tail_end_polynomial, rowsFrom_end]

/-- The column-only term and one contribution for each possible least selected row. -/
theorem independencePolynomial_ferrers (rowLength : Fin n → ℕ) (hrow : Antitone rowLength) :
    independencePolynomial (graph m rowLength) univ =
      (1 + X) ^ m + X * ∑ i : Fin n,
        (1 + X) ^ ((n - 1 - i.val) + (m - rowLength i)) := by
  simpa [tail_zero, rowsFrom] using
    (tail_polynomial (m := m) rowLength hrow 0 (Nat.zero_le n))

/-- The whole-graph polynomial's degree-`k` coefficient counts Mathlib's
size-`k` independent sets. -/
theorem coeff_independencePolynomial_eq_card_indepSetFinset {α : Type*}
    [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) :
    (independencePolynomial G univ).coeff k = (G.indepSetFinset k).card := by
  have hsets :
      (configurations G univ).filter (fun S => k = S.card) = G.indepSetFinset k := by
    ext S
    simp only [configurations, mem_filter, mem_powerset, subset_univ, true_and,
      SimpleGraph.mem_indepSetFinset_iff]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  rw [← hsets]
  simp [independencePolynomial, partition]

@[simp] theorem card_indepSetFinset_ferrers_zero (rowLength : Fin n → ℕ) :
    ((graph m rowLength).indepSetFinset 0).card = 1 := by
  have hzero : (graph m rowLength).indepSetFinset 0 = {∅} := by
    ext S
    simp only [SimpleGraph.mem_indepSetFinset_iff, mem_singleton,
      SimpleGraph.isNIndepSet_iff, Finset.card_eq_zero]
    refine ⟨And.right, ?_⟩
    rintro rfl
    simp [SimpleGraph.IsIndepSet]
  rw [hzero, card_singleton]

/-- The count at size `k + 1` is a binomial count for each least-row case
and a binomial count for column-only subsets. -/
theorem card_indepSetFinset_ferrers_succ (rowLength : Fin n → ℕ)
    (hrow : Antitone rowLength) (k : ℕ) :
    ((graph m rowLength).indepSetFinset (k + 1)).card =
      m.choose (k + 1) + ∑ i : Fin n, ((n - 1 - i.val) + (m - rowLength i)).choose k := by
  have h := coeff_independencePolynomial_eq_card_indepSetFinset (graph m rowLength) (k + 1)
  rw [independencePolynomial_ferrers rowLength hrow, coeff_add, coeff_X_mul,
    finsetSum_coeff] at h
  simp only [coeff_one_add_X_pow] at h
  exact_mod_cast h.symm

end D5.S3.StatisticalMechanics.HardCore.FerrersGraphCount
