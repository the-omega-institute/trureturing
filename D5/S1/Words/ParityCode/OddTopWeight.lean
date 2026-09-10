/- GID: D5/S1/Words/ParityCode/OddTopWeight
   generality: G
   mirror-B: D5/B/S1/Words/ParityCode/OddTopWeight
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Odd square binary matrices of top even row and column weight are counted by factorial. -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace D5.S1.Words.ParityCode.OddTopWeight

open scoped BigOperators

/-- The number of ones in a binary row. -/
def ones {n : ℕ} (r : Fin n → Bool) : ℕ :=
  ∑ j, if r j then 1 else 0

/-- Every row and every column has an even number of ones. -/
def EvenRowsCols {n : ℕ} (M : Fin n → Fin n → Bool) : Prop :=
  (∀ i, Even (ones (M i))) ∧ (∀ j, Even (ones (fun i => M i j)))

/-- The total number of ones, summed over all matrix entries. -/
def weight {n : ℕ} (M : Fin n → Fin n → Bool) : ℕ :=
  ∑ i, ones (M i)

private theorem ones_add_zeros {n : ℕ} (r : Fin n → Bool) :
    ones r + (Finset.univ.filter fun j => r j = false).card = n := by
  classical
  have hz : (∑ j : Fin n, if r j = false then 1 else 0 : ℕ) =
      (Finset.univ.filter fun j => r j = false).card := by
    simp
  rw [ones, ← hz, ← Finset.sum_add_distrib]
  have h (j : Fin n) : (if r j then 1 else 0) + (if r j = false then 1 else 0) = 1 := by
    cases r j <;> rfl
  simp_rw [h]
  simp

private theorem row_bound {n : ℕ} (hn : Odd n) (r : Fin n → Bool)
    (hr : Even (ones r)) : ones r ≤ n - 1 := by
  have h := ones_add_zeros r
  have hne : ones r ≠ n := fun heq => (Nat.not_even_iff_odd.mpr hn) (heq ▸ hr)
  omega

private theorem rows_saturated {n : ℕ} (hn : Odd n) (M : Fin n → Fin n → Bool)
    (hr : ∀ i, Even (ones (M i))) (hw : weight M = n * (n - 1)) :
    ∀ i, ones (M i) = n - 1 := by
  have hs : (∑ i, ones (M i)) = ∑ _ : Fin n, (n - 1) := by simpa [weight] using hw
  exact fun i => (Finset.sum_eq_sum_iff_of_le (fun j _ => row_bound hn (M j) (hr j))).mp
    hs i (Finset.mem_univ i)

private theorem row_unique_zero {n : ℕ} (hn : Odd n) (M : Fin n → Fin n → Bool)
    (hr : ∀ i, Even (ones (M i))) (hw : weight M = n * (n - 1)) (i : Fin n) :
    ∃! j, M i j = false := by
  have hc := ones_add_zeros (M i)
  rw [rows_saturated hn M hr hw i] at hc
  have hnpos : 0 < n := hn.pos
  have hz : (Finset.univ.filter fun j => M i j = false).card = 1 := by omega
  simpa using Finset.card_eq_one_iff_existsUnique.mp hz

private theorem weight_transpose {n : ℕ} (M : Fin n → Fin n → Bool) :
    weight (fun i j => M j i) = weight M := by
  exact Finset.sum_comm

private theorem col_unique_zero {n : ℕ} (hn : Odd n) (M : Fin n → Fin n → Bool)
    (hc : ∀ j, Even (ones (fun i => M i j))) (hw : weight M = n * (n - 1))
    (j : Fin n) : ∃! i, M i j = false :=
  row_unique_zero hn (fun i j => M j i) hc ((weight_transpose M).trans hw) j

private noncomputable def zeroPerm {n : ℕ} (hn : Odd n)
    (M : Fin n → Fin n → Bool) (hM : EvenRowsCols M ∧ weight M = n * (n - 1)) :
    Equiv.Perm (Fin n) := by
  let f : Fin n → Fin n := fun i => (row_unique_zero hn M hM.1.1 hM.2 i).exists.choose
  have hf (i : Fin n) : M i (f i) = false :=
    (row_unique_zero hn M hM.1.1 hM.2 i).exists.choose_spec
  have hi : Function.Injective f := by
    intro i j hij
    exact (col_unique_zero hn M hM.1.2 hM.2 (f i)).unique (hf i) (hij ▸ hf j)
  exact Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩

private theorem zeroPerm_spec {n : ℕ} (hn : Odd n)
    (M : Fin n → Fin n → Bool) (hM : EvenRowsCols M ∧ weight M = n * (n - 1))
    (i j : Fin n) : M i j = false ↔ zeroPerm hn M hM i = j := by
  have hf : M i (zeroPerm hn M hM i) = false :=
    (row_unique_zero hn M hM.1.1 hM.2 i).exists.choose_spec
  exact ⟨fun hj => (row_unique_zero hn M hM.1.1 hM.2 i).unique hf hj,
    fun hij => hij ▸ hf⟩

private def permComplement {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Bool :=
  fun i j => decide (σ i ≠ j)

private theorem permComplement_rows {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ones (permComplement σ i) = n - 1 := by
  have h := ones_add_zeros (permComplement σ i)
  have hz : (Finset.univ.filter fun j => permComplement σ i j = false) = {σ i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, permComplement,
      decide_eq_false_iff_not, not_not, Finset.mem_singleton]
    exact eq_comm
  rw [hz, Finset.card_singleton] at h
  omega

private theorem permComplement_cols {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    ones (fun i => permComplement σ i j) = n - 1 := by
  have h := ones_add_zeros (fun i => permComplement σ i j)
  have hz : (Finset.univ.filter fun i => permComplement σ i j = false) = {σ.symm j} := by
    ext i
    simp [permComplement, ← σ.eq_symm_apply]
  rw [hz, Finset.card_singleton] at h
  omega

private theorem permComplement_valid {n : ℕ} (hn : Odd n) (σ : Equiv.Perm (Fin n)) :
    EvenRowsCols (permComplement σ) ∧ weight (permComplement σ) = n * (n - 1) := by
  have he : Even (n - 1) := by
    rw [Nat.even_iff]
    have ho := Nat.odd_iff.mp hn
    omega
  refine ⟨⟨fun i => (permComplement_rows σ i).symm ▸ he,
    fun j => (permComplement_cols σ j).symm ▸ he⟩, ?_⟩
  simp [weight, permComplement_rows]

private noncomputable def topWeightEquiv (n : ℕ) (hn : Odd n) :
    {M : Fin n → Fin n → Bool // EvenRowsCols M ∧ weight M = n * (n - 1)} ≃
      Equiv.Perm (Fin n) where
  toFun M := zeroPerm hn M.val M.prop
  invFun σ := ⟨permComplement σ, permComplement_valid hn σ⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    have h := zeroPerm_spec hn M.val M.prop i j
    cases hm : M.val i j <;> simp_all [permComplement]
  right_inv σ := by
    apply Equiv.ext
    intro i
    apply (zeroPerm_spec hn (permComplement σ) (permComplement_valid hn σ) i (σ i)).mp
    simp [permComplement]

/-- Odd square binary matrices of maximum even row and column weight are counted by `n!`. -/
theorem spcp_odd_top_weight (n : ℕ) (hn : Odd n) :
    Nat.card {M : Fin n → Fin n → Bool // EvenRowsCols M ∧ weight M = n * (n - 1)}
      = n.factorial := by
  rw [Nat.card_congr (topWeightEquiv n hn), Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

#print axioms spcp_odd_top_weight

end D5.S1.Words.ParityCode.OddTopWeight
