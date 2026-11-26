/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnEnergy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Ring.Abs]
   utility: none
   digest: Three integral columns with sparse Gram interactions have unit-vector energy rigidity. -/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! The normalized integer energy test for the three minority columns in the
18+3 fold of Hong–Wu–Xia Problem 2 (arXiv:2610.09483v1, Section 7). -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy

variable {n : ℕ}

/-- Squared energy of the column combination on the retained rows. -/
@[expose] def columnEnergy (rows : Finset (Fin n)) (B : Fin n → Fin 3 → ℤ)
    (a : Fin 3 → ℤ) : ℤ :=
  ∑ r ∈ rows, (∑ j : Fin 3, B r j * a j) ^ 2

private theorem gram_cross_lower (g x y : ℤ) (hg : |g| ≤ 1) :
    -(x ^ 2 + y ^ 2) ≤ 2 * g * (x * y) := by
  have hprod : |g * (x * y)| ≤ |x| * |y| := by
    rw [abs_mul g, abs_mul x y]
    exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg x) (abs_nonneg y)) hg
  have hpair : 2 * (|x| * |y|) ≤ x ^ 2 + y ^ 2 := by
    simpa only [mul_assoc, sq_abs] using two_mul_le_add_sq (|x|) (|y|)
  linarith only [hprod, hpair, neg_abs_le (g * (x * y))]

private theorem one_le_int_sq {x : ℤ} (hx : x ≠ 0) : 1 ≤ x ^ 2 := by
  have h := sq_pos_of_ne_zero hx
  omega

/-- Content. The support-sensitive Gram estimate separates the signed coordinate
vectors from all other nonzero integral combinations at energy four. -/
theorem three_column_energy (rows : Finset (Fin n)) (B : Fin n → Fin 3 → ℤ)
    (hdiag : ∀ j, (∑ r ∈ rows, B r j ^ 2) = 4)
    (hoff : ∀ i j : Fin 3, i < j → |∑ r ∈ rows, B r i * B r j| ≤ 1)
    (a : Fin 3 → ℤ) (ha : a ≠ 0) :
    let energy := columnEnergy rows B a
    4 ≤ energy ∧
      (energy = 4 ↔
        ∃ i, (a i = 1 ∨ a i = -1) ∧ ∀ j, j ≠ i → a j = 0) ∧
      ((∃ i j, i ≠ j ∧ a i ≠ 0 ∧ a j ≠ 0) → 6 ≤ energy) := by
  dsimp only
  have hexpand : columnEnergy rows B a =
      (∑ r ∈ rows, B r 0 ^ 2) * a 0 ^ 2 +
      (∑ r ∈ rows, B r 1 ^ 2) * a 1 ^ 2 +
      (∑ r ∈ rows, B r 2 ^ 2) * a 2 ^ 2 +
      2 * (∑ r ∈ rows, B r 0 * B r 1) * (a 0 * a 1) +
      2 * (∑ r ∈ rows, B r 0 * B r 2) * (a 0 * a 2) +
      2 * (∑ r ∈ rows, B r 1 * B r 2) * (a 1 * a 2) := by
    unfold columnEnergy
    simp only [Fin.sum_univ_three, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hdiag 0, hdiag 1, hdiag 2] at hexpand
  have h01 := gram_cross_lower _ (a 0) (a 1) (hoff 0 1 (by decide))
  have h02 := gram_cross_lower _ (a 0) (a 2) (hoff 0 2 (by decide))
  have h12 := gram_cross_lower _ (a 1) (a 2) (hoff 1 2 (by decide))
  have allThree (h0 : a 0 ≠ 0) (h1 : a 1 ≠ 0) (h2 : a 2 ≠ 0) :
      6 ≤ columnEnergy rows B a := by
    linarith only [hexpand, h01, h02, h12, one_le_int_sq h0, one_le_int_sq h1, one_le_int_sq h2]
  have gap (htwo : ∃ i j, i ≠ j ∧ a i ≠ 0 ∧ a j ≠ 0) : 6 ≤ columnEnergy rows B a := by
    obtain ⟨i, j, hij, hi, hj⟩ := htwo
    have hpairs : (a 0 ≠ 0 ∧ a 1 ≠ 0) ∨ (a 0 ≠ 0 ∧ a 2 ≠ 0) ∨ (a 1 ≠ 0 ∧ a 2 ≠ 0) := by
      fin_cases i <;> fin_cases j <;> simp_all <;> tauto
    rcases hpairs with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
    · by_cases h2 : a 2 = 0
      · simp [h2] at hexpand
        linarith only [hexpand, h01, one_le_int_sq h0, one_le_int_sq h1]
      · exact allThree h0 h1 h2
    · by_cases h1 : a 1 = 0
      · simp [h1] at hexpand
        linarith only [hexpand, h02, one_le_int_sq h0, one_le_int_sq h2]
      · exact allThree h0 h1 h2
    · by_cases h0 : a 0 = 0
      · simp [h0] at hexpand
        linarith only [hexpand, h12, one_le_int_sq h1, one_le_int_sq h2]
      · exact allThree h0 h1 h2
  have single (i : Fin 3) (hrest : ∀ j, j ≠ i → a j = 0) :
      columnEnergy rows B a = 4 * a i ^ 2 := by
    unfold columnEnergy
    calc
      _ = ∑ r ∈ rows, (B r i * a i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        congr 1
        exact Finset.sum_eq_single i (fun j _ hji => by rw [hrest j hji, mul_zero]) (by simp)
      _ = (∑ r ∈ rows, B r i ^ 2) * a i ^ 2 := by
        simp only [mul_pow, Finset.sum_mul]
      _ = _ := by rw [hdiag i]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  have rest (h : ¬ ∃ j k, j ≠ k ∧ a j ≠ 0 ∧ a k ≠ 0) : ∀ j, j ≠ i → a j = 0 := by
    intro j hji
    by_contra hj
    exact h ⟨j, i, hji, hj, hi⟩
  refine ⟨?_, ⟨?_, ?_⟩, gap⟩
  · by_cases h : ∃ j k, j ≠ k ∧ a j ≠ 0 ∧ a k ≠ 0
    · exact le_trans (by decide : (4 : ℤ) ≤ 6) (gap h)
    · rw [single i (rest h)]
      linarith only [one_le_int_sq hi]
  · intro he
    have hrest := rest (fun h => by have := gap h; omega)
    have hsquare : a i ^ 2 = 1 := by linarith only [he, single i hrest]
    exact ⟨i, sq_eq_one_iff.mp hsquare, hrest⟩
  · rintro ⟨j, hj, hrest⟩
    rw [single j hrest, sq_eq_one_iff.mpr hj] <;> decide

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy
