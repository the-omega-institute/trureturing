/- GID: D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.claim; result=D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.result; claim=D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.claim
   digest: Star matrices force unbounded internal dimension in vector-valued orthostochastic lifts. -/

import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
Vector-valued orthostochastic lifts of star matrices require at least one internal
dimension per noncentral column.
-/

noncomputable section

open Matrix Finset
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Matrix.GutkinOrthostochasticDimensionRefutation

/-- The norm equations and both orthogonality equations in Gutkin's definition of `Iso`. -/
def IsGutkinLift {n d : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (V : Fin n → Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ r c, ‖V r c‖ ^ 2 = P r c) ∧
  (∀ j k, ∑ r, ⟪V r j, V r k⟫ = if j = k then 1 else 0) ∧
  (∀ j k, ∑ c, ⟪V j c, V k c⟫ = if j = k then 1 else 0)

/-- Real vector-valued orthostochasticity with internal dimension `d`. -/
def IsOrthostochasticOfDim {n : ℕ} (d : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P ∈ doublyStochastic ℝ (Fin n) ∧ ∃ V : Fin n → Fin n → EuclideanSpace ℝ (Fin d), IsGutkinLift P V

/-- The natural-number infimum of the dimensions admitting every bistochastic matrix. -/
def dMin (n : ℕ) : ℕ :=
  sInf {d : ℕ | ∀ P ∈ doublyStochastic ℝ (Fin n), IsOrthostochasticOfDim d P}

/-- Gutkin's Conjecture 1. -/
def claim : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, 2 ≤ dMin n ∧ dMin n ≤ 3

/-- The symmetric matrix supported on a star and the noncentral diagonal. -/
def starMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun r c =>
    if r.val = 0 then
      if c.val = 0 then 0 else 1 / ((n - 1 : ℕ) : ℝ)
    else if c.val = 0 then 1 / ((n - 1 : ℕ) : ℝ)
    else if r = c then 1 - 1 / ((n - 1 : ℕ) : ℝ) else 0

private lemma star_symmetric (n : ℕ) (r c : Fin n) :
    starMatrix n r c = starMatrix n c r := by
  unfold starMatrix
  by_cases hr : r.val = 0 <;> by_cases hc : c.val = 0 <;>
    simp only [hr, hc, ite_true, ite_false, eq_comm]

private lemma star_row_sum {n : ℕ} (hn : 2 ≤ n) (r : Fin n) :
    ∑ c, starMatrix n r c = 1 := by
  let : NeZero n := ⟨by omega⟩
  have hden : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - 1 ≠ 0)
  by_cases hr : r.val = 0
  · have he (c : Fin n) : starMatrix n r c =
        1 / ((n - 1 : ℕ) : ℝ) - if c = 0 then 1 / ((n - 1 : ℕ) : ℝ) else 0 := by
      simp only [starMatrix, hr, ite_true, Fin.val_eq_zero_iff]
      split <;> ring
    simp_rw [he]
    simp only [sum_sub_distrib, sum_const, card_fin, nsmul_eq_mul,
      sum_ite_eq', mem_univ, ite_true]
    have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : n = n - 1 + 1)
    rw [hcast]
    field_simp
    ring
  · have hr0 : r ≠ 0 := by intro h; apply hr; rw [h]; rfl
    have he (c : Fin n) : starMatrix n r c =
        (if c = 0 then 1 / ((n - 1 : ℕ) : ℝ) else 0) +
        (if c = r then 1 - 1 / ((n - 1 : ℕ) : ℝ) else 0) := by
      simp only [starMatrix, hr, ite_false, Fin.val_eq_zero_iff]
      by_cases hc : c = 0 <;> by_cases hcr : c = r <;>
        simp_all only [ite_true, ite_false, eq_comm, add_zero, zero_add, not_false_eq_true]
    simp_rw [he]
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    ring

private lemma star_doubly_stochastic {n : ℕ} (hn : 2 ≤ n) :
    starMatrix n ∈ doublyStochastic ℝ (Fin n) := by
  have hden : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n - 1)
  have ha : 0 ≤ 1 / ((n - 1 : ℕ) : ℝ) := div_nonneg (by norm_num) (by linarith)
  have hb : 1 / ((n - 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).2 hden
  refine mem_doublyStochastic_iff_sum.mpr ⟨?_, star_row_sum hn, ?_⟩
  · intro r c
    unfold starMatrix
    split <;> split <;> (try split) <;> linarith
  · intro c
    simp_rw [star_symmetric n _ c]
    exact star_row_sum hn c

private lemma star_lift_dimension_bound {n d : ℕ} (hn : 2 ≤ n)
    (V : Fin n → Fin n → EuclideanSpace ℝ (Fin d))
    (hNorm : ∀ r c, ‖V r c‖ ^ 2 = starMatrix n r c)
    (hColumn : ∀ j k, ∑ r, ⟪V r j, V r k⟫ = if j = k then 1 else 0) :
    n - 1 ≤ d := by
  let : NeZero n := ⟨by omega⟩
  have hzero (r c : Fin n) (h : starMatrix n r c = 0) : V r c = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp ((hNorm r c).trans h)
  have hcross (j k : Fin n) (hj : j.val ≠ 0) (hk : k.val ≠ 0) (hjk : j ≠ k) :
      ⟪V 0 j, V 0 k⟫ = 0 := by
    have he : ∑ r, ⟪V r j, V r k⟫ = ⟪V 0 j, V 0 k⟫ := by
      apply sum_eq_single 0
      · intro r _ hr
        have hr' : r.val ≠ 0 := by
          intro h
          exact hr (Fin.ext h)
        by_cases hrj : r = j
        · have hrk : r ≠ k := by rwa [hrj]
          have hz : V r k = 0 := hzero r k (by
            simp only [starMatrix, hr', hk, hrk, ite_false])
          rw [hz, inner_zero_right]
        · have hz : V r j = 0 := hzero r j (by
            simp only [starMatrix, hr', hj, hrj, ite_false])
          rw [hz, inner_zero_left]
      · intro h
        exact False.elim (h (mem_univ 0))
    rw [← he, hColumn, ite_eq_right hjk]
  let col : Fin (n - 1) → Fin n := fun j => ⟨j.val + 1, by omega⟩
  have hc0 (j : Fin (n - 1)) : (col j).val ≠ 0 := by
    change j.val + 1 ≠ 0
    omega
  have hne (j : Fin (n - 1)) : V 0 (col j) ≠ 0 := by
    intro hz
    have h := hNorm 0 (col j)
    rw [hz, norm_zero, zero_pow (by decide)] at h
    have ha : (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact one_div_ne_zero (by exact_mod_cast (by omega : n - 1 ≠ 0))
    apply ha
    have he : 0 = (1 : ℝ) / ((n - 1 : ℕ) : ℝ) := by
      simpa only [starMatrix, Fin.val_zero, ite_true, hc0 j, ite_false] using h
    exact he.symm
  have horth : Pairwise fun j k : Fin (n - 1) => ⟪V 0 (col j), V 0 (col k)⟫ = 0 := by
    intro j k hjk
    apply hcross (col j) (col k) (hc0 j) (hc0 k)
    intro h
    apply hjk
    apply Fin.ext
    have hval := congrArg Fin.val h
    change j.val + 1 = k.val + 1 at hval
    omega
  have hli : LinearIndependent ℝ (fun j : Fin (n - 1) => V 0 (col j)) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hne horth
  have hdim := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin] at hdim
  exact hdim

theorem result : ¬ claim := by
  rintro ⟨n₀, hn₀⟩
  let n := max n₀ 5
  obtain ⟨hmin, hmax⟩ := hn₀ n (le_max_left _ _)
  have hn : 5 ≤ n := le_max_right _ _
  let dims : Set ℕ :=
    {d | ∀ P ∈ doublyStochastic ℝ (Fin n), IsOrthostochasticOfDim d P}
  have hnonempty : dims.Nonempty := by
    by_contra h
    have hempty : dims = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hzero : dMin n = 0 := Nat.sInf_eq_zero.mpr (Or.inr hempty)
    omega
  have hmem : dMin n ∈ dims := Nat.sInf_mem hnonempty
  obtain ⟨_, V, hNorm, hColumn, _⟩ :=
    hmem (starMatrix n) (star_doubly_stochastic (by omega))
  have hdim := star_lift_dimension_bound (by omega : 2 ≤ n) V hNorm hColumn
  omega

end D5.S3.Quantum.Matrix.GutkinOrthostochasticDimensionRefutation
