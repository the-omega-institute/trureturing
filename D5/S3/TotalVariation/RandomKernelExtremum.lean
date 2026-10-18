/- GID: D5/S3/TotalVariation/RandomKernelExtremum
   generality: G
   mirror-B: D5/B/S3/TotalVariation/RandomKernelExtremum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp separable simplex estimates for stochastic approximation to independence. -/

import D5.S3.TotalVariation.Metric
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open scoped BigOperators
noncomputable section
namespace D5.S3.TotalVariation.RandomKernelExtremum

/-- The finite-dimensional candidate indexed by the support size. -/
def coefficient (d k : ℕ) : ℝ :=
  ((k : ℝ) - 1) / ((k : ℝ) * ((d : ℝ) + k - 2))

/-- Zero-valued indices zero and one make the maximum total at every dimension. -/
def beta (d : ℕ) : ℝ :=
  (Finset.range (d + 1)).sup' (by simp) (coefficient d)

/-- The proposed uniform approximation radius. -/
def rho (d : ℕ) : ℝ := ((d : ℝ) - 1) * beta d

/-- The overlap contribution of one marginal coordinate. -/
def overlap (b a x : ℝ) : ℝ := (1 - x) * min b x + x * min a x

private theorem coefficient_le_beta {d k : ℕ} (hk : k ≤ d) :
    coefficient d k ≤ beta d := by
  exact Finset.le_sup' (coefficient d) (Finset.mem_range.mpr (by omega))

private theorem beta_nonneg (d : ℕ) : 0 ≤ beta d := by
  have h := coefficient_le_beta (d := d) (k := 0) (by omega)
  simpa [coefficient] using h

/-- A finite simplex bound with independently checkable scalar hypotheses.
The finite support inequalities and the discriminant bound control all three pieces. -/
theorem simplex_overlap_bound {d : ℕ} (b a : ℝ)
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 3 / 4)
    (hdisc : a ^ 2 ≤ 4 * b)
    (hrel : a = 1 - ((d : ℝ) - 1) * b)
    (hfinite : ∀ n : ℕ, 2 ≤ n → n ≤ d →
      a ≤ 1 / (n : ℝ) + ((n : ℝ) - 1) * b)
    (s : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i) (hm : ∑ i, s i = 1) :
    a ≤ ∑ i, overlap b a (s i) := by
  classical
  have hx (i : Fin d) : s i ≤ 1 := by
    rw [← hm]
    exact Finset.single_le_sum (fun j _ => hs j) (Finset.mem_univ i)
  have hpoint (i : Fin d) : (a - b) * s i ≤ overlap b a (s i) := by
    by_cases hl : s i ≤ b
    · simp only [overlap, min_eq_right hl, min_eq_right (hl.trans hba)]
      nlinarith [hs i]
    · by_cases hh : a ≤ s i
      · simp only [overlap, min_eq_left (le_of_not_ge hl), min_eq_left hh]
        nlinarith
      · simp only [overlap, min_eq_left (le_of_not_ge hl),
          min_eq_right (le_of_not_ge hh)]
        nlinarith [sq_nonneg (s i - a / 2)]
  by_cases hhigh : ∃ i, a ≤ s i
  · obtain ⟨j, hj⟩ := hhigh
    have hall : ∑ i, (a - b) * s i + (if i = j then b else 0) ≤
        ∑ i, overlap b a (s i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hij : i = j
      · subst i
        simp only [ite_true, overlap, min_eq_left (hba.trans hj), min_eq_left hj]
        ring_nf
        exact le_rfl
      · simpa [hij] using hpoint i
    simpa [Finset.sum_add_distrib, ← Finset.mul_sum, hm] using hall
  · have hlowhigh (i : Fin d) : s i ≤ a := le_of_not_ge (fun h => hhigh ⟨i, h⟩)
    let M := Finset.univ.filter (fun i : Fin d => b ≤ s i)
    let L := Finset.univ.filter (fun i : Fin d => ¬ b ≤ s i)
    let t : ℝ := ∑ i ∈ M, s i
    let q : ℝ := ∑ i ∈ M, s i ^ 2
    let n : ℕ := M.card
    have ht0 : 0 ≤ t := Finset.sum_nonneg (fun i _ => hs i)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [← hm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hs i)
    have hsplit : (∑ i ∈ M, s i) + ∑ i ∈ L, s i = 1 := by
      simpa [M, L] using (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i : Fin d => b ≤ s i) (f := s)).trans hm
    have hform : ∑ i, overlap b a (s i) = 1 - t + q - b * t + (n : ℝ) * b := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun i : Fin d => b ≤ s i)]
      have hM : (∑ i ∈ M, overlap b a (s i)) = q - b * t + (n : ℝ) * b := by
        calc
          _ = ∑ i ∈ M, (s i ^ 2 - b * s i + b) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi' := (Finset.mem_filter.mp hi).2
            simp only [overlap, min_eq_left hi', min_eq_right (hlowhigh i)]
            ring
          _ = _ := by simp [q, t, n, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hL : (∑ i ∈ L, overlap b a (s i)) = ∑ i ∈ L, s i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : s i ≤ b := le_of_not_ge (Finset.mem_filter.mp hi).2
        simp only [overlap, min_eq_right hi', min_eq_right (hi'.trans hba)]
        ring
      change (∑ i ∈ M, overlap b a (s i)) + ∑ i ∈ L, overlap b a (s i) = _
      rw [hM, hL]
      dsimp [t] at *
      linarith
    rw [hform]
    have hn : n ≤ d := by
      dsimp [n]
      simpa using Finset.card_le_card (Finset.filter_subset (fun i : Fin d => b ≤ s i) Finset.univ)
    have hcs : t ^ 2 ≤ (n : ℝ) * q := by
      exact sq_sum_le_card_mul_sum_sq
    rcases n with _ | n
    · have hM0 : M = ∅ := Finset.card_eq_zero.mp (show M.card = 0 from rfl)
      have ht : t = 0 := by simp [t, hM0]
      have hq : q = 0 := by simp [q, hM0]
      simp only [Nat.cast_zero, zero_mul, ht, hq, sub_zero, add_zero]
      linarith
    · by_cases hn1 : n = 0
      · subst n
        norm_num at hcs ⊢
        have hbt : 0 ≤ b * (1 - t) := mul_nonneg hb (sub_nonneg.mpr ht1)
        nlinarith [sq_nonneg (t - 1 / 2)]
      · have hn2 : 2 ≤ n + 1 := by omega
        have hnpos : (0 : ℝ) < n + 1 := by positivity
        have hnreal : (2 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hn2
        have hf := hfinite (n + 1) hn2 hn
        have haux : 1 - t + t ^ 2 / (n + 1 : ℕ) - b * t + ((n + 1 : ℕ) : ℝ) * b ≥
            1 / (n + 1 : ℕ) + (((n + 1 : ℕ) : ℝ) - 1) * b := by
          have hnpos' : (0 : ℝ) < (n + 1 : ℕ) := by positivity
          apply (le_of_sub_nonneg ?_)
          have hmul : 0 ≤ (1 - t) * (((n + 1 : ℕ) : ℝ) - (1 + t) + b * (n + 1 : ℕ)) := by
            apply mul_nonneg (sub_nonneg.mpr ht1)
            nlinarith
          apply (mul_nonneg_iff_of_pos_right hnpos').mp
          convert hmul using 1 <;> field_simp <;> ring
        have hq : t ^ 2 / (n + 1 : ℕ) ≤ q := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
          simpa [mul_comm] using hcs
        linarith

#print axioms simplex_overlap_bound
end D5.S3.TotalVariation.RandomKernelExtremum
