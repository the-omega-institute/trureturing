/- GID: D5/S3/TotalVariation/RandomKernelExtremum
   generality: G
   mirror-B: D5/B/S3/TotalVariation/RandomKernelExtremum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp separable simplex estimates for stochastic approximation to independence. -/

import D5.S3.TotalVariation.Metric
import D5.S3.TotalVariation.Convexity
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
private theorem simplex_overlap_bound {d : ℕ} (b a : ℝ)
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 3 / 4)
    (hdisc : a ^ 2 ≤ 4 * b)
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
    have hall : (∑ i, ((a - b) * s i + (if i = j then b else 0))) ≤
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
    by_cases hn0 : n = 0
    · have hM0 : M = ∅ := Finset.card_eq_zero.mp hn0
      have ht : t = 0 := by simp [t, hM0]
      have hq : q = 0 := by simp [q, hM0]
      simp only [hn0, Nat.cast_zero, zero_mul, ht, hq, sub_zero, add_zero]
      linarith
    · by_cases hn1 : n = 1
      · rw [hn1, Nat.cast_one, one_mul] at hcs ⊢
        have hbt : 0 ≤ b * (1 - t) := mul_nonneg hb (sub_nonneg.mpr ht1)
        nlinarith only [hcs, hbt, ha, sq_nonneg (t - 1 / 2)]
      · have hn2 : 2 ≤ n := by omega
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hf := hfinite n hn2 hn
        have haux : 1 / (n : ℝ) + ((n : ℝ) - 1) * b ≤
            1 - t + t ^ 2 / n - b * t + (n : ℝ) * b := by
          apply le_of_sub_nonneg
          have hmul : 0 ≤ (1 - t) * ((n : ℝ) - (1 + t) + b * n) := by
            apply mul_nonneg (sub_nonneg.mpr ht1)
            nlinarith only [hnreal, ht1, mul_nonneg hb hnpos.le]
          apply (mul_nonneg_iff_of_pos_right hnpos).mp
          convert hmul using 1 <;> field_simp <;> ring
        have hq : t ^ 2 / n ≤ q := (div_le_iff₀ hnpos).mpr (by simpa [mul_comm] using hcs)
        linarith only [hf, haux, hq]

private theorem beta_le_inv {d : ℕ} (hd : 2 ≤ d) : beta d ≤ 1 / (d : ℝ) := by
  apply Finset.sup'_le
  intro k hk
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  rcases k with _ | k
  · simp [coefficient, le_of_lt (one_div_pos.mpr hd0)]
  · rcases k with _ | k
    · simp [coefficient, le_of_lt (one_div_pos.mpr hd0)]
    · have hkR : (2 : ℝ) ≤ (k + 2 : ℕ) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
      have hden : (0 : ℝ) < (k + 2 : ℕ) * ((d : ℝ) + (k + 2 : ℕ) - 2) := mul_pos (by linarith) (by linarith)
      unfold coefficient
      apply (div_le_div_iff₀ hden hd0).mpr
      nlinarith only [hdR, hkR, mul_nonneg (sub_nonneg.mpr hkR) (by positivity : (0 : ℝ) ≤ (k + 2 : ℕ))]

private theorem beta_two {d : ℕ} (hd : 2 ≤ d) : 1 / (2 * (d : ℝ)) ≤ beta d := by
  have h := coefficient_le_beta (d := d) (k := 2) hd
  simpa only [coefficient, Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num,
    show (d : ℝ) + 2 - 2 = d by ring] using h

private theorem beta_support {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n) (hnd : n ≤ d) :
    1 - ((d : ℝ) - 1) * beta d ≤ 1 / (n : ℝ) + ((n : ℝ) - 1) * beta d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((d : ℝ) + n - 2) := mul_pos (by linarith) (by linarith)
  have h : (n : ℝ) - 1 ≤ beta d * ((n : ℝ) * ((d : ℝ) + n - 2)) :=
    (div_le_iff₀ hden).mp (coefficient_le_beta hnd)
  have hn0 : (0 : ℝ) < n := by linarith
  apply (mul_le_mul_iff_right₀ hn0).mp
  field_simp
  nlinarith only [h]

private theorem beta_discriminant {d : ℕ} (hd : 2 ≤ d) :
    (1 - ((d : ℝ) - 1) * beta d) ^ 2 ≤ 4 * beta d := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.range (d + 1)).Nonempty by simp) (coefficient d)
  change beta d = coefficient d k at hmax
  have hkd : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hβpos : 0 < beta d := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (2 * (d : ℝ))) (beta_two hd)
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> simp [coefficient] at hmax <;> linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hden : (0 : ℝ) < (k : ℝ) * ((d : ℝ) + k - 2) := mul_pos (by linarith) (by linarith)
  have hlower : ((k : ℝ) - 1) * ((k : ℝ) - 2) ≤ (d : ℝ) - 1 := by
    by_cases hk3 : 3 ≤ k
    · have hprev := coefficient_le_beta (d := d) (k := k - 1) (by omega)
      rw [hmax] at hprev
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      simp only [coefficient, hcast] at hprev
      have hprevden : 0 < ((k : ℝ) - 1) * ((d : ℝ) + ((k : ℝ) - 1) - 2) := by
        have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
        exact mul_pos (by linarith) (by linarith)
      have hcross := (div_le_div_iff₀ hprevden hden).mp hprev
      nlinarith only [hcross]
    · have : k = 2 := by omega
      subst k
      norm_num
      linarith
  have hupper : (d : ℝ) - 1 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    by_cases hlast : k = d
    · rw [hlast]
      nlinarith only [hdR]
    · have hnext := coefficient_le_beta (d := d) (k := k + 1) (by omega)
      rw [hmax] at hnext
      simp only [coefficient, Nat.cast_add, Nat.cast_one] at hnext
      have hnextden : 0 < ((k : ℝ) + 1) * ((d : ℝ) + ((k : ℝ) + 1) - 2) := mul_pos (by linarith) (by linarith)
      have hcross := (div_le_div_iff₀ hnextden hden).mp hnext
      nlinarith only [hcross]
  have hgap : 0 ≤ (k : ℝ) * (k - 1) - (d - 1) := sub_nonneg.mpr hupper
  have hgap2 : (k : ℝ) * (k - 1) - (d - 1) ≤ 2 * (k - 1) := by nlinarith only [hlower]
  have hsq : ((k : ℝ) * (k - 1) - (d - 1)) ^ 2 ≤ 4 * (k - 1) ^ 2 := by
    nlinarith only [mul_nonneg hgap (sub_nonneg.mpr hgap2), sq_nonneg (2 * (k : ℝ) - 2 - ((k : ℝ) * (k - 1) - (d - 1)))]
  have hpoly : ((d : ℝ) - 1 + k * (k - 1)) ^ 2 ≤
      4 * k * (k - 1) * ((d : ℝ) + k - 2) := by
    have hmore : 0 ≤ ((k : ℝ) - 1) ^ 2 * ((k : ℝ) - 1) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hsq, hmore]
  rw [hmax]
  unfold coefficient
  have haeq : 1 - ((d : ℝ) - 1) * (((k : ℝ) - 1) / ((k : ℝ) * ((d : ℝ) + k - 2))) =
      ((d : ℝ) - 1 + k * (k - 1)) / ((k : ℝ) * ((d : ℝ) + k - 2)) := by
    field_simp [show ((d : ℝ) + k - 2) ≠ 0 by linarith,
      show (k : ℝ) ≠ 0 by linarith]
    <;> ring
  rw [haeq, div_pow]
  calc
    _ ≤ (4 * k * (k - 1) * ((d : ℝ) + k - 2)) /
        ((k : ℝ) * ((d : ℝ) + k - 2)) ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hpoly
    _ = _ := by
      field_simp
      <;> ring

/-- The complete nonconvex separable bound for every real probability vector in every d>=2. -/
theorem sharp_simplex_overlap_bound {d : ℕ} (hd : 2 ≤ d)
    (s : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i) (hm : ∑ i, s i = 1) :
    1 - rho d ≤ ∑ i, overlap (beta d) (1 - rho d) (s i) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hb := beta_nonneg d
  have hbhi := (le_div_iff₀ hd0).mp (beta_le_inv hd)
  have hblo := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))).mp (beta_two hd)
  apply simplex_overlap_bound (beta d) (1 - rho d) hb
  · dsimp [rho]
    nlinarith only [hbhi]
  · dsimp [rho]
    have hprod : 0 ≤ ((d : ℝ) - 2) * beta d := mul_nonneg (by linarith) hb
    nlinarith only [hblo, hprod, hdR]
  · exact beta_discriminant hd
  · exact fun n hn hnd => beta_support hd hn hnd
  · exact hs
  · exact hm

#print axioms sharp_simplex_overlap_bound


open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric

/-- A label is retained with probability 1-rho; each other label receives beta. -/
def replacement (d : ℕ) (i x : Fin d) : ℝ :=
  if x = i then 1 - rho d else beta d

/-- Change the first coordinate and retain the second coordinate. -/
def firstOutput {d : ℕ} (p : Fin d × Fin d → ℝ) (z : Fin d × Fin d) : ℝ :=
  ∑ i, p (i, z.2) * replacement d i z.1

/-- Average the two one-coordinate replacement channels. -/
def optimalActive {d : ℕ} (p : Fin d × Fin d → ℝ) (z : Fin d × Fin d) : ℝ :=
  (firstOutput p z + firstOutput (fun z => p z.swap) z.swap) / 2

private theorem replacement_mass {d : ℕ} (i : Fin d) :
    ∑ x, replacement d i x = 1 := by
  classical
  have heq (x : Fin d) : replacement d i x = beta d +
      if x = i then 1 - (d : ℝ) * beta d else 0 := by
    by_cases h : x = i <;> simp [replacement, h, rho] <;> ring
  simp only [heq, Finset.sum_add_distrib]
  simp [rho]
  <;> ring

private theorem tv_overlap {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    totalVariation p q = 1 - ∑ x, min (p x) (q x) := by
  have heq (x : X) : |p x - q x| = p x + q x - 2 * min (p x) (q x) := by
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp only [totalVariation, heq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp, hq]
  ring

private theorem replacement_average {d : ℕ} (s : Fin d → ℝ) (hm : ∑ i, s i = 1) :
    (∑ i, s i * totalVariation (replacement d i) s) =
      1 - ∑ x, overlap (beta d) (1 - rho d) (s x) := by
  classical
  simp_rw [tv_overlap _ _ (replacement_mass _) hm, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hm]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have heq (i : Fin d) : s i * min (replacement d i x) (s x) =
      s i * min (beta d) (s x) +
        if i = x then s x * (min (1 - rho d) (s x) - min (beta d) (s x)) else 0 := by
    by_cases h : i = x
    · subst i; simp [replacement]; ring
    · have h' : x ≠ i := Ne.symm h
      simp [replacement, h, h']
  simp only [heq, Finset.sum_add_distrib, ← Finset.sum_mul, hm, one_mul]
  simp [overlap]
  <;> ring

private theorem first_output_le {d : ℕ} (hd : 2 ≤ d)
    (p : Fin d × Fin d → ℝ) (hp : ∀ z, 0 ≤ p z) (hm : ∑ z, p z = 1) :
    totalVariation (firstOutput p)
      (fun z => (∑ j, p (z.1, j)) * (∑ i, p (i, z.2))) ≤ rho d := by
  let s : Fin d → ℝ := fun i => ∑ j, p (i, j)
  have hs (i : Fin d) : 0 ≤ s i := Finset.sum_nonneg fun j _ => hp (i, j)
  have hsm : ∑ i, s i = 1 := by simpa [s, Fintype.sum_prod_type] using hm
  have heq (x j : Fin d) : firstOutput p (x, j) - s x * (∑ i, p (i, j)) =
      ∑ i, p (i, j) * (replacement d i x - s x) := by
    simp only [firstOutput, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have habs (x j : Fin d) : |firstOutput p (x, j) - s x * (∑ i, p (i, j))| ≤
      ∑ i, p (i, j) * |replacement d i x - s x| := by
    rw [heq]
    calc
      _ ≤ ∑ i, |p (i, j) * (replacement d i x - s x)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hp _)]
  have hbound : totalVariation (firstOutput p)
      (fun z => s z.1 * (∑ i, p (i, z.2))) ≤
      ∑ i, s i * totalVariation (replacement d i) s := by
    simp only [totalVariation, Fintype.sum_prod_type]
    calc
      _ ≤ (1 / 2 : ℝ) * ∑ x, ∑ j, ∑ i, p (i, j) * |replacement d i x - s x| := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun j _ => habs x j
      _ = _ := by
        simp_rw [Finset.sum_comm (f := fun j i => p (i, j) * |replacement d i _ - s _|)]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
        dsimp [s]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hsharp := sharp_simplex_overlap_bound hd s hs hsm
  rw [replacement_average s hsm] at hbound
  exact hbound.trans (by linarith only [hsharp])

/-- Every active joint law, with arbitrary zero entries, obeys the proposed approximation bound. -/
theorem active_joint_upper_bound {d : ℕ} (hd : 2 ≤ d)
    (p : Fin d × Fin d → ℝ) (hp : ∀ z, 0 ≤ p z) (hm : ∑ z, p z = 1) :
    totalVariation (optimalActive p)
      (fun z => (∑ j, p (z.1, j)) * (∑ i, p (i, z.2))) ≤ rho d := by
  have hfirst := first_output_le hd p hp hm
  have hswap : (∑ z : Fin d × Fin d, p z.swap) = 1 := by
    simp only [Fintype.sum_prod_type, Prod.swap_prod_mk] at hm ⊢
    rw [Finset.sum_comm]
    exact hm
  have hsecond := first_output_le hd (fun z => p z.swap) (fun z => hp z.swap) hswap
  let target : Fin d × Fin d → ℝ := fun z => (∑ j, p (z.1, j)) * (∑ i, p (i, z.2))
  have hsecond' : totalVariation (fun z => firstOutput (fun z => p z.swap) z.swap) target ≤ rho d := by
    simp only [totalVariation, Fintype.sum_prod_type, Prod.swap_prod_mk] at hsecond ⊢
    rw [Finset.sum_comm]
    simpa only [target, mul_comm] using hsecond
  have hc := D5.S3.TotalVariation.Convexity.total_variation_joint_convex
    (firstOutput p) (fun z => firstOutput (fun z => p z.swap) z.swap) target target
    (1 / 2) (by constructor <;> norm_num)
  have heq : (fun i => (1 / 2 : ℝ) * target i + (1 - 1 / 2) * target i) = target := by
    funext i; ring
  rw [heq] at hc
  have hleft : (fun i => (1 / 2 : ℝ) * firstOutput p i +
      (1 - 1 / 2) * firstOutput (fun z => p z.swap) i.swap) = optimalActive p := by
    funext i; simp [optimalActive]; ring
  rw [hleft] at hc
  dsimp [target] at *
  linarith only [hc, hfirst, hsecond']

#print axioms active_joint_upper_bound


/-- Conditional independence completion preserves the blocking mass. -/
def completion {d : ℕ} (p : Option (Fin d × Fin d) → ℝ) : Option (Fin d × Fin d) → ℝ
  | none => p none
  | some z => if 0 < 1 - p none then
      (∑ j, p (some (z.1, j))) * (∑ i, p (some (i, z.2))) / (1 - p none)
    else 0

/-- Output-first indexing makes the stochasticity condition a column sum. -/
def optimalKernel (d : ℕ) : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ
  | none, none => 1
  | some _, none => 0
  | none, some _ => 0
  | some x, some y =>
    (replacement d y.1 x.1 * (if x.2 = y.2 then 1 else 0) +
      (if x.1 = y.1 then 1 else 0) * replacement d y.2 x.2) / 2

/-- Matrix action on an unknown source law. -/
def kernelOutput {d : ℕ} (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ)
    (p : Option (Fin d × Fin d) → ℝ) (x : Option (Fin d × Fin d)) : ℝ :=
  ∑ y, K x y * p y

/-- Uniform error over all nonnegative normalized real source laws. -/
def worstError {d : ℕ} (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ) : ℝ :=
  sSup {e : ℝ | ∃ p : Option (Fin d × Fin d) → ℝ,
    (∀ z, 0 ≤ p z) ∧ (∑ z, p z = 1) ∧ e = totalVariation (kernelOutput K p) (completion p)}

private theorem tv_scale {X : Type*} [Fintype X] (r : ℝ) (hr : 0 ≤ r) (p q : X → ℝ) :
    totalVariation (fun x => r * p x) (fun x => r * q x) = r * totalVariation p q := by
  simp only [totalVariation, ← mul_sub, abs_mul, abs_of_nonneg hr, ← Finset.mul_sum]
  ring

private theorem optimal_linear {d : ℕ} (r : ℝ) (p : Fin d × Fin d → ℝ) :
    optimalActive (fun z => r * p z) = fun z => r * optimalActive p z := by
  funext z
  simp [optimalActive, firstOutput, mul_assoc, ← Finset.mul_sum]
  ring

private theorem active_scaled_bound {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (hr : 0 < r)
    (p : Fin d × Fin d → ℝ) (hp : ∀ z, 0 ≤ p z) (hm : ∑ z, p z = r) :
    totalVariation (optimalActive p)
      (fun z => (∑ j, p (z.1, j)) * (∑ i, p (i, z.2)) / r) ≤ r * rho d := by
  let q : Fin d × Fin d → ℝ := fun z => p z / r
  have hq (z) : 0 ≤ q z := div_nonneg (hp z) hr.le
  have hqm : ∑ z, q z = 1 := by simp [q, ← Finset.sum_div, hm, hr.ne']
  have hpq : p = fun z => r * q z := by funext z; dsimp [q]; field_simp [hr.ne'] <;> ring
  have htarget : (fun z : Fin d × Fin d => (∑ j, p (z.1, j)) * (∑ i, p (i, z.2)) / r) =
      fun z => r * ((∑ j, q (z.1, j)) * (∑ i, q (i, z.2))) := by
    funext z
    simp only [q, ← Finset.sum_div]
    field_simp [hr.ne']
    <;> ring
  rw [htarget, hpq, optimal_linear, tv_scale r hr.le]
  exact mul_le_mul_of_nonneg_left (active_joint_upper_bound hd q hq hqm) hr.le

private theorem optimal_output {d : ℕ} (p : Option (Fin d × Fin d) → ℝ) :
    kernelOutput (optimalKernel d) p = fun z => match z with
      | none => p none
      | some z => optimalActive (fun z => p (some z)) z := by
  classical
  funext z
  cases z with
  | none => simp [kernelOutput, optimalKernel, Fintype.sum_option]
  | some z =>
    simp only [kernelOutput, Fintype.sum_option, optimalKernel, zero_mul, add_zero,
      Fintype.sum_prod_type, optimalActive, firstOutput, Prod.swap_prod_mk]
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simp_rw [add_mul, Finset.sum_add_distrib]
    congr 1
    · simp [mul_ite, ite_mul, eq_comm, mul_comm]

private theorem optimal_stochastic {d : ℕ} (hd : 2 ≤ d) :
    (∀ x y, 0 ≤ optimalKernel d x y) ∧ ∀ y, ∑ x, optimalKernel d x y = 1 := by
  classical
  have hb := beta_nonneg d
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hbhi := (le_div_iff₀ (by linarith : (0 : ℝ) < d)).mp (beta_le_inv hd)
  have hrep (i x : Fin d) : 0 ≤ replacement d i x := by
    unfold replacement
    split_ifs
    · dsimp [rho]; nlinarith only [hb, hbhi]
    · exact hb
  constructor
  · intro x y
    cases x with
    | none => cases y <;> norm_num [optimalKernel]
    | some x =>
      cases y with
      | none => norm_num [optimalKernel]
      | some y =>
        simp only [optimalKernel]
        apply div_nonneg _ (by norm_num)
        apply add_nonneg
        · exact mul_nonneg (hrep _ _) (by split_ifs <;> norm_num)
        · exact mul_nonneg (by split_ifs <;> norm_num) (hrep _ _)
  · intro y
    cases y with
    | none => simp [optimalKernel, Fintype.sum_option]
    | some y =>
      simp only [optimalKernel, Fintype.sum_option, zero_add,
        Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp [replacement_mass, Finset.sum_ite_irrel]

/-- The explicit fixed column-stochastic kernel attains the uniform upper bound,
including the blocking vertex and every partially blocked source. -/
theorem optimal_kernel_upper_bound {d : ℕ} (hd : 2 ≤ d) :
    ((∀ x y, 0 ≤ optimalKernel d x y) ∧ ∀ y, ∑ x, optimalKernel d x y = 1) ∧
    ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput (optimalKernel d) p) (completion p) ≤ rho d := by
  refine ⟨optimal_stochastic hd, ?_⟩
  intro p hp hm
  have hmass : ∑ z : Fin d × Fin d, p (some z) = 1 - p none := by
    simp only [Fintype.sum_option] at hm
    linarith only [hm]
  have hr0 : 0 ≤ 1 - p none := by
    rw [← hmass]
    exact Finset.sum_nonneg fun z _ => hp (some z)
  have hr1 : 1 - p none ≤ 1 := by linarith only [hp none]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ : 0 ≤ rho d := mul_nonneg (by linarith) (beta_nonneg d)
  rw [optimal_output]
  by_cases hr : 0 < 1 - p none
  · have hc := active_scaled_bound hd (1 - p none) hr (fun z => p (some z))
      (fun z => hp (some z)) hmass
    have htv : totalVariation
        (fun z => match z with | none => p none | some z => optimalActive (fun z => p (some z)) z)
        (completion p) =
        totalVariation (optimalActive (fun z => p (some z)))
          (fun z => (∑ j, p (some (z.1, j))) * (∑ i, p (some (i, z.2))) / (1 - p none)) := by
      simp [totalVariation, Fintype.sum_option, completion, hr]
    rw [htv]
    exact hc.trans (mul_le_of_le_one_left hρ hr1)
  · have hrz : 1 - p none = 0 := le_antisymm (le_of_not_gt hr) hr0
    have hpz (z : Fin d × Fin d) : p (some z) = 0 := by
      have hle : p (some z) ≤ ∑ w : Fin d × Fin d, p (some w) :=
        Finset.single_le_sum (fun w _ => hp (some w)) (Finset.mem_univ z)
      rw [hmass, hrz] at hle
      exact le_antisymm hle (hp _)
    have hout (z : Fin d × Fin d) : optimalActive (fun z => p (some z)) z = 0 := by
      simp [optimalActive, firstOutput, hpz]
    simp [totalVariation, Fintype.sum_option, completion, hr, hout, hρ]

#print axioms optimal_kernel_upper_bound


private theorem completion_point {d : ℕ} (i j : Fin d) :
    completion (Pi.single (some (i,j)) 1 : Option (Fin d × Fin d) → ℝ) =
      Pi.single (some (i,j)) 1 := by
  classical
  let p : Option (Fin d × Fin d) → ℝ := Pi.single (some (i,j)) 1
  have hrow (x : Fin d) : (∑ y, p (some (x,y))) = if x = i then 1 else 0 := by
    by_cases h : x = i
    · subst x; simp [p, Pi.single_apply]
    · simp [p, Pi.single_apply, Prod.mk.injEq, h, Ne.symm h]
  have hcol (y : Fin d) : (∑ x, p (some (x,y))) = if y = j then 1 else 0 := by
    by_cases h : y = j
    · subst y; simp [p, Pi.single_apply]
    · simp [p, Pi.single_apply, Prod.mk.injEq, h, Ne.symm h]
  change completion p = p
  funext z
  cases z with
  | none => rfl
  | some z =>
    rcases z with ⟨x,y⟩
    have hpnone : p none = 0 := by simp [p, Pi.single_apply]
    simp only [completion, hpnone, sub_zero, zero_lt_one, ↓reduceIte, hrow, hcol, div_one]
    by_cases h1 : x = i <;> by_cases h2 : y = j
    all_goals simp [p, Pi.single_apply, Prod.mk.injEq, h1, h2] <;> aesop

private theorem tv_point {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℝ) (hq : ∀ z, 0 ≤ q z) (hm : ∑ z, q z = 1) (x : X) :
    totalVariation q (Pi.single x 1) = 1 - q x := by
  rw [tv_overlap _ _ hm (by simp)]
  congr 1
  have hqx : q x ≤ 1 := by
    rw [← hm]
    exact Finset.single_le_sum (fun z _ => hq z) (Finset.mem_univ x)
  rw [Finset.sum_eq_single x]
  · simp [Pi.single_apply, min_eq_left hqx]
  · intro y _ hne
    simp [Pi.single_apply, hne, Ne.symm hne, min_eq_right (hq y)]
  · simp

/-- Every deterministic active source attains rho, and the supremum error of the
explicit fixed stochastic kernel is exactly rho. -/
theorem optimal_kernel_attains {d : ℕ} (hd : 2 ≤ d) :
    (∀ i j : Fin d, totalVariation
      (kernelOutput (optimalKernel d) (Pi.single (some (i,j)) 1))
      (completion (Pi.single (some (i,j)) 1)) = rho d) ∧
    worstError (optimalKernel d) = rho d := by
  classical
  obtain ⟨hstoch, hupper⟩ := optimal_kernel_upper_bound hd
  have hpoint (i j : Fin d) : totalVariation
      (kernelOutput (optimalKernel d) (Pi.single (some (i,j)) 1))
      (completion (Pi.single (some (i,j)) 1)) = rho d := by
    rw [completion_point]
    have hout : kernelOutput (optimalKernel d) (Pi.single (some (i,j)) 1) =
        fun z => optimalKernel d z (some (i,j)) := by
      funext z
      simp [kernelOutput, Pi.single_apply, mul_ite]
    rw [hout, tv_point _ (fun z => hstoch.1 z _) (hstoch.2 _) ]
    simp [optimalKernel, replacement]
  refine ⟨hpoint, ?_⟩
  let i : Fin d := ⟨0, by omega⟩
  let p : Option (Fin d × Fin d) → ℝ := Pi.single (some (i,i)) 1
  have hp : ∀ z, 0 ≤ p z := by intro z; simp [p, Pi.single_apply]; positivity
  have hm : ∑ z, p z = 1 := by simp [p]
  have hne : {e : ℝ | ∃ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) ∧ (∑ z, p z = 1) ∧
      e = totalVariation (kernelOutput (optimalKernel d) p) (completion p)}.Nonempty := by
    exact ⟨_, p, hp, hm, rfl⟩
  have hbdd : BddAbove {e : ℝ | ∃ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) ∧ (∑ z, p z = 1) ∧
      e = totalVariation (kernelOutput (optimalKernel d) p) (completion p)} := by
    refine ⟨rho d, ?_⟩
    rintro e ⟨p, hp, hm, rfl⟩
    exact hupper p hp hm
  apply le_antisymm
  · apply csSup_le hne
    rintro e ⟨q, hq, hqm, rfl⟩
    exact hupper q hq hqm
  · rw [← hpoint i i]
    exact le_csSup hbdd ⟨p, hp, hm, rfl⟩

#print axioms optimal_kernel_attains


/-- A uniform full diagonal matching, with no blocking mass. -/
def diagonalLaw (d : ℕ) : Option (Fin d × Fin d) → ℝ
  | none => 0
  | some z => if z.1 = z.2 then 1 / (d : ℝ) else 0

private theorem diagonal_probability {d : ℕ} (hd : 0 < d) :
    (∀ z, 0 ≤ diagonalLaw d z) ∧ ∑ z, diagonalLaw d z = 1 := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · intro z; cases z <;> simp only [diagonalLaw] <;> positivity
  · simp [diagonalLaw, Fintype.sum_option, Fintype.sum_prod_type, hdR.ne']

private theorem diagonal_completion {d : ℕ} (hd : 0 < d) :
    completion (diagonalLaw d) = fun z => match z with
      | none => 0 | some _ => 1 / (d : ℝ)^2 := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  funext z
  cases z <;> simp [completion, diagonalLaw, Fintype.sum_prod_type, one_div, pow_two]

private theorem diagonal_gap {d : ℕ} (hd : 0 < d) :
    totalVariation (diagonalLaw d) (completion (diagonalLaw d)) = 1 - 1 / (d : ℝ) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [diagonal_completion hd]
  have hmass : (∑ z : Option (Fin d × Fin d),
      (match z with | none => (0 : ℝ) | some _ => 1 / (d : ℝ)^2)) = 1 := by
    simp [Fintype.sum_option, Fintype.sum_prod_type]
    field_simp
  rw [tv_overlap _ _ (diagonal_probability hd).2 hmass]
  congr 1
  have hcmp : 1 / (d : ℝ)^2 ≤ 1 / (d : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hdR) hdR).mpr
    nlinarith
  have hmin (x y : Fin d) : min (if x = y then 1 / (d : ℝ) else 0)
      (1 / (d : ℝ)^2) = if x = y then 1 / (d : ℝ)^2 else 0 := by
    by_cases h : x = y
    · simp only [if_pos h]
      exact min_eq_right hcmp
    · simp only [if_neg h]
      exact min_eq_left (by positivity)
  simp only [Fintype.sum_option, Fintype.sum_prod_type, diagonalLaw, min_self, zero_add]
  simp_rw [hmin]
  simp
  field_simp

private theorem tv_sum_le {I X : Type*} [Fintype I] [Fintype X]
    (f g : I → X → ℝ) :
    totalVariation (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤
      ∑ i, totalVariation (f i) (g i) := by
  simp only [totalVariation, ← Finset.sum_sub_distrib]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ x, ∑ i, |f i x - g i x| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by rw [Finset.sum_comm, Finset.mul_sum]

private theorem kernel_mixture {d : ℕ}
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ) :
    kernelOutput K (diagonalLaw d) =
      fun z => (1 / (d : ℝ)) * ∑ i : Fin d, K z (some (i,i)) := by
  classical
  funext z
  simp [kernelOutput, diagonalLaw, Fintype.sum_option, Fintype.sum_prod_type,
    mul_ite, ← Finset.sum_mul, Finset.mul_sum, mul_comm]

/-- Every fixed linear kernel has a uniform approximation error at least
(d-1)/(2d). Stochasticity is unnecessary for this obstruction. -/
theorem uniform_kernel_lower_bound {d : ℕ} (hd : 2 ≤ d)
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ) (e : ℝ)
    (he : ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput K p) (completion p) ≤ e) :
    ((d : ℝ) - 1) / (2 * d) ≤ e := by
  classical
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdet (i : Fin d) : totalVariation (fun z => K z (some (i,i)))
      (Pi.single (some (i,i)) 1) ≤ e := by
    have h := he (Pi.single (some (i,i)) 1)
      (fun z => by simp [Pi.single_apply]; positivity) (by simp)
    rw [completion_point] at h
    have hout : kernelOutput K (Pi.single (some (i,i)) 1) =
        fun z => K z (some (i,i)) := by
      funext z
      simp [kernelOutput, Pi.single_apply, mul_ite]
    rw [hout] at h
    exact h
  have hdiag : diagonalLaw d = fun z => (1 / (d : ℝ)) *
      ∑ i : Fin d, (Pi.single (some (i,i)) 1 : Option (Fin d × Fin d) → ℝ) z := by
    funext z
    cases z with
    | none => simp [diagonalLaw]
    | some z =>
      rcases z with ⟨x,y⟩
      by_cases h : x = y
      · subst y; simp [diagonalLaw, Pi.single_apply]
      · simp [diagonalLaw, Pi.single_apply, Prod.mk.injEq, h, Ne.symm h]
  have hmix : totalVariation (kernelOutput K (diagonalLaw d)) (diagonalLaw d) ≤ e := by
    rw [kernel_mixture, hdiag, tv_scale _ (by positivity)]
    calc
      _ ≤ (1 / (d : ℝ)) * ∑ i : Fin d,
          totalVariation (fun z => K z (some (i,i))) (Pi.single (some (i,i)) 1) :=
        mul_le_mul_of_nonneg_left (tv_sum_le _ _) (by positivity)
      _ ≤ (1 / (d : ℝ)) * ∑ _i : Fin d, e :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hdet i) (by positivity)
      _ = e := by simp [hdR.ne']
  have htest := he (diagonalLaw d) (diagonal_probability hd0).1 (diagonal_probability hd0).2
  have htri := total_variation_triangle (diagonalLaw d)
    (kernelOutput K (diagonalLaw d)) (completion (diagonalLaw d))
  rw [diagonal_gap hd0, total_variation_comm (diagonalLaw d) (kernelOutput K (diagonalLaw d))] at htri
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
  have h := (mul_le_mul_iff_right₀ hdR).mpr (show 1 - 1 / (d : ℝ) ≤ 2 * e by linarith)
  field_simp at h
  nlinarith only [h]

#print axioms uniform_kernel_lower_bound


private theorem rho_le_one {d : ℕ} (hd : 2 ≤ d) : rho d ≤ 1 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb := (le_div_iff₀ (by linarith : (0 : ℝ) < d)).mp (beta_le_inv hd)
  have hb0 := beta_nonneg d
  dsimp [rho]
  nlinarith only [hb, hb0]

private theorem rho_approach {d k : ℕ} (hk : 2 ≤ k) (hd : k * k ≤ d) :
    1 - 2 / (k : ℝ) ≤ rho d := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkd : k ≤ d := by nlinarith
  have hdR : (k : ℝ) * k ≤ d := by exact_mod_cast hd
  have hd2 : (2 : ℝ) ≤ d := by nlinarith only [hdR, hkR]
  have ht : (0 : ℝ) < (d : ℝ) + k - 2 := by linarith
  have hden : (0 : ℝ) < (k : ℝ) * ((d : ℝ) + k - 2) := mul_pos hk0 ht
  have hb : (k : ℝ) - 1 ≤ beta d * ((k : ℝ) * ((d : ℝ) + k - 2)) :=
    (div_le_iff₀ hden).mp (coefficient_le_beta hkd)
  have hm := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ d - 1)
  have hpoly : ((k : ℝ) - 2) * ((d : ℝ) + k - 2) ≤ ((d : ℝ) - 1) * (k - 1) := by
    nlinarith only [hdR, hkR]
  have hmul : (k : ℝ) - 2 ≤ ((d : ℝ) - 1) * beta d * k := by
    apply (mul_le_mul_iff_right₀ ht).mp
    nlinarith only [hm, hpoly]
  have hdiv := (div_le_iff₀ hk0).mpr hmul
  dsimp [rho]
  calc
    1 - 2 / (k : ℝ) = ((k : ℝ) - 2) / k := by field_simp <;> ring
    _ ≤ _ := hdiv

/-- The sharp candidate radii approach one over unbounded finite dimensions. -/
theorem rho_tendsto_one : Filter.Tendsto rho Filter.atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (max 2 (2 / ε))
  have hk2 : 2 ≤ k := by have := (le_max_left (2 : ℝ) (2 / ε)).trans hk.le; exact_mod_cast this
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2) ((le_max_left _ _).trans_lt hk)
  have hfrac : 2 / (k : ℝ) < ε := by
    apply (div_lt_iff₀ hk0).mpr
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hk)
    nlinarith only [hh]
  refine ⟨k*k, fun d hd => ?_⟩
  have hd2 : 2 ≤ d := by nlinarith
  have hupper := rho_le_one hd2
  have hlower := rho_approach hk2 hd
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith only [hlower, hfrac]

#print axioms rho_tendsto_one

end D5.S3.TotalVariation.RandomKernelExtremum
