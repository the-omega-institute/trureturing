/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMarginalTails
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marginal Taylor remainder bounds on the compact refined BMV comparison box. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails

/-! Taylor bounds for the compact marginal and its first two derivatives. -/

open MeasureTheory Set

noncomputable section

namespace RefinedBMV.PositiveCenter

open SmallCorner
open DimThree (gaps gaps_cycle_all mem_gaps_iff_total word_counts_all)

private abbrev Gap := ℕ × ℕ × ℕ
private abbrev exponent (p : ℕ) (g : Gap) : ℝ := 3 * (g.2.2 : ℝ) / p - 1
private abbrev denominator (p : ℕ) : ℝ := ((gaps p).length : ℝ) * compactKappa p

private theorem normalization {p : ℕ} (hp : 0 < p) :
    compactKappa p = compositionMarginalVariance p / 2 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hN : ((gaps p).length : ℝ) ≠ 0 := by exact_mod_cast (word_counts_all p).2.1.ne'
  unfold compactKappa compositionMarginalVariance
  rw [(centered_marginal_sums hp).2]
  field_simp [hN, hpR]
  norm_num

private theorem exponent_abs_le {p : ℕ} (hp : 0 < p) {g : Gap} (hg : g ∈ gaps p) :
    |exponent p g| ≤ 2 := by
  have hsum := (mem_gaps_iff_total p g).mp hg
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hj : (g.2.2 : ℝ) ≤ p := by exact_mod_cast (show g.2.2 ≤ p by omega)
  have hl : (0 : ℝ) ≤ 3 * (g.2.2 : ℝ) / p := by positivity
  have hu : 3 * (g.2.2 : ℝ) / p ≤ 3 := (div_le_iff₀ hpR).2 (by linarith)
  exact abs_le.2 ⟨by dsimp only [exponent]; linarith, by dsimp only [exponent]; linarith⟩

private def scalarPolynomial (b t : ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, b ^ (k + i) * t ^ i /
    ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) * (((k + i : ℕ) : ℝ) + 2))

private theorem weighted_error {b t R : ℝ} (hb : |b| ≤ 2) (ht : |t| ≤ R)
    {k n : ℕ} (hn : 2 ≤ n) (hR : 2 * R / (n.succ : ℝ) < 1) :
    |(∫ s in (0 : ℝ)..1, (1 - s) * (b * s) ^ k * Real.exp (t * (b * s))) -
        scalarPolynomial b t k n| ≤
      ((2 : ℝ) ^ k * (2 * R) ^ n / (n.factorial : ℝ) / (1 - 2 * R / (n.succ : ℝ))) /
        (((n + k : ℕ) : ℝ) + 1) / (((n + k : ℕ) : ℝ) + 2) := by
  let w (s : ℝ) := (1 - s) * (b * s) ^ k
  let z (s : ℝ) := t * (b * s)
  let pol (s : ℝ) := ∑ i ∈ Finset.range n, z s ^ i / (i.factorial : ℝ)
  have hpol : (∫ s in (0 : ℝ)..1, w s * pol s) = scalarPolynomial b t k n := by
    simp only [pol, scalarPolynomial, Finset.mul_sum]
    refine (intervalIntegral.integral_finsetSum (fun i _ ↦ ?_)).trans ?_
    · apply Continuous.intervalIntegrable
      dsimp only [w, z]
      fun_prop
    apply Finset.sum_congr rfl
    intro i _
    have heq (s : ℝ) :
        w s * (z s ^ i / (i.factorial : ℝ)) =
          (b ^ (k + i) * t ^ i / (i.factorial : ℝ)) * ((1 - s) * s ^ (k + i)) := by
      simp only [w, z, mul_pow, pow_add]
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul, unit_weight_moment]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_assoc]
    ac_rfl
  have hv : Continuous (fun s ↦ w s * Real.exp (z s)) := by
    dsimp only [w, z]
    fun_prop
  have hP : Continuous (fun s ↦ w s * pol s) := by
    dsimp only [w, pol, z]
    fun_prop
  let C : ℝ := (2 : ℝ) ^ k * (2 * R) ^ n / n.factorial / (1 - 2 * R / (n.succ : ℝ))
  have hR₀ : 0 ≤ R := (abs_nonneg t).trans ht
  have hC : Continuous (fun s : ℝ ↦ C * ((1 - s) * s ^ (n + k))) := by fun_prop
  have hbound (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
      ‖w s * Real.exp (z s) - w s * pol s‖ ≤ C * ((1 - s) * s ^ (n + k)) := by
    have hs₀ : 0 ≤ s := hs.1.le
    have hbs : |b * s| ≤ 2 * s := by
      rw [abs_mul, abs_of_nonneg hs₀]
      exact mul_le_mul_of_nonneg_right hb hs₀
    have hz : |z s| ≤ 2 * R * s := by
      rw [show z s = t * (b * s) from rfl, abs_mul]
      calc
        _ ≤ R * (2 * s) := mul_le_mul ht hbs (abs_nonneg _) hR₀
        _ = _ := by ring
    have hratio : 2 * R * s / (n.succ : ℝ) ≤ 2 * R / (n.succ : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) hs.2) (by positivity)
    have htail := compactExp_sub_truncation_geometric_le hn hz (hratio.trans_lt hR)
    have htail' : |Real.exp (z s) - pol s| ≤
        (2 * R * s) ^ n / (n.factorial : ℝ) / (1 - 2 * R / (n.succ : ℝ)) :=
      htail.trans (div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hR)
        (sub_le_sub_left hratio 1))
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    dsimp only [w]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_pow, mul_assoc]
    calc
      _ ≤ (1 - s) * ((2 * s) ^ k *
          ((2 * R * s) ^ n / (n.factorial : ℝ) / (1 - 2 * R / (n.succ : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hbs _) htail' (abs_nonneg _)
            (pow_nonneg (mul_nonneg (by norm_num) hs₀) _))
          (sub_nonneg.mpr hs.2)
      _ = _ := by simp only [C, mul_pow, pow_add]; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one
    (Filter.Eventually.of_forall hbound) (hC.intervalIntegrable 0 1)
  change |(∫ s in (0 : ℝ)..1, w s * Real.exp (z s)) - scalarPolynomial b t k n| ≤ _
  rw [← hpol, ← intervalIntegral.integral_sub (μ := volume) (hv.intervalIntegrable 0 1)
    (hP.intervalIntegrable 0 1)]
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, unit_weight_moment] at h
  refine h.trans_eq ?_
  norm_num [C, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem list_sum_map_finsetSum {α ι : Type*} (l : List α) (s : Finset ι)
    (f : α → ι → ℝ) :
    (l.map fun g ↦ ∑ i ∈ s, f g i).sum = ∑ i ∈ s, (l.map fun g ↦ f g i).sum := by
  induction l with
  | nil => simp
  | cons g l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

private theorem marginal_power_sum_eq {p : ℕ} (hp : 0 < p) (n : ℕ) :
    ((gaps p).map fun g ↦ exponent p g ^ 2 * exponent p g ^ n).sum /
      denominator p = jointTaylorMoment p n 0 := by
  have h := ((gaps_cycle_all p).map fun g ↦
    (3 * (g.2.1 : ℝ) / p - 1) ^ 2 * (3 * (g.2.1 : ℝ) / p - 1) ^ n).sum_eq
  simp only [List.map_map, Function.comp_def] at h
  change _ = ((gaps p).map fun g ↦ (3 * (g.2.1 : ℝ) / p - 1) ^ 2 *
    ((3 * (g.2.1 : ℝ) / p - 1) ^ n * exponent p g ^ 0)).sum /
    ((gaps p).length * (compositionMarginalVariance p / 2))
  simp only [pow_zero, mul_one, denominator, normalization hp, exponent, h]

/- The derivatives share the same normalized moment row. -/
noncomputable def compactMarginalTaylorUpTo (p k n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, jointTaylorMoment p (k + i) 0 * t ^ i /
    ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) * (((k + i : ℕ) : ℝ) + 2))

private theorem marginalTaylorUpTo_eq_sum {p : ℕ} (hp : 0 < p) (k n : ℕ) (t : ℝ) :
    compactMarginalTaylorUpTo p k n t =
      ((gaps p).map fun g ↦ exponent p g ^ 2 *
        scalarPolynomial (exponent p g) t k n).sum / denominator p := by
  simp only [compactMarginalTaylorUpTo, scalarPolynomial, Finset.mul_sum,
    list_sum_map_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← marginal_power_sum_eq hp]
  simp_rw [show ∀ (x : ℝ), x ^ 2 *
      (x ^ (k + i) * t ^ i / ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) *
        (((k + i : ℕ) : ℝ) + 2))) =
      (x ^ 2 * x ^ (k + i)) * (t ^ i / ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) *
        (((k + i : ℕ) : ℝ) + 2))) by
    intro x
    ring]
  rw [List.sum_map_mul_right]
  ring

/-- Exact geometric Taylor error for the regularized marginal and its derivatives. -/
theorem iteratedDeriv_compactZ_sub_taylorUpTo_le {p k n : ℕ}
    (hp : 0 < p) (hn : 2 ≤ n) {t R : ℝ} (ht : |t| ≤ R) (hR : 2 * R / (n.succ : ℝ) < 1) :
    |iteratedDeriv k (compactZ p) t - compactMarginalTaylorUpTo p k n t| ≤
      ((2 : ℝ) ^ (k + 1) * (2 * R) ^ n / (n.factorial : ℝ) / (1 - 2 * R / (n.succ : ℝ))) /
        (((n + k : ℕ) : ℝ) + 1) / (((n + k : ℕ) : ℝ) + 2) := by
  let ε : ℝ := ((2 : ℝ) ^ k * (2 * R) ^ n / (n.factorial : ℝ) / (1 - 2 * R / (n.succ : ℝ))) /
    (((n + k : ℕ) : ℝ) + 1) / (((n + k : ℕ) : ℝ) + 2)
  rw [iteratedDeriv_compactZ_eq_integral hp, marginalTaylorUpTo_eq_sum hp]
  let f (g : Gap) := exponent p g ^ 2 *
    (∫ s in (0 : ℝ)..1, (1 - s) * (exponent p g * s) ^ k *
      Real.exp (t * (exponent p g * s)))
  let pol (g : Gap) := exponent p g ^ 2 * scalarPolynomial (exponent p g) t k n
  let weight (g : Gap) := exponent p g ^ 2 * ε
  change |((gaps p).map f).sum / denominator p - ((gaps p).map pol).sum / denominator p| ≤ _
  have hN : (0 : ℝ) < (gaps p).length := by exact_mod_cast (word_counts_all p).2.1
  have hden : 0 < denominator p := by
    rw [denominator, normalization hp]
    exact mul_pos hN (half_pos (compositionMarginalVariance_pos p))
  have hlocal (g : Gap) (hg : g ∈ gaps p) : |f g - pol g| ≤ weight g := by
    dsimp only [f, pol, weight]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (weighted_error (k := k) (exponent_abs_le hp hg) ht hn hR)
      (sq_nonneg _)
  have hsum (l : List Gap) (hl : ∀ g ∈ l, |f g - pol g| ≤ weight g) :
      |(l.map f).sum - (l.map pol).sum| ≤ (l.map weight).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [show f g + (l.map f).sum - (pol g + (l.map pol).sum) =
        (f g - pol g) + ((l.map f).sum - (l.map pol).sum) by ring]
      exact (abs_add_le _ _).trans (add_le_add (hl g (by simp))
        (ih fun j hj ↦ hl j (List.mem_cons_of_mem _ hj)))
  have hsquare : ((gaps p).map fun g ↦ exponent p g ^ 2).sum = 2 * denominator p := by
    dsimp only [exponent, denominator]
    rw [normalization hp, compositionMarginalVariance]
    field_simp [hN.ne']
  rw [← sub_div, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine (hsum (gaps p) hlocal).trans_eq ?_
  dsimp only [weight]
  rw [List.sum_map_mul_right, hsquare]
  simp only [ε, pow_succ]
  ring

/-- The degree-`22 - k` approximation on `[-2, 2]` also bounds the third derivative. -/
theorem iteratedDeriv_compactZ_sub_taylor_le_two_of_le_three {p k : ℕ}
    (hp : 0 < p) (hk : k ≤ 3) {t : ℝ} (ht : |t| ≤ 2) :
    |iteratedDeriv k (compactZ p) t - marginalTaylorPolynomial p k t| ≤
      (2 : ℝ) ^ (k + 2) * 4 ^ (23 - k) / ((Nat.factorial (23 - k) : ℝ) * 24 * 25) := by
  let n := 23 - k
  have hn : 20 ≤ n := by dsimp [n]; omega
  have hnR : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : (2 : ℝ) * 2 / (n.succ : ℝ) < 1 := by
    rw [Nat.cast_succ, div_lt_iff₀ (by positivity)]
    linarith
  have hden : (1 / 2 : ℝ) ≤ 1 - 2 * 2 / (n.succ : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 - 1 / 2 by norm_num]
    apply sub_le_sub_left
    rw [Nat.cast_succ, div_le_iff₀ (by positivity)]
    linarith
  have h := iteratedDeriv_compactZ_sub_taylorUpTo_le (k := k) hp (show 2 ≤ n by omega) ht hR
  have hsum : n + k = 23 := by dsimp [n]; omega
  rw [hsum] at h
  refine h.trans ?_
  norm_num at *
  calc
    _ ≤ ((2 : ℝ) ^ (k + 1) * 4 ^ n / (n.factorial : ℝ) / (1 / 2 : ℝ)) / 24 / 25 := by
      gcongr
    _ = _ := by rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]; dsimp [n]; ring

/-- Uniform Taylor error on `[-2, 2]` through the second derivative. -/
theorem iteratedDeriv_compactZ_sub_taylor_le_two {p k : ℕ} (hp : 0 < p) (hk : k ≤ 2)
    {t : ℝ} (ht : |t| ≤ 2) :
    |iteratedDeriv k (compactZ p) t - marginalTaylorPolynomial p k t| ≤
      (2 : ℝ) ^ (k + 2) * 4 ^ (23 - k) / ((Nat.factorial (23 - k) : ℝ) * 24 * 25) :=
  iteratedDeriv_compactZ_sub_taylor_le_two_of_le_three hp (hk.trans (by decide)) ht

#print axioms iteratedDeriv_compactZ_sub_taylor_le_two

end RefinedBMV.PositiveCenter
