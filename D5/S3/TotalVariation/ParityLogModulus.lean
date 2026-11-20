/- GID: D5/S3/TotalVariation/ParityLogModulus
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityLogModulus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaging nontrivial sign moments gives a logarithmic total-variation modulus. -/

import D5.S3.TotalVariation.ParityLogStability
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite-distance stability of logarithmic parity coefficients. -/

set_option autoImplicit false
open scoped BigOperators
open D5.S3.TotalVariation.Pinsker (totalVariation)
namespace D5.S3.TotalVariation.ParityLogModulus

open D5.S3.TotalVariation.ParityLogStability

private theorem log_abs_difference_le {e x y : ℝ}
    (he : 0 < e) (hx : e ≤ |x|) (hy : e ≤ |y|) :
    |Real.log (|x|) - Real.log (|y|)| ≤ Real.log (1 + |x - y| / e) := by
  have ordered {u v : ℝ} (hu : e ≤ |u|) (huv : |u| ≤ |v|) :
      Real.log |v| - Real.log |u| ≤ Real.log (1 + |v - u| / e) := by
    have hu₀ := he.trans_le hu
    have hv₀ := hu₀.trans_le huv
    rw [← Real.log_div hv₀.ne' hu₀.ne']
    apply Real.log_le_log (div_pos hv₀ hu₀)
    rw [show |v| / |u| = 1 + (|v| - |u|) / |u| by field_simp; ring]
    apply add_le_add_right
    exact (div_le_div_of_nonneg_left (sub_nonneg.mpr huv) he hu).trans
      (div_le_div_of_nonneg_right
        ((le_abs_self _).trans (abs_abs_sub_abs_le_abs_sub v u)) he.le)
  rcases le_total (|x|) (|y|) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn
      (he.trans_le hx) (he.trans_le hy) h)), neg_sub, abs_sub_comm]
    exact ordered hx h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
      (he.trans_le hy) (he.trans_le hx) h))]
    exact ordered hy h

private theorem moment_distance_sum_le {A : Type*} [AddCommGroup A] [Fintype A]
    (two : ∀ x : A, x + x = 0) (p q : A → ℝ) (hmass : ∑ x, p x = ∑ x, q x) :
    (∑ ψ : AddChar A ℂ, |moment p ψ - moment q ψ|) ≤
      (Fintype.card A : ℝ) * totalVariation p q := by
  classical
  let s (ψ : AddChar A ℂ) : ℝ := if 0 ≤ moment p ψ - moment q ψ then 1 else -1
  let k (x : A) := ∑ ψ : AddChar A ℂ, s ψ * sign ψ x
  have hsgn (ψ : AddChar A ℂ) : |s ψ| = 1 := by
    dsimp [s]
    split <;> norm_num
  have hsplit (ψ : AddChar A ℂ) :
      |moment p ψ - moment q ψ| = s ψ * (moment p ψ - moment q ψ) := by
    dsimp [s]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_nonpos (le_of_not_ge h), neg_one_mul]
  have hdifference (ψ : AddChar A ℂ) :
      moment p ψ - moment q ψ = ∑ x, (p x - q x) * sign ψ x := by
    simp only [moment, sub_mul, Finset.sum_sub_distrib]
  have hosc (x y : A) : |k x - k y| ≤ (Fintype.card A : ℝ) := by
    dsimp [k]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ ψ : AddChar A ℂ, |s ψ * sign ψ x - s ψ * sign ψ y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ψ : AddChar A ℂ, |sign ψ x - sign ψ y| := by
        apply Finset.sum_congr rfl
        intro ψ _
        rw [← mul_sub, abs_mul, hsgn, one_mul]
      _ ≤ _ := sign_difference_sum two x y
  have hidentity :
      (∑ ψ : AddChar A ℂ, |moment p ψ - moment q ψ|) =
        ∑ x, (p x - q x) * k x := by
    simp_rw [hsplit, hdifference, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [k]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    ring
  rw [hidentity]
  exact (le_abs_self _).trans (abs_expectation_le_oscillation p q k hmass _ hosc)

/-- Keeping only nontrivial characters in Jensen's inequality improves the
linear stability bound to a logarithmic modulus at positive distance. -/
theorem log_parity_coefficient_modulus {A : Type*} [AddCommGroup A] [Fintype A]
    (two : ∀ x : A, x + x = 0) (hcard : 1 < Fintype.card A)
    (p q : A → ℝ) (hmass : ∑ x, p x = ∑ x, q x) (a : A) (e : ℝ) (he : 0 < e)
    (hp : ∀ ψ, e ≤ |moment p ψ|) (hq : ∀ ψ, e ≤ |moment q ψ|) :
    let beta : ℝ := ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ)
    |logCoefficient a p - logCoefficient a q| ≤
      2 * beta * Real.log (1 + totalVariation p q / (beta * e)) := by
  classical
  let n : ℝ := Fintype.card A
  let t := (Finset.univ : Finset (AddChar A ℂ)).erase 0
  let d (ψ : AddChar A ℂ) := |moment p ψ - moment q ψ|
  let z (ψ : AddChar A ℂ) := 1 + d ψ / e
  let f (ψ : AddChar A ℂ) := sign ψ a *
    (Real.log |moment p ψ| - Real.log |moment q ψ|)
  have hn₁ : 1 < n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn : 0 < n := by linarith
  have hdenom : 0 < n - 1 := sub_pos.mpr hn₁
  have ht : (t.card : ℝ) = n - 1 := by
    dsimp [t, n]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq,
      Nat.cast_sub (Nat.le_of_lt hcard)]
    norm_num
  have hzero : moment p (0 : AddChar A ℂ) = moment q (0 : AddChar A ℂ) := by
    simpa [moment, sign] using hmass
  have hd_total : ∑ ψ ∈ t, d ψ ≤ n * totalVariation p q := by
    have h := Finset.sum_erase_add Finset.univ d (Finset.mem_univ (0 : AddChar A ℂ))
    change (∑ ψ ∈ t, d ψ) + d 0 = _ at h
    rw [show d 0 = 0 by simp [d, hzero], add_zero] at h
    rw [h]
    exact moment_distance_sum_le two p q hmass
  have hsum_w : ∑ _ψ ∈ t, (n - 1)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ht, mul_inv_cancel₀ hdenom.ne']
  have hz (ψ : AddChar A ℂ) : 0 < z ψ :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (abs_nonneg _) he.le)
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := t) (w := fun _ => (n - 1)⁻¹) (p := z)
    (fun _ _ => inv_nonneg.mpr hdenom.le) hsum_w (fun ψ _ => hz ψ)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hmean : (n - 1)⁻¹ * (∑ ψ ∈ t, z ψ) ≤
      1 + totalVariation p q / ((n - 1) / n * e) := by
    have hsum : (∑ ψ ∈ t, z ψ) = n - 1 + (∑ ψ ∈ t, d ψ) / e := by
      dsimp [z]
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, ht,
        mul_one]
    rw [hsum]
    calc
      _ ≤ (n - 1)⁻¹ * (n - 1 + n * totalVariation p q / e) := by
        gcongr
      _ = _ := by field_simp
  have hzavg : 0 < (n - 1)⁻¹ * (∑ ψ ∈ t, z ψ) := by
    apply mul_pos (inv_pos.mpr hdenom)
    have ht_real : 0 < (t.card : ℝ) := by rwa [ht]
    have ht₀ : 0 < t.card := by exact_mod_cast ht_real
    exact Finset.sum_pos (fun ψ _ => hz ψ) (Finset.card_pos.mp ht₀)
  have hlogs : (∑ ψ ∈ t, Real.log (z ψ)) ≤ (n - 1) *
      Real.log (1 + totalVariation p q / ((n - 1) / n * e)) := by
    apply (inv_mul_le_iff₀ hdenom).mp
    exact hj.trans (Real.log_le_log hzavg hmean)
  have hf0 : f 0 = 0 := by simp [f, hzero]
  have hfsum : ∑ ψ : AddChar A ℂ, f ψ = ∑ ψ ∈ t, f ψ := by
    have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : AddChar A ℂ))
    change (∑ ψ ∈ t, f ψ) + f 0 = _ at h
    simpa [hf0] using h.symm
  have hcoef : logCoefficient a p - logCoefficient a q =
      (-2 / n) * ∑ ψ : AddChar A ℂ, f ψ := by
    unfold logCoefficient
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp only [f, n, mul_sub]
  dsimp
  rw [hcoef, hfsum, abs_mul, abs_div, abs_of_pos hn, show |(-2 : ℝ)| = 2 by norm_num]
  change (2 / n) * |∑ ψ ∈ t, f ψ| ≤
    2 * ((n - 1) / n) * Real.log (1 + totalVariation p q / ((n - 1) / n * e))
  calc
    _ ≤ (2 / n) * (∑ ψ ∈ t, Real.log (z ψ)) := by
      gcongr
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro ψ _
      rw [show f ψ = _ by rfl, abs_mul, abs_sign two, one_mul]
      exact log_abs_difference_le he (hp ψ) (hq ψ)
    _ ≤ (2 / n) * ((n - 1) *
        Real.log (1 + totalVariation p q / ((n - 1) / n * e))) := by gcongr
    _ = _ := by ring

end D5.S3.TotalVariation.ParityLogModulus
