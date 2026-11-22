/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/SignedOmittedSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/SignedOmittedSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Möbius cancellation in the low-frequency omitted root response. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.OmittedSpectrumCutoff

/-! Finite Abel summation over the omitted degrees of the actual root expansion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Finset Real Complex ArithmeticFunction
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open scoped ArithmeticFunction.Moebius

/-- A frequency cutoff separates signed degree cancellation from the high-frequency tail. -/
theorem signed_omitted_root_density_of_cutoff (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ m H : ℕ, 2 ≤ m → 0 < H →
      ∀ u : ℝ, (m : ℝ)+1 ≤ u → ∀ A : ℝ,
      (∀ k ≤ m+1, |∑ n ∈ Finset.range k, (μ n : ℝ)| ≤ A) →
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        Real.exp (-(orderRate m)*u) *
          (C * (A * ((H : ℝ)+1)^(1/4 : ℝ) * (1+((H : ℝ)+1)*(u/((m : ℝ)+1))) +
            ((m : ℝ)+1)*(H : ℝ)^(-1/4 : ℝ))) :=
  signed_omitted_root_density_of_varying_cutoff hRH

private theorem cutoff_power_budget {q u : ℝ} (hq : 1 ≤ q) (hu₀ : 0 ≤ u)
    (hu : u ≤ q^(29/28 : ℝ)) :
    let H := ⌊q^(1/7 : ℝ)⌋₊
    0 < H ∧
      q^(3/4 : ℝ) * ((H : ℝ)+1)^(1/4 : ℝ) * (1+((H : ℝ)+1)*(u/q)) ≤
        6*q^(27/28 : ℝ) ∧
      q*(H : ℝ)^(-1/4 : ℝ) ≤ 2*q^(27/28 : ℝ) := by
  let Y := q^(1/7 : ℝ)
  let H := ⌊Y⌋₊
  have hq₀ := zero_lt_one.trans_le hq
  have hY : 1 ≤ Y := Real.one_le_rpow hq (by norm_num)
  have hH₁ : 1 ≤ H := (Nat.le_floor_iff (zero_le_one.trans hY)).2 (by simpa using hY)
  have hH₀ : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hH₁
  have hHle : (H : ℝ) ≤ Y := Nat.floor_le (zero_le_one.trans hY)
  have hYle : Y < (H : ℝ)+1 := Nat.lt_floor_add_one _
  have hYupper : Y ≤ 2*(H : ℝ) := by linarith
  have hHupper : (H : ℝ)+1 ≤ 2*Y := by linarith
  have htwo : (2 : ℝ)^(1/4 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1/4 : ℝ) ≤ 1)
  have hYpow : Y^(1/4 : ℝ) = q^(1/28 : ℝ) := by
    dsimp [Y]
    rw [← Real.rpow_mul hq₀.le]
    norm_num
  have habove : ((H : ℝ)+1)^(1/4 : ℝ) ≤ 2*q^(1/28 : ℝ) := by
    refine (Real.rpow_le_rpow (by positivity) hHupper (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hY), hYpow]
    exact mul_le_mul_of_nonneg_right htwo (by positivity)
  have hbelow : q^(1/28 : ℝ) ≤ 2*(H : ℝ)^(1/4 : ℝ) := by
    rw [← hYpow]
    refine (Real.rpow_le_rpow (zero_le_one.trans hY) hYupper (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) hH₀.le]
    exact mul_le_mul_of_nonneg_right htwo (by positivity)
  have hratio : u/q ≤ q^(1/28 : ℝ) := by
    apply (div_le_iff₀ hq₀).2
    refine hu.trans_eq ?_
    calc
      _ = q^(1/28 : ℝ)*q^(1 : ℝ) := by rw [← Real.rpow_add hq₀]; norm_num
      _ = _ := by rw [Real.rpow_one]
  have hprod : ((H : ℝ)+1)*(u/q) ≤ 2*q^(5/28 : ℝ) := by
    refine (mul_le_mul hHupper hratio (div_nonneg hu₀ hq₀.le) (by positivity)).trans_eq ?_
    dsimp [Y]
    rw [mul_assoc, ← Real.rpow_add hq₀]
    norm_num
  have hunit : 1 ≤ q^(5/28 : ℝ) := Real.one_le_rpow hq (by norm_num)
  have hsum : 1+((H : ℝ)+1)*(u/q) ≤ 3*q^(5/28 : ℝ) := by linarith
  refine ⟨hH₁, ?_, ?_⟩
  · refine (mul_le_mul (mul_le_mul_of_nonneg_left habove (by positivity)) hsum
      (by positivity) (by positivity)).trans_eq ?_
    calc
      _ = 6*(q^(3/4 : ℝ)*q^(1/28 : ℝ)*q^(5/28 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hq₀, ← Real.rpow_add hq₀]; norm_num
  · have hnegative : (H : ℝ)^(-1/4 : ℝ) ≤ 2*q^(-1/28 : ℝ) := by
      rw [show (-1/4 : ℝ) = -(1/4) by ring, show (-1/28 : ℝ) = -(1/28) by ring,
        Real.rpow_neg hH₀.le, Real.rpow_neg hq₀.le]
      simp only [← one_div, mul_one_div]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa only [one_mul] using hbelow)
    refine (mul_le_mul_of_nonneg_left hnegative hq₀.le).trans_eq ?_
    calc
      _ = 2*(q^(1 : ℝ)*q^(-1/28 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hq₀]; norm_num

private theorem far_power_budget {q u : ℝ} (hq : 1 ≤ q) (hu : q^(29/28 : ℝ) ≤ u) :
    1+q^2/u+q^(7/8 : ℝ) ≤ 3*q^(27/28 : ℝ) := by
  have hq₀ := zero_lt_one.trans_le hq
  have hu₀ := (Real.rpow_pos_of_pos hq₀ (29/28 : ℝ)).trans_le hu
  have hratio : q^2/u ≤ q^(27/28 : ℝ) := by
    apply (div_le_iff₀ hu₀).2
    calc
      _ = q^(27/28 : ℝ)*q^(29/28 : ℝ) := by
        rw [← Real.rpow_add hq₀, show (27/28 : ℝ)+29/28 = 2 by norm_num]
        exact (Real.rpow_natCast q 2).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hq₀.le _)
  have hp : q^(7/8 : ℝ) ≤ q^(27/28 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
  linarith [Real.one_le_rpow hq (by norm_num : (0 : ℝ) ≤ 27/28)]

/-- Under RH and a three-quarter power bound for Möbius prefixes, the signed omitted root
density has power-saving dependence on the truncation order. -/
theorem signed_omitted_root_density_power (hRH : RiemannHypothesis) {D : ℝ}
    (hprefix : ∀ m : ℕ, 2 ≤ m → ∀ k ≤ m+1,
      |∑ n ∈ Finset.range k, (μ n : ℝ)| ≤ D*(((m : ℝ)+1)^(3/4 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, (m : ℝ)+1 ≤ u →
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ)*rootDensity n u| ≤
        C * (((m : ℝ)+1)^(27/28 : ℝ)) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨F, hF, hsplit⟩ := signed_omitted_root_density_of_cutoff hRH
  obtain ⟨G, hG, hfar⟩ := omitted_root_density_spacing hRH
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans
      (hprefix 2 le_rfl 0 (by omega))) (by positivity)
  refine ⟨max (F*(6*D+2)) (3*G), (show 0 < 3*G by positivity).trans_le (le_max_right _ _), ?_⟩
  intro m hm u hu
  let q := (m : ℝ)+1
  let T := (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n)
  let W := Real.exp (-(orderRate m)*u)
  have hq : 1 ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hqP : 0 ≤ q^(27/28 : ℝ) := by positivity
  by_cases hlarge : q^(29/28 : ℝ) ≤ u
  · have habs : |∑ n ∈ T, -(μ n : ℝ)*rootDensity n u| ≤
        ∑ n ∈ T, |rootDensity n u| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (by exact_mod_cast abs_moebius_le_one (n := n))
    refine (habs.trans (hfar m hm u hu)).trans ?_
    calc
      _ ≤ W * (G*(3*q^(27/28 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (far_power_budget hq hlarge) hG.le) hW
      _ = (3*G)*q^(27/28 : ℝ)*W := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hqP) hW
  · let H := ⌊q^(1/7 : ℝ)⌋₊
    let A := D*q^(3/4 : ℝ)
    obtain ⟨hH, hlow, hhigh⟩ :=
      cutoff_power_budget hq ((zero_le_one.trans hq).trans hu) (le_of_not_ge hlarge)
    have hs := hsplit m H hm hH u hu A (hprefix m hm)
    refine hs.trans ?_
    have hl : A*((H : ℝ)+1)^(1/4 : ℝ)*(1+((H : ℝ)+1)*(u/q)) ≤
        D*(6*q^(27/28 : ℝ)) := by
      dsimp only [A]
      rw [mul_assoc D, mul_assoc D]
      exact mul_le_mul_of_nonneg_left hlow hD
    calc
      _ ≤ W * (F*(D*(6*q^(27/28 : ℝ))+2*q^(27/28 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hl hhigh) hF.le) hW
      _ = (F*(6*D+2))*q^(27/28 : ℝ)*W := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hqP) hW

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
