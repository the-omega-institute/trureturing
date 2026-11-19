/- GID: D5/S3/Weil/Mertens/MobiusDyadicShellLower
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/MobiusDyadicShellLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Each right-half nontrivial zeta zero forces arbitrarily late signed Möbius shells at its exact energy scale. -/

import D5.S3.Weil.Mertens.MobiusDyadicEnergy
import D5.S3.Weil.ZeroSum
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual zeta zeros force arbitrarily late shells at their exact geometric scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.MobiusDyadicShellLower

open Filter MeasureTheory
open scoped BigOperators Topology
open D5.S3.Weil.Mertens.MobiusDyadicEnergy
  (K mobiusDyadicShellEnergy signed_dyadic_eventual_prefix_lower_bound)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

/-- Each actual zero in the closed right half of the open critical strip forces
arbitrarily late signed Möbius shells at its exact geometric energy scale. -/
theorem exists_mobiusDyadicShellEnergy_ge_of_zero {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hh : (1 / 2 : ℝ) ≤ ρ.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ k : ℕ, M ≤ k ∧
      c * ((2 : ℝ) ^ (2 * ρ.re - 1)) ^ k ≤ mobiusDyadicShellEnergy k := by
  obtain ⟨rate, hrate, N₀, hprefix⟩ :=
    signed_dyadic_eventual_prefix_lower_bound hh hρ.2.2
      (show riemannZeta ρ = 0 from hρ.1)
  let γ : ℝ := 2 * ρ.re - 1
  let q : ℝ := (2 : ℝ) ^ γ
  change ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ k : ℕ, M ≤ k ∧
    c * q ^ k ≤ mobiusDyadicShellEnergy k
  have hγ : 0 ≤ γ := by
    dsimp only [γ]
    linarith only [hh]
  have hq : 1 ≤ q := Real.one_le_rpow (by norm_num) hγ
  have hgeom_one (N : ℕ) : (∑ k ∈ Finset.range N, (1 : ℝ) ^ k) = (N : ℝ) := by
    simp
  obtain ⟨scale, hscale, hkernel⟩ :
      ∃ scale : ℝ, 0 < scale ∧ ∀ N : ℕ,
        K ρ.re ((N : ℝ) * Real.log 2) = scale * (∑ k ∈ Finset.range N, q ^ k) := by
    rcases eq_or_lt_of_le hγ with hzero | hpos
    · have hq_one : q = 1 := by
        change (2 : ℝ) ^ γ = 1
        rw [← hzero, Real.rpow_zero]
      have hlinear (U : ℝ) : K ρ.re U = U := by
        change (∫ t in (0 : ℝ)..U, Real.exp (γ * t)) = U
        simp only [← hzero, zero_mul, Real.exp_zero, intervalIntegral.integral_const,
          sub_zero, smul_eq_mul, mul_one]
      refine ⟨Real.log 2, Real.log_pos (by norm_num), fun N => ?_⟩
      rw [hlinear, hq_one, hgeom_one, mul_comm]
    · have hq_gt : 1 < q := Real.one_lt_rpow (by norm_num) hpos
      have hexp (U : ℝ) : K ρ.re U = (Real.exp (γ * U) - 1) / γ := by
        change (∫ t in (0 : ℝ)..U, Real.exp (γ * t)) = _
        rw [intervalIntegral.integral_comp_mul_left Real.exp hpos.ne', mul_zero,
          integral_exp, Real.exp_zero, smul_eq_mul, div_eq_mul_inv, mul_comm γ⁻¹]
      have hpower (N : ℕ) : q ^ N = Real.exp (γ * ((N : ℝ) * Real.log 2)) := by
        dsimp only [q]
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
        congr 1
        ring
      refine ⟨(q - 1) / γ, div_pos (sub_pos.mpr hq_gt) hpos, fun N => ?_⟩
      rw [hexp, ← hpower N, ← geom_sum_mul q N]
      ring
  let c : ℝ := rate * scale / 2
  have hc : 0 < c := half_pos (mul_pos hrate hscale)
  have hrate_scale : rate * scale = c + c := by
    dsimp only [c]
    ring
  refine ⟨c, hc, ?_⟩
  intro M
  by_contra hnone
  have htail (k : ℕ) (hk : M ≤ k) :
      mobiusDyadicShellEnergy k ≤ c * q ^ k :=
    le_of_not_ge (fun hlarge => hnone ⟨k, hk, hlarge⟩)
  let head : ℝ := ∑ k ∈ Finset.range M, mobiusDyadicShellEnergy k
  have hupper (N : ℕ) (hMN : M ≤ N) :
      (∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) ≤
        head + c * (∑ k ∈ Finset.range N, q ^ k) := by
    rw [← Finset.sum_range_add_sum_Ico mobiusDyadicShellEnergy hMN, Finset.mul_sum]
    have hsum :
        (∑ k ∈ Finset.Ico M N, mobiusDyadicShellEnergy k) ≤
          ∑ k ∈ Finset.range N, c * q ^ k := by
      calc
        _ ≤ ∑ k ∈ Finset.Ico M N, c * q ^ k :=
          Finset.sum_le_sum (fun k hk => htail k (Finset.mem_Ico.mp hk).1)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2)
          (fun k _ _ => mul_nonneg hc.le (pow_nonneg (zero_le_one.trans hq) k))
    exact add_le_add_right hsum head
  have hgap : ∀ᶠ N : ℕ in atTop, head < c * (∑ k ∈ Finset.range N, q ^ k) := by
    rcases eq_or_lt_of_le hq with hq_one | hq_gt
    · have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      filter_upwards [(hN.const_mul_atTop hc).eventually_gt_atTop head] with N hlarge
      rw [← hq_one, hgeom_one]
      exact hlarge
    · let d : ℝ := c / (q - 1)
      have hd : 0 < d := div_pos hc (sub_pos.mpr hq_gt)
      have hsmall : ∀ᶠ N : ℕ in atTop, (head + d) / q ^ N < d :=
        ((tendsto_pow_atTop_atTop_of_one_lt hq_gt).const_div_atTop (head + d)).eventually
          (gt_mem_nhds hd)
      filter_upwards [hsmall] with N hN
      have hpow : 0 < q ^ N := pow_pos (zero_lt_one.trans hq_gt) N
      have hhead : head + d < d * q ^ N := (div_lt_iff₀ hpow).mp hN
      rw [geom_sum_eq hq_gt.ne' N]
      calc
        head < d * q ^ N - d := lt_sub_iff_add_lt.mpr hhead
        _ = c * ((q ^ N - 1) / (q - 1)) := by
          dsimp only [d]
          ring
  obtain ⟨N, hN₀, hMN, hhead⟩ :=
    ((eventually_ge_atTop N₀).and ((eventually_ge_atTop M).and hgap)).exists
  have hlower := hprefix N hN₀
  rw [hkernel N, ← mul_assoc, hrate_scale, add_mul] at hlower
  exact (not_le_of_gt (add_lt_add_left hhead _)) (hlower.trans (hupper N hMN))

end D5.S3.Weil.Mertens.MobiusDyadicShellLower
