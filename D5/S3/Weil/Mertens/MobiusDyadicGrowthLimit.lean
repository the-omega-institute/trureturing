/- GID: D5/S3/Weil/Mertens/MobiusDyadicGrowthLimit
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/MobiusDyadicGrowthLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cumulative limit and individual limsup for signed Möbius shell energies. -/

import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import D5.S3.Weil.Mertens.MobiusDyadicEnergy
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import D5.S3.Weil.ZetaPntBounds.MobiusDyadicEnergyUpper
import Mathlib.Algebra.Field.GeomSum
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Order.LiminfLimsup

/-! The cumulative logarithmic growth rate of the literal signed Möbius shell energies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
open D5.S3.Arith.MoebiusLogarithmic (reciprocalSum abs_reciprocalSum_le_one)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap
  (zeroAbscissa zero_real_parts_nonempty zero_re_le_abscissa)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
  (zetaZeroData zetaZeroData_isNontrivial zetaZeroData_reflection)
open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (mobiusPartialSum mobiusDyadicShellEnergy_normalized_tendsto_zero_of_zero_free)
open D5.S3.Weil.Mertens.MobiusDyadicEnergy
  (K mobiusDyadicDifference mobiusDyadicShellEnergy signed_dyadic_eventual_prefix_lower_bound)

private theorem half_le_zeroAbscissa : (1 / 2 : ℝ) ≤ zeroAbscissa := by
  have h := zero_re_le_abscissa (zetaZeroData_isNontrivial 0)
  have hr := zero_re_le_abscissa (zetaZeroData_isNontrivial (zetaZeroData.reflection 0))
  rw [zetaZeroData_reflection] at hr
  simp only [Complex.sub_re, Complex.one_re] at hr
  linarith only [h, hr]

private theorem zeroAbscissa_le_one : zeroAbscissa ≤ 1 := by
  apply csSup_le zero_real_parts_nonempty
  rintro r ⟨ρ, hρ, rfl⟩
  exact hρ.2.2.le

private theorem zero_free_right_of_zeroAbscissa (z : ℂ) (hz : zeroAbscissa < z.re)
    (_hz1 : z ≠ 1) : riemannZeta z ≠ 0 := by
  by_cases hline : 1 ≤ z.re
  · exact riemannZeta_ne_zero_of_one_le_re hline
  · intro hzero
    have hre : 0 < z.re := by linarith [half_le_zeroAbscissa]
    have hnt : IsNontrivialZero z := by
      exact ⟨hzero, hre, lt_of_not_ge hline⟩
    exact (not_lt_of_ge (zero_re_le_abscissa hnt)) hz

private theorem shellEnergy_nonneg (k : ℕ) : 0 ≤ mobiusDyadicShellEnergy k :=
  integral_nonneg (fun _ => sq_nonneg _)

private theorem shellEnergy_le_four_mul_pow (k : ℕ) :
    mobiusDyadicShellEnergy k ≤ 4 * (2 : ℝ) ^ k := by
  have hm (x : ℝ) : |mobiusPartialSum x| ≤ 1 := by
    have he : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    simpa only [mobiusPartialSum, reciprocalSum, he] using abs_reciprocalSum_le_one x
  let a : ℝ := (2 : ℝ) ^ k
  let b : ℝ := (2 : ℝ) ^ (k + 1)
  have hab : a ≤ b := pow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ k)
  have hlength : b - a = a := by
    dsimp [a, b]
    rw [pow_succ]
    ring
  have hfinite : (volume : Measure ℝ) (Ioc a b) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound : ‖∫ x in Ioc a b, mobiusDyadicDifference x ^ 2‖ ≤
      4 * (volume : Measure ℝ).real (Ioc a b) := by
    refine norm_setIntegral_le_of_norm_le_const_ae hfinite (Eventually.of_forall ?_)
    intro x
    have hd : |mobiusDyadicDifference x| ≤ 2 := by
      obtain ⟨h₁, h₂⟩ := abs_le.mp (hm x)
      obtain ⟨h₃, h₄⟩ := abs_le.mp (hm (2 * x))
      rw [mobiusDyadicDifference, abs_le]
      constructor <;> linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc
      _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
      _ = 4 := by norm_num
  rw [Real.volume_real_Ioc_of_le hab, hlength] at hbound
  exact (le_abs_self (mobiusDyadicShellEnergy k)).trans (by
    simpa only [Real.norm_eq_abs, mobiusDyadicShellEnergy, a, b] using hbound)

private theorem exists_shellEnergy_bound {α : ℝ} (hΘ : zeroAbscissa < 1)
    (hα : 2 * zeroAbscissa - 1 < α) (hα₁ : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      mobiusDyadicShellEnergy k ≤ C * ((2 : ℝ) ^ α) ^ k := by
  have hα₀ : 0 < α := by linarith [half_le_zeroAbscissa]
  have hnorm : Tendsto (fun k : ℕ => mobiusDyadicShellEnergy k / ((2 : ℝ) ^ α) ^ k)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) α] using
      (mobiusDyadicShellEnergy_normalized_tendsto_zero_of_zero_free
        (θ := zeroAbscissa) (α := α)
        half_le_zeroAbscissa hΘ zero_free_right_of_zeroAbscissa hα hα₁)
  have htail : ∀ᶠ k : ℕ in atTop, mobiusDyadicShellEnergy k / ((2 : ℝ) ^ α) ^ k < 1 :=
    hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨M, hM⟩ := eventually_atTop.1 htail
  let C : ℝ := 1 + ∑ k ∈ Finset.range M, mobiusDyadicShellEnergy k
  have hsum : 0 ≤ ∑ k ∈ Finset.range M, mobiusDyadicShellEnergy k :=
    Finset.sum_nonneg (fun k _ => shellEnergy_nonneg k)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, zero_le_one.trans hC, fun k => ?_⟩
  have hq : 1 ≤ ((2 : ℝ) ^ α) ^ k :=
    one_le_pow₀ (Real.one_le_rpow (by norm_num) hα₀.le)
  by_cases hk : M ≤ k
  · have hpos : 0 < ((2 : ℝ) ^ α) ^ k := zero_lt_one.trans_le hq
    have hle : mobiusDyadicShellEnergy k ≤ ((2 : ℝ) ^ α) ^ k := by
      simpa only [one_mul] using ((div_lt_iff₀ hpos).mp (hM k hk)).le
    exact hle.trans (le_mul_of_one_le_left hpos.le hC)
  · have hsingle : mobiusDyadicShellEnergy k ≤
        ∑ j ∈ Finset.range M, mobiusDyadicShellEnergy j :=
      Finset.single_le_sum (fun j _ => shellEnergy_nonneg j)
        (Finset.mem_range.mpr (lt_of_not_ge hk))
    have hkC : mobiusDyadicShellEnergy k ≤ C := by dsimp [C]; linarith
    exact hkC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hq)

private theorem tendsto_dyadicTime :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.log 2) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num))

private theorem tendsto_log_exponential_quotient {c : ℝ} (hc : 0 < c) (α : ℝ) :
    Tendsto (fun N : ℕ =>
      Real.log (c * Real.exp (α * ((N : ℝ) * Real.log 2))) / ((N : ℝ) * Real.log 2))
      atTop (𝓝 α) := by
  have hshift : Tendsto (fun N : ℕ => Real.log c / ((N : ℝ) * Real.log 2)) atTop (𝓝 0) :=
    tendsto_dyadicTime.const_div_atTop (Real.log c)
  have hlim : Tendsto (fun N : ℕ => Real.log c / ((N : ℝ) * Real.log 2) + α) atTop (𝓝 α) :=
    by simpa only [zero_add] using hshift.add_const α
  refine hlim.congr' ?_
  filter_upwards [tendsto_dyadicTime.eventually_gt_atTop (0 : ℝ)] with N hN
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp, add_div,
    mul_div_cancel_right₀ _ (ne_of_gt hN)]

private theorem eventually_growth_lt_of_shell_bound {α B C : ℝ}
    (hα : 0 < α) (hαB : α < B) (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, mobiusDyadicShellEnergy k ≤ C * ((2 : ℝ) ^ α) ^ k) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (1 + ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) /
        ((N : ℝ) * Real.log 2) < B := by
  let q : ℝ := (2 : ℝ) ^ α
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hα
  have hq₀ : 0 < q - 1 := sub_pos.mpr hq
  let M : ℝ := 1 + C / (q - 1)
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hC hq₀.le)
  have ht : ∀ᶠ N : ℕ in atTop,
      Real.log (M * Real.exp (α * ((N : ℝ) * Real.log 2))) / ((N : ℝ) * Real.log 2) < B :=
    (tendsto_log_exponential_quotient hM α).eventually (gt_mem_nhds hαB)
  filter_upwards [ht, tendsto_dyadicTime.eventually_gt_atTop (0 : ℝ)] with N hN htime
  have hgeom : (∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) ≤
      (C / (q - 1)) * q ^ N := by
    calc
      _ ≤ C * (∑ k ∈ Finset.range N, q ^ k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun k _ => hbound k)
      _ = C * ((q ^ N - 1) / (q - 1)) := by rw [geom_sum_eq hq.ne' N]
      _ ≤ C * (q ^ N / (q - 1)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hq₀.le) hC
      _ = _ := by ring
  have hpower : q ^ N = Real.exp (α * ((N : ℝ) * Real.log 2)) := by
    dsimp [q]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    congr 1
    ring
  have hprefix : 1 + (∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) ≤
      M * Real.exp (α * ((N : ℝ) * Real.log 2)) := by
    calc
      _ ≤ q ^ N + (C / (q - 1)) * q ^ N := add_le_add (one_le_pow₀ hq.le) hgeom
      _ = _ := by rw [← hpower]; dsimp [M]; ring
  have hpos : 0 < 1 + (∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun k _ => shellEnergy_nonneg k))
  exact (div_le_div_of_nonneg_right (Real.log_le_log hpos hprefix) htime.le).trans_lt hN

private theorem eventually_lt_growth_of_zero {ρ : ℂ} {A : ℝ} (hρ : IsNontrivialZero ρ)
    (hβ : (1 / 2 : ℝ) < ρ.re) (hA : A < 2 * ρ.re - 1) :
    ∀ᶠ N : ℕ in atTop, A <
      Real.log (1 + ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) /
        ((N : ℝ) * Real.log 2) := by
  let γ : ℝ := 2 * ρ.re - 1
  have hγ : 0 < γ := by dsimp [γ]; linarith
  obtain ⟨coefficient, hcoefficient, N₀, hprefix⟩ :=
    signed_dyadic_eventual_prefix_lower_bound hβ.le hρ.2.2
      (show riemannZeta ρ = 0 from hρ.1)
  let c : ℝ := coefficient / 2 / γ
  have hc₀ : 0 < c := div_pos (div_pos hcoefficient (by norm_num)) hγ
  have hK (U : ℝ) : K ρ.re U = (Real.exp (γ * U) - 1) / γ := by
    change (∫ t in (0 : ℝ)..U, Real.exp (γ * t)) = _
    rw [intervalIntegral.integral_comp_mul_left Real.exp hγ.ne', mul_zero,
      integral_exp, Real.exp_zero, smul_eq_mul, div_eq_mul_inv, mul_comm γ⁻¹]
  have hcutoff : ∀ᶠ N : ℕ in atTop, N₀ ≤ N := eventually_ge_atTop N₀
  have hlarge : ∀ᶠ N : ℕ in atTop, Real.log 2 / γ ≤ (N : ℝ) * Real.log 2 :=
    tendsto_dyadicTime.eventually_ge_atTop (Real.log 2 / γ)
  have ht : ∀ᶠ N : ℕ in atTop, A <
      Real.log (c * Real.exp (γ * ((N : ℝ) * Real.log 2))) / ((N : ℝ) * Real.log 2) :=
    (tendsto_log_exponential_quotient hc₀ γ).eventually (lt_mem_nhds hA)
  filter_upwards [ht, hcutoff, hlarge, tendsto_dyadicTime.eventually_gt_atTop (0 : ℝ)]
    with N hN hcut hU htime
  let U : ℝ := (N : ℝ) * Real.log 2
  have hexp : (2 : ℝ) ≤ Real.exp (γ * U) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
    rw [mul_comm γ U]
    exact (div_le_iff₀ hγ).mp hU
  have hbound : coefficient * K ρ.re U ≤ ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k :=
    hprefix N hcut
  rw [hK] at hbound
  have hlower : c * Real.exp (γ * U) ≤
      1 + (∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) := by
    calc
      _ = coefficient * ((Real.exp (γ * U) / 2) / γ) := by
        dsimp only [c]
        ring
      _ ≤ coefficient * ((Real.exp (γ * U) - 1) / γ) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith) hγ.le) hcoefficient.le
      _ ≤ _ := hbound.trans (le_add_of_nonneg_left zero_le_one)
  exact hN.trans_le (div_le_div_of_nonneg_right
    (Real.log_le_log (mul_pos hc₀ (Real.exp_pos _)) hlower) htime.le)

/-- The exact cumulative exponential growth exponent of the literal signed Möbius shells. -/
theorem tendsto_log_one_add_sum_mobiusDyadicShellEnergy :
    Tendsto (fun N : ℕ =>
      Real.log (1 + ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) /
        ((N : ℝ) * Real.log 2)) atTop (𝓝 (2 * zeroAbscissa - 1)) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro A hA
    by_cases hA₀ : A < 0
    · apply Eventually.of_forall
      intro N
      have hsum : 0 ≤ ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k :=
        Finset.sum_nonneg (fun k _ => shellEnergy_nonneg k)
      exact hA₀.trans_le (div_nonneg (Real.log_nonneg (le_add_of_nonneg_right hsum))
        (mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg (by norm_num))))
    · have hab : (A + 1) / 2 < zeroAbscissa := by linarith
      obtain ⟨r, ⟨ρ, hρ, rfl⟩, hβ⟩ := exists_lt_of_lt_csSup zero_real_parts_nonempty hab
      have hnonneg : 0 ≤ A := le_of_not_gt hA₀
      exact eventually_lt_growth_of_zero hρ (by linarith only [hβ, hnonneg]) (by linarith only [hβ])
  · intro B hB
    rcases lt_or_eq_of_le zeroAbscissa_le_one with hΘ | hΘ
    · have hmin : 2 * zeroAbscissa - 1 < min 1 B := lt_min (by linarith) hB
      obtain ⟨α, hα, hαhi⟩ := exists_between hmin
      have hα₁ : α < 1 := hαhi.trans_le (min_le_left _ _)
      have hαB : α < B := hαhi.trans_le (min_le_right _ _)
      have hα₀ : 0 < α := by linarith [half_le_zeroAbscissa]
      obtain ⟨C, hC, hbound⟩ := exists_shellEnergy_bound hΘ hα hα₁
      exact eventually_growth_lt_of_shell_bound hα₀ hαB hC hbound
    · have hB₁ : (1 : ℝ) < B := by rw [hΘ] at hB; linarith
      exact eventually_growth_lt_of_shell_bound (α := 1) (C := 4) zero_lt_one hB₁
        (by norm_num) (fun k => by simpa only [Real.rpow_one] using shellEnergy_le_four_mul_pow k)

#print axioms tendsto_log_one_add_sum_mobiusDyadicShellEnergy

/-- The exact limsup of the logarithmic growth of the literal signed Möbius shells. -/
theorem limsup_log_one_add_mobiusDyadicShellEnergy :
    Filter.limsup (fun k : ℕ =>
      Real.log (1 + mobiusDyadicShellEnergy k) / ((k : ℝ) * Real.log 2)) Filter.atTop =
      2 * zeroAbscissa - 1 := by
  let L : ℝ := 2 * zeroAbscissa - 1
  let u : ℕ → ℝ := fun k =>
    Real.log (1 + mobiusDyadicShellEnergy k) / ((k : ℝ) * Real.log 2)
  let v : ℕ → ℝ := fun N =>
    Real.log (1 + ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) /
      ((N : ℝ) * Real.log 2)
  change Filter.limsup u atTop = L
  have hv : Tendsto v atTop (𝓝 L) := tendsto_log_one_add_sum_mobiusDyadicShellEnergy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu_nonneg (k : ℕ) : 0 ≤ u k :=
    div_nonneg (Real.log_nonneg (le_add_of_nonneg_right (shellEnergy_nonneg k)))
      (mul_nonneg (Nat.cast_nonneg k) hlog2.le)
  have hu_cobdd : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) u :=
    Filter.isCoboundedUnder_le_of_le atTop hu_nonneg

  -- The prefix through shell k, with the denominator taken at k.
  let w : ℕ → ℝ := fun k =>
    v (k + 1) * (1 + Real.log 2 / ((k : ℝ) * Real.log 2))
  have hw : Tendsto w atTop (𝓝 L) := by
    have hshift : Tendsto (fun k : ℕ => v (k + 1)) atTop (𝓝 L) :=
      (tendsto_add_atTop_iff_nat 1).2 hv
    have hscale : Tendsto (fun k : ℕ => 1 + Real.log 2 / ((k : ℝ) * Real.log 2))
        atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using
        (tendsto_dyadicTime.const_div_atTop (Real.log 2)).const_add (1 : ℝ)
    simpa only [w, mul_one] using hshift.mul hscale
  have huw : ∀ᶠ k : ℕ in atTop, u k ≤ w k := by
    filter_upwards [tendsto_dyadicTime.eventually_gt_atTop (0 : ℝ)] with k htime
    have hnext : 0 < ((k + 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_pos (Nat.cast_pos.mpr (Nat.succ_pos k)) hlog2
    have hscale :
        1 + Real.log 2 / ((k : ℝ) * Real.log 2) =
          (((k + 1 : ℕ) : ℝ) * Real.log 2) / ((k : ℝ) * Real.log 2) := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_div, div_self htime.ne']
    have hsingle : mobiusDyadicShellEnergy k ≤
        ∑ j ∈ Finset.range (k + 1), mobiusDyadicShellEnergy j :=
      Finset.single_le_sum (fun j _ => shellEnergy_nonneg j)
        (Finset.mem_range.mpr (Nat.lt_succ_self k))
    dsimp only [u, w, v]
    rw [hscale, div_mul_div_cancel₀ hnext.ne']
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one (shellEnergy_nonneg k))
        (add_le_add (le_refl (1 : ℝ)) hsingle)) htime.le
  have hw_bdd : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) w := hw.isBoundedUnder_le
  have hu_bdd : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) u := hw_bdd.mono_le huw
  refine le_antisymm ?_ ?_
  · calc
      Filter.limsup u atTop ≤ Filter.limsup w atTop :=
        Filter.limsup_le_limsup huw hu_cobdd hw_bdd
      _ = L := hw.limsup_eq
  · refine Filter.le_limsup_of_le hu_bdd fun b hb => ?_
    by_contra! hbL
    obtain ⟨k, hk⟩ := hb.exists
    have hb₀ : 0 ≤ b := (hu_nonneg k).trans hk
    obtain ⟨α, hbα, hαL⟩ := exists_between hbL
    have hα₀ : 0 < α := hb₀.trans_lt hbα
    have hpow (j : ℕ) : 1 ≤ ((2 : ℝ) ^ α) ^ j :=
      one_le_pow₀ (Real.one_le_rpow (by norm_num) hα₀.le)
    have hlogpow (j : ℕ) : Real.log (((2 : ℝ) ^ α) ^ j) =
        α * ((j : ℝ) * Real.log 2) := by
      rw [Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      ring
    have htail : ∀ᶠ j : ℕ in atTop,
        mobiusDyadicShellEnergy j ≤ ((2 : ℝ) ^ α) ^ j := by
      filter_upwards [hb, tendsto_dyadicTime.eventually_gt_atTop (0 : ℝ)] with j hj htime
      change Real.log (1 + mobiusDyadicShellEnergy j) / ((j : ℝ) * Real.log 2) ≤ b at hj
      have hlog : Real.log (1 + mobiusDyadicShellEnergy j) ≤ α * ((j : ℝ) * Real.log 2) :=
        (div_le_iff₀ htime).mp (hj.trans hbα.le)
      rw [← hlogpow j] at hlog
      have hpos : 0 < 1 + mobiusDyadicShellEnergy j :=
        add_pos_of_pos_of_nonneg zero_lt_one (shellEnergy_nonneg j)
      exact (le_add_of_nonneg_left zero_le_one).trans
        ((Real.log_le_log_iff hpos (zero_lt_one.trans_le (hpow j))).mp hlog)
    obtain ⟨M, hM⟩ := eventually_atTop.1 htail
    let C : ℝ := 1 + ∑ j ∈ Finset.range M, mobiusDyadicShellEnergy j
    have hsum : 0 ≤ ∑ j ∈ Finset.range M, mobiusDyadicShellEnergy j :=
      Finset.sum_nonneg (fun j _ => shellEnergy_nonneg j)
    have hC : 1 ≤ C := le_add_of_nonneg_right hsum
    have hC₀ : 0 ≤ C := zero_le_one.trans hC
    have hbound (j : ℕ) : mobiusDyadicShellEnergy j ≤ C * ((2 : ℝ) ^ α) ^ j := by
      by_cases hj : M ≤ j
      · exact (hM j hj).trans
          (le_mul_of_one_le_left (zero_le_one.trans (hpow j)) hC)
      · have hsingle : mobiusDyadicShellEnergy j ≤
            ∑ i ∈ Finset.range M, mobiusDyadicShellEnergy i :=
          Finset.single_le_sum (fun i _ => shellEnergy_nonneg i)
            (Finset.mem_range.mpr (lt_of_not_ge hj))
        have hhead : (∑ i ∈ Finset.range M, mobiusDyadicShellEnergy i) ≤ C :=
          le_add_of_nonneg_left zero_le_one
        exact hsingle.trans (hhead.trans (le_mul_of_one_le_right hC₀ (hpow j)))
    obtain ⟨B, hαB, hBL⟩ := exists_between hαL
    have hupper : ∀ᶠ N : ℕ in atTop, v N < B :=
      eventually_growth_lt_of_shell_bound hα₀ hαB hC₀ hbound
    have hlower : ∀ᶠ N : ℕ in atTop, B < v N :=
      (tendsto_order.1 hv).1 B hBL
    obtain ⟨_, hlt, hgt⟩ := (hupper.and hlower).exists
    exact (not_lt_of_ge hgt.le) hlt

#print axioms limsup_log_one_add_mobiusDyadicShellEnergy

end D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit
