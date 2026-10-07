/- GID: D5/S3/Arith/Robin/LogarithmicEndpointVariation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/LogarithmicEndpointVariation
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Cubic endpoint Mellin moments pay the entire logarithmic fourth variation. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import D5.S3.Arith.Robin.LogarithmicMellinReserve

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology
open MeasureTheory Set
open D5.S3.Arith.Robin
open MellinWeightedVariation LogarithmicMellinReserve

namespace D5.S3.Arith.Robin.LogarithmicEndpointVariation

/-- The contentful kernel-price step. A small beta interval pays the full
logarithmic price for every m >= 8, including arbitrarily large m. -/
private lemma log_four_kernel_price {m : ℝ} (hm : 8 ≤ m) :
    m / (Real.log m) ^ 4 ≤ 4 * Real.exp 1 *
      (∫ β in (0 : ℝ)..(1 / 2 : ℝ),
        β ^ 3 * Real.exp (Real.log m * (1 - β))) := by
  have hm0 : 0 < m := by linarith
  have hl : 0 < Real.log m := Real.log_pos (by linarith)
  have hlog8 : 2 ≤ Real.log (8 : ℝ) := by
    have heq := Real.log_pow (2 : ℝ) 3
    norm_num at heq
    have htwo := Real.log_two_gt_d9
    linarith
  have hl2 : 2 ≤ Real.log m :=
    hlog8.trans (Real.log_le_log (by norm_num) hm)
  let u : ℝ := 1 / Real.log m
  have hu : 0 < u := by dsimp [u]; positivity
  have huhalf : u ≤ (1 / 2 : ℝ) := by
    dsimp [u]
    apply (div_le_iff₀ hl).2
    linarith
  have hc : Continuous (fun β : ℝ =>
      β ^ 3 * Real.exp (Real.log m * (1 - β))) := by fun_prop
  have hsmall : ∀ β ∈ Icc (0 : ℝ) u,
      m / Real.exp 1 * β ^ 3 ≤
        β ^ 3 * Real.exp (Real.log m * (1 - β)) := by
    intro β hβ
    have hβlog : β * Real.log m ≤ 1 := by
      have h := (le_div_iff₀ hl).mp hβ.2
      simpa only [u] using h
    have hp : m / Real.exp 1 ≤ Real.exp (Real.log m * (1 - β)) := by
      calc
        _ = Real.exp (Real.log m - 1) := by
          rw [Real.exp_sub, Real.exp_log hm0]
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hp (pow_nonneg hβ.1 3)
  have hlocal : (∫ β in (0 : ℝ)..u, m / Real.exp 1 * β ^ 3) ≤
      (∫ β in (0 : ℝ)..u, β ^ 3 * Real.exp (Real.log m * (1 - β))) :=
    intervalIntegral.integral_mono_on hu.le
    ((continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 u)
    (hc.intervalIntegrable 0 u) hsmall
  have hlocalValue :
      (∫ β in (0 : ℝ)..u, m / Real.exp 1 * β ^ 3) =
        m / (4 * Real.exp 1 * (Real.log m) ^ 4) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    dsimp [u]
    norm_num
    field_simp [hl.ne', (Real.exp_pos 1).ne']
    <;> ring
  rw [hlocalValue] at hlocal
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) (1 / 2))]
      (fun β : ℝ => β ^ 3 * Real.exp (Real.log m * (1 - β))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with β hβ
    exact mul_nonneg (pow_nonneg hβ.1.le 3) (Real.exp_pos _).le
  have hlarge := intervalIntegral.integral_mono_interval
    (show (0 : ℝ) ≤ 0 from le_rfl) hu.le huhalf hnonneg
    (hc.intervalIntegrable 0 (1 / 2))
  calc
    m / (Real.log m) ^ 4 =
        (4 * Real.exp 1) * (m / (4 * Real.exp 1 * (Real.log m) ^ 4)) := by
      field_simp [hl.ne', (Real.exp_pos 1).ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hlocal.trans hlarge) (by positivity)

/-- Cubic endpoint moments pay a complete logarithmic fourth moment.
The exact six-term head is retained; the infinite tail is bounded uniformly.
The hypothesis concerns all finite spectral prefixes, so no pre-existing
logarithmic summability or parameter/infinite-sum interchange is assumed. -/
theorem log_four_variation_of_cubic_endpoint_moments
    (a : ℕ → ℝ) (C : ℝ) (ha : ∀ m, 0 ≤ a m) (hC : 0 ≤ C)
    (hbudget : ∀ β : ℝ, 0 < β → β ≤ (1 / 2 : ℝ) → ∀ N : ℕ,
      (∑ j ∈ Finset.range N, ((j + 8 : ℕ) : ℝ) ^ (1 - β) * a (j + 8)) ≤
        C / β ^ 3) :
    Summable (fun j : ℕ =>
      ((j + 2 : ℕ) : ℝ) / (Real.log ((j + 2 : ℕ) : ℝ)) ^ 4 * a (j + 2)) ∧
    (∑' j : ℕ, ((j + 2 : ℕ) : ℝ) /
      (Real.log ((j + 2 : ℕ) : ℝ)) ^ 4 * a (j + 2)) ≤
      (∑ j ∈ Finset.range 6, ((j + 2 : ℕ) : ℝ) /
        (Real.log ((j + 2 : ℕ) : ℝ)) ^ 4 * a (j + 2)) +
          2 * Real.exp 1 * C := by
  classical
  let f : ℕ → ℝ := fun j => ((j + 2 : ℕ) : ℝ) /
    (Real.log ((j + 2 : ℕ) : ℝ)) ^ 4 * a (j + 2)
  have hf : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; positivity [ha (j + 2)]
  have htail : ∀ N : ℕ, (∑ j ∈ Finset.range N, f (j + 6)) ≤
      2 * Real.exp 1 * C := by
    intro N
    let F : ℕ → ℝ → ℝ := fun j β => β ^ 3 *
      Real.exp (Real.log ((j + 8 : ℕ) : ℝ) * (1 - β)) * a (j + 8)
    have hF : ∀ j, Continuous (F j) := by intro j; dsimp [F]; fun_prop
    have hFint : ∀ j, IntervalIntegrable (F j) volume (0 : ℝ) (1 / 2) :=
      fun j => (hF j).intervalIntegrable 0 (1 / 2)
    have hsumInt : IntervalIntegrable
        (fun β => ∑ j ∈ Finset.range N, F j β) volume (0 : ℝ) (1 / 2) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hsum : ∀ β ∈ Ioo (0 : ℝ) (1 / 2),
        (∑ j ∈ Finset.range N, F j β) ≤ C := by
      intro β hβ
      have heq : (∑ j ∈ Finset.range N, F j β) =
          β ^ 3 * (∑ j ∈ Finset.range N,
            ((j + 8 : ℕ) : ℝ) ^ (1 - β) * a (j + 8)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [F]
        rw [Real.rpow_def_of_pos (by positivity)]
        ring
      rw [heq]
      calc
        _ ≤ β ^ 3 * (C / β ^ 3) := mul_le_mul_of_nonneg_left
          (hbudget β hβ.1 hβ.2.le N) (pow_nonneg hβ.1.le 3)
        _ = C := by field_simp [hβ.1.ne']
    have hintegral :
        (∫ β in (0 : ℝ)..(1 / 2 : ℝ), ∑ j ∈ Finset.range N, F j β) ≤ C / 2 := by
      calc
        _ ≤ ∫ _β in (0 : ℝ)..(1 / 2 : ℝ), C :=
          intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
            hsumInt intervalIntegrable_const hsum
        _ = _ := by simp; ring
    have hprice : ∀ j,
        f (j + 6) ≤ 4 * Real.exp 1 *
          (∫ β in (0 : ℝ)..(1 / 2 : ℝ), F j β) := by
      intro j
      have hp := mul_le_mul_of_nonneg_right
        (log_four_kernel_price (m := ((j + 8 : ℕ) : ℝ))
          (by exact_mod_cast (show 8 ≤ j + 8 by omega)))
        (ha (j + 8))
      calc
        f (j + 6) = ((j + 8 : ℕ) : ℝ) /
            (Real.log ((j + 8 : ℕ) : ℝ)) ^ 4 * a (j + 8) := by
          dsimp [f]
        _ ≤ _ := hp
        _ = _ := by
          dsimp [F]
          rw [intervalIntegral.integral_mul_const]
          ring
    calc
      _ ≤ ∑ j ∈ Finset.range N, 4 * Real.exp 1 *
          (∫ β in (0 : ℝ)..(1 / 2 : ℝ), F j β) :=
        Finset.sum_le_sum (fun j _ => hprice j)
      _ = 4 * Real.exp 1 *
          (∫ β in (0 : ℝ)..(1 / 2 : ℝ), ∑ j ∈ Finset.range N, F j β) := by
        rw [intervalIntegral.integral_finsetSum (fun j _ => hFint j), Finset.mul_sum]
      _ ≤ 4 * Real.exp 1 * (C / 2) :=
        mul_le_mul_of_nonneg_left hintegral (by positivity)
      _ = 2 * Real.exp 1 * C := by ring
  have hprefix : ∀ N : ℕ, (∑ j ∈ Finset.range N, f j) ≤
      (∑ j ∈ Finset.range 6, f j) + 2 * Real.exp 1 * C := by
    intro N
    calc
      _ ≤ ∑ j ∈ Finset.range (6 + N), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) (fun j _ _ => hf j)
      _ = (∑ j ∈ Finset.range 6, f j) +
          (∑ j ∈ Finset.range N, f (j + 6)) := by
        simpa only [Nat.add_comm] using Finset.sum_range_add f 6 N
      _ ≤ _ := by
        simpa only [add_comm] using
          add_le_add_left (htail N) (∑ j ∈ Finset.range 6, f j)
  exact ⟨summable_of_sum_range_le hf hprefix,
    Real.tsum_le_of_sum_range_le hf hprefix⟩

noncomputable def cubicEndpointConstant (d a μ x : ℝ) : ℝ :=
  ((1 + (Real.log x)⁻¹) / 2 +
    (1 + 2 * (Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2)) *
      (a + d / 2 + 3 * μ / 2) / Real.log x

/-- The same logarithmic envelopes pay the full logarithmic fourth
variation of every measurable residual through their Mellin endpoint family. -/
theorem logarithmic_four_weighted_variation (ρ : ℝ → ℝ) (d a μ x : ℝ)
    (hx : 1 < x) (hρ : Measurable ρ) (hd : 0 ≤ d) (ha : 0 ≤ a) (hμ : 0 ≤ μ)
    (hlow : ∀ y : ℝ, 0 < y → y ≤ 1 → |ρ y| ≤ d * y + a * (-Real.log y * y))
    (hhigh : ∀ y : ℝ, 1 ≤ y → |ρ y| ≤ μ * (1 + Real.log y)) :
    Summable (fun j : ℕ => ((j + 2 : ℕ) : ℝ) /
      (Real.log ((j + 2 : ℕ) : ℝ)) ^ 4 *
        |genericP ρ x (j + 2) - genericP ρ x (j + 3)|) ∧
    (∑' j : ℕ, ((j + 2 : ℕ) : ℝ) /
      (Real.log ((j + 2 : ℕ) : ℝ)) ^ 4 *
        |genericP ρ x (j + 2) - genericP ρ x (j + 3)|) ≤
      (∑ j ∈ Finset.range 6, ((j + 2 : ℕ) : ℝ) /
        (Real.log ((j + 2 : ℕ) : ℝ)) ^ 4 *
          |genericP ρ x (j + 2) - genericP ρ x (j + 3)|) +
          2 * Real.exp 1 * cubicEndpointConstant d a μ x := by
  classical
  let v : ℕ → ℝ := fun m => |genericP ρ x (m : ℝ) - genericP ρ x ((m : ℝ) + 1)|
  have hv : ∀ m, 0 ≤ v m := fun m => abs_nonneg _
  have hC : 0 ≤ cubicEndpointConstant d a μ x := by
    unfold cubicEndpointConstant
    positivity [ha, hμ, Real.log_pos hx]
  have hbudget : ∀ β : ℝ, 0 < β → β ≤ (1 / 2 : ℝ) → ∀ N : ℕ,
      (∑ j ∈ Finset.range N, ((j + 8 : ℕ) : ℝ) ^ (1 - β) * v (j + 8)) ≤
        cubicEndpointConstant d a μ x / β ^ 3 := by
    intro β hβ hβhalf N
    have hα : 0 < 1 - β := by linarith
    have hα1 : 1 - β < 1 := by linarith
    let f : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ (1 - β) * v (j + 1)
    have hg : Summable f ∧ (∑' j, f j) ≤
        x ^ ((1 - β) - 1) / Real.log x * ((1 + (Real.log x)⁻¹ +
          (1 + 2 * (Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2) / β) *
            reserve d a μ (1 - β)) := by
      have hm := logarithmic_weighted_variation ρ d a μ x (1 - β)
        hx hα hα1 hρ hlow hhigh
      refine ⟨?_, ?_⟩
      · simpa only [f, v, Nat.cast_add, Nat.cast_one, add_assoc,
          one_add_one_eq_two] using hm.1
      · calc
          _ ≤ variationConstant x (1 - β) * reserve d a μ (1 - β) := by
            simpa only [f, v, Nat.cast_add, Nat.cast_one, add_assoc,
              one_add_one_eq_two] using hm.2
          _ = _ := by
            unfold variationConstant
            rw [show 1 - (1 - β) = β by ring]
            ring
    have hf : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; positivity [hv (j + 1)]
    have hwhole : (∑ j ∈ Finset.range (7 + N), f j) ≤
        x ^ ((1 - β) - 1) / Real.log x * ((1 + (Real.log x)⁻¹ +
          (1 + 2 * (Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2) / β) *
            reserve d a μ (1 - β)) :=
      (Summable.sum_le_tsum (Finset.range (7 + N)) (fun j _ => hf j) hg.1).trans hg.2
    have hhead : 0 ≤ ∑ j ∈ Finset.range 7, f j :=
      Finset.sum_nonneg (fun j _ => hf j)
    have hsplit : (∑ j ∈ Finset.range (7 + N), f j) =
        (∑ j ∈ Finset.range 7, f j) + (∑ j ∈ Finset.range N, f (j + 7)) := by
      simpa only [Nat.add_comm] using Finset.sum_range_add f 7 N
    have htail : (∑ j ∈ Finset.range N,
        ((j + 8 : ℕ) : ℝ) ^ (1 - β) * v (j + 8)) ≤
        x ^ ((1 - β) - 1) / Real.log x * ((1 + (Real.log x)⁻¹ +
          (1 + 2 * (Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2) / β) *
            reserve d a μ (1 - β)) := by
      have ht : (∑ j ∈ Finset.range N, f (j + 7)) ≤
          x ^ ((1 - β) - 1) / Real.log x * ((1 + (Real.log x)⁻¹ +
          (1 + 2 * (Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2) / β) *
            reserve d a μ (1 - β)) := by
        rw [hsplit] at hwhole
        linarith
      simpa only [f, show ∀ j : ℕ, (j + 7) + 1 = j + 8 by intro j; omega] using ht
    refine htail.trans ?_
    let L := Real.log x
    let h₁ := 1 + L⁻¹
    let h₂ := 1 + 2 * L⁻¹ + 2 * L⁻¹ ^ 2
    have hL : 0 < L := Real.log_pos hx
    have hh₁ : 0 ≤ h₁ := by dsimp [h₁]; positivity
    have hh₂ : 0 ≤ h₂ := by dsimp [h₂]; positivity
    have hden1 : 1 / (1 - β) ≤ 2 := (div_le_iff₀ hα).2 (by linarith)
    have hden2 : 1 / (1 - β) ^ 2 ≤ 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hα)).2
      nlinarith [sq_nonneg (β - (1 / 2 : ℝ))]
    have hreserve : reserve d a μ (1 - β) ≤ a / β ^ 2 + d / β + 6 * μ := by
      unfold reserve
      rw [show 1 - (1 - β) = β by ring]
      have hhigh := mul_le_mul_of_nonneg_left (add_le_add hden1 hden2) hμ
      nlinarith [hhigh]
    have hreserve0 : 0 ≤ reserve d a μ (1 - β) := by
      unfold reserve
      positivity [ha, hμ]
    have hxpow : x ^ ((1 - β) - 1) ≤ 1 := by
      calc
        _ ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
        _ = _ := Real.rpow_zero x
    have hcoeff : 0 ≤ h₁ + h₂ / β := by positivity
    have hpolynomial : (h₁ * β + h₂) * (a + d * β + 6 * μ * β ^ 2) ≤
        (h₁ / 2 + h₂) * (a + d / 2 + 3 * μ / 2) := by
      have hb2 : β ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
      have hmu2 := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ 6 * μ by positivity [hμ])
      have hDβ := mul_le_mul_of_nonneg_left hβhalf hd
      apply mul_le_mul
      · have hfirst := add_le_add_right
          (mul_le_mul_of_nonneg_left hβhalf hh₁) h₂
        calc
          _ ≤ h₁ * (1 / 2 : ℝ) + h₂ := by
            simpa only [add_comm] using hfirst
          _ = _ := by ring
      · nlinarith [hDβ, hmu2]
      · positivity [ha, hμ]
      · positivity
    have htarget : x ^ ((1 - β) - 1) / L *
        ((h₁ + h₂ / β) * reserve d a μ (1 - β)) ≤ cubicEndpointConstant d a μ x / β ^ 3 := by
      calc
        _ ≤ (1 / L) * ((h₁ + h₂ / β) *
            (a / β ^ 2 + d / β + 6 * μ)) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right hxpow hL.le
          · exact mul_le_mul_of_nonneg_left hreserve hcoeff
          · exact mul_nonneg hcoeff hreserve0
          · positivity
        _ = (1 / (L * β ^ 3)) *
            ((h₁ * β + h₂) * (a + d * β + 6 * μ * β ^ 2)) := by
          field_simp [hL.ne', hβ.ne']
          <;> ring
        _ ≤ (1 / (L * β ^ 3)) *
            ((h₁ / 2 + h₂) * (a + d / 2 + 3 * μ / 2)) :=
          mul_le_mul_of_nonneg_left hpolynomial (by positivity)
        _ = _ := by
          unfold cubicEndpointConstant
          dsimp [L, h₁, h₂]
          field_simp [(Real.log_pos hx).ne', hβ.ne']
          <;> ring
    simpa only [L, h₁, h₂, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using htarget
  have h := log_four_variation_of_cubic_endpoint_moments v
    (cubicEndpointConstant d a μ x) hv hC hbudget
  simpa only [v, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num] using h


end D5.S3.Arith.Robin.LogarithmicEndpointVariation
