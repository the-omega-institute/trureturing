/- GID: D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/DiracHydrogenFineStructure4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Runge–Lenz symmetry, circular Dirac radial states and Sommerfeld energy coefficients. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Orthogonality.OrthogonalFourSplit
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! Hydrogen shell counts, explicit radial solutions and the fine-structure expansion.
The concrete orthogonal split uses two copies of the oriented cross-product Lie algebra,
with the inverse coordinates given by the sum and difference of the two factors. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D

theorem bohr_shell_degeneracy (n : ℕ) :
    (∑ ℓ ∈ Finset.range n, (2 * ℓ + 1)) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem bohr_spin_shell_capacity (n : ℕ) :
    (∑ ℓ ∈ Finset.range n, 2 * (2 * ℓ + 1)) = 2 * n ^ 2 := by
  rw [← Finset.mul_sum, bohr_shell_degeneracy]

theorem dirac_subshell_degeneracy (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, (if k + 1 = n then 2 * k + 2 else 4 * k + 4)) = 2 * n ^ 2 := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_eq_add_one]
  calc
    (∑ k ∈ Finset.range p, (if k + 1 = p + 1 then 2 * k + 2 else 4 * k + 4)) + (2 * p + 2)
        = (∑ k ∈ Finset.range p, (2 * (2 * k + 1) + 2)) + (2 * p + 2) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          have hkp := Finset.mem_range.mp hk
          rw [ite_eq_right (by omega)]
          ring
    _ = 2 * (p + 1) ^ 2 := by
      rw [Finset.sum_add_distrib, bohr_spin_shell_capacity]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      change 2 * p ^ 2 + p * 2 + (2 * p + 2) = _
      ring

def circularGamma (k : ℕ) (ζ : ℝ) : ℝ := Real.sqrt ((k : ℝ) ^ 2 - ζ ^ 2)
def circularEnergy (m : ℝ) (k : ℕ) (ζ : ℝ) : ℝ := m * circularGamma k ζ / (k : ℝ)
def circularDecay (m : ℝ) (k : ℕ) (ζ : ℝ) : ℝ := m * ζ / (k : ℝ)
def circularG (m : ℝ) (k : ℕ) (ζ r : ℝ) : ℝ :=
  r ^ circularGamma k ζ * Real.exp (-circularDecay m k ζ * r)
def circularF (m : ℝ) (k : ℕ) (ζ r : ℝ) : ℝ :=
  -(((k : ℝ) - circularGamma k ζ) / ζ) * circularG m k ζ r

def radialDiracAt (m E ζ : ℝ) (κ : ℤ) (G F : ℝ → ℝ) (r : ℝ) : Prop :=
  DifferentiableAt ℝ G r ∧ DifferentiableAt ℝ F r ∧
    deriv G r + ((κ : ℝ) / r) * G r = (m + E + ζ / r) * F r ∧
    deriv F r - ((κ : ℝ) / r) * F r = (m - E - ζ / r) * G r

private theorem circular_gamma_bounds {k : ℕ} {ζ : ℝ} (hζ : 0 < ζ) (hζk : ζ < (k : ℝ)) :
    0 < circularGamma k ζ ∧ circularGamma k ζ < (k : ℝ) ∧
      circularGamma k ζ ^ 2 = (k : ℝ) ^ 2 - ζ ^ 2 := by
  have hp : 0 < (k : ℝ) ^ 2 - ζ ^ 2 := by
    have := mul_pos (sub_pos.mpr hζk) (add_pos (hζ.trans hζk) hζ)
    nlinarith only [this]
  have hγ : 0 < circularGamma k ζ := Real.sqrt_pos.2 hp
  have hs : circularGamma k ζ ^ 2 = (k : ℝ) ^ 2 - ζ ^ 2 := Real.sq_sqrt hp.le
  refine ⟨hγ, (Real.sqrt_lt' (hζ.trans hζk)).2 ?_, hs⟩
  nlinarith only [sq_pos_of_pos hζ]

private theorem circularG_derivative (m : ℝ) (k : ℕ) (ζ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (circularG m k ζ)
      ((circularGamma k ζ / r - circularDecay m k ζ) * circularG m k ζ r) r := by
  have hpow := Real.hasDerivAt_rpow_const (p := circularGamma k ζ) (Or.inl hr.ne')
  have hexp := ((hasDerivAt_id r).const_mul (-circularDecay m k ζ)).exp
  convert hpow.mul hexp using 1
  · rfl
  · simp only [id_eq, mul_one, circularG, Real.rpow_sub_one hr.ne']
    ring

theorem dirac_circular_solves_coupled_radial_ode (m : ℝ) (k : ℕ) {ζ r : ℝ}
    (hζ : 0 < ζ) (hζk : ζ < (k : ℝ)) (hr : 0 < r) :
    let G := circularG m k ζ
    let F := circularF m k ζ
    let rate := circularGamma k ζ / r - circularDecay m k ζ
    HasDerivAt G (rate * G r) r ∧ HasDerivAt F (rate * F r) r ∧
      radialDiracAt m (circularEnergy m k ζ) ζ (-(k : ℤ)) G F r := by
  dsimp only
  let c := -(((k : ℝ) - circularGamma k ζ) / ζ)
  have hG := circularG_derivative m k ζ hr
  have hF : HasDerivAt (circularF m k ζ)
      ((circularGamma k ζ / r - circularDecay m k ζ) * circularF m k ζ r) r := by
    convert hG.const_mul c using 1
    · rfl
    · change _ * (c * _) = c * (_ * _)
      ring
  have hk : (k : ℝ) ≠ 0 := (hζ.trans hζk).ne'
  have hp := (circular_gamma_bounds hζ hζk).2.2
  have hc₁ : ζ * c = circularGamma k ζ - (k : ℝ) := by
    dsimp only [c]
    field_simp
    ring
  have hc₂ : c * ((k : ℝ) + circularGamma k ζ) = -ζ := by
    dsimp only [c]
    field_simp
    nlinarith only [hp]
  have hE₁ : (m + circularEnergy m k ζ) * c = -circularDecay m k ζ := by
    calc
      _ = (m / (k : ℝ)) * (c * ((k : ℝ) + circularGamma k ζ)) := by
        unfold circularEnergy
        field_simp
      _ = _ := by rw [hc₂]; simp only [circularDecay]; ring
  have hE₂ : -c * circularDecay m k ζ = m - circularEnergy m k ζ := by
    unfold circularDecay circularEnergy
    calc
      _ = -(m / (k : ℝ)) * (ζ * c) := by ring
      _ = _ := by rw [hc₁]; field_simp; ring
  refine ⟨hG, hF, hG.differentiableAt, hF.differentiableAt, ?_, ?_⟩
  · rw [hG.deriv]
    simp only [Int.cast_neg, Int.cast_natCast]
    change _ = _ * (c * circularG m k ζ r)
    calc
      _ = ((circularGamma k ζ - (k : ℝ)) / r - circularDecay m k ζ) *
            circularG m k ζ r := by ring
      _ = (ζ * c / r + (-circularDecay m k ζ)) * circularG m k ζ r := by rw [hc₁]; ring
      _ = _ := by rw [← hE₁]; ring
  · rw [hF.deriv]
    simp only [Int.cast_neg, Int.cast_natCast]
    change (_ * (c * circularG m k ζ r)) - _ * (c * circularG m k ζ r) = _
    calc
      _ = ((c * ((k : ℝ) + circularGamma k ζ)) / r - c * circularDecay m k ζ) *
            circularG m k ζ r := by ring
      _ = ((-ζ) / r + (-c) * circularDecay m k ζ) * circularG m k ζ r := by
        rw [hc₂]
        ring
      _ = _ := by rw [hE₂]; ring

theorem dirac_1s_solves_coupled_radial_ode (m : ℝ) {ζ r : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ < 1) (hr : 0 < r) :
    let G := circularG m 1 ζ
    let F := circularF m 1 ζ
    let rate := Real.sqrt (1 - ζ ^ 2) / r - m * ζ
    HasDerivAt G (rate * G r) r ∧ HasDerivAt F (rate * F r) r ∧
      radialDiracAt m (m * Real.sqrt (1 - ζ ^ 2)) ζ (-1) G F r := by
  simpa [circularGamma, circularDecay, circularEnergy] using
    dirac_circular_solves_coupled_radial_ode m 1 hζ (by exact_mod_cast hζ1) hr

theorem dirac_2p_solves_coupled_radial_ode (m : ℝ) {ζ r : ℝ}
    (hζ : 0 < ζ) (hζ2 : ζ < 2) (hr : 0 < r) :
    let G := circularG m 2 ζ
    let F := circularF m 2 ζ
    let rate := Real.sqrt (4 - ζ ^ 2) / r - m * ζ / 2
    HasDerivAt G (rate * G r) r ∧ HasDerivAt F (rate * F r) r ∧
      radialDiracAt m (m * Real.sqrt (4 - ζ ^ 2) / 2) ζ (-2) G F r := by
  simpa [circularGamma, circularDecay, circularEnergy, show (2 : ℝ) ^ 2 = 4 by norm_num] using
    dirac_circular_solves_coupled_radial_ode m 2 hζ (by exact_mod_cast hζ2) hr

private theorem circular_ratio_rationalized {k : ℕ} {ζ : ℝ} (hζ : 0 < ζ)
    (hζk : ζ < (k : ℝ)) :
    ((k : ℝ) - circularGamma k ζ) / ζ = ζ / ((k : ℝ) + circularGamma k ζ) := by
  obtain ⟨hg, _, hs⟩ := circular_gamma_bounds hζ hζk
  apply (div_eq_div_iff hζ.ne' (add_pos (hζ.trans hζk) hg).ne').2
  nlinarith only [hs]

theorem dirac_1s_normalizable_and_small_component_ratio {m ζ : ℝ}
    (hm : 0 < m) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    let γ := circularGamma 1 ζ
    let G := circularG m 1 ζ
    let F := circularF m 1 ζ
    (∀ r > 0, |F r / G r| = (1 - γ) / ζ) ∧
      (1 - γ) / ζ = Real.sqrt ((1 - γ) / (1 + γ)) ∧ (1 - γ) / ζ < 1 ∧
      IntegrableOn (fun r => (G r) ^ 2 + (F r) ^ 2) (Ioi 0) := by
  dsimp only
  let γ := circularGamma 1 ζ
  let c := (1 - γ) / ζ
  obtain ⟨hg, hg1, _⟩ := circular_gamma_bounds (k := 1) hζ (by exact_mod_cast hζ1)
  change 0 < γ at hg
  norm_num at hg1
  change γ < 1 at hg1
  have hrational : c = ζ / (1 + γ) := by
    simpa [c, γ] using circular_ratio_rationalized (k := 1) hζ (by exact_mod_cast hζ1)
  have hc : 0 < c := div_pos (sub_pos.mpr hg1) hζ
  have hden : 0 < 1 + γ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    have hG : 0 < circularG m 1 ζ r :=
      mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
    rw [circularF, mul_div_cancel_right₀ _ hG.ne', abs_neg]
    simpa [c, γ] using abs_of_pos hc
  · have hsq : c ^ 2 = (1 - γ) / (1 + γ) := by
      calc
        _ = ((1 - γ) / ζ) * (ζ / (1 + γ)) := by
          rw [← hrational]; ring
        _ = _ := by field_simp
    rw [← hsq, Real.sqrt_sq hc.le]
  · change c < 1
    rw [hrational, div_lt_one hden]
    linarith only [hζ1, hg]
  · have hd : 0 < circularDecay m 1 ζ := by simp [circularDecay, mul_pos hm hζ]
    have htail := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := 2 * γ) (b := 2 * circularDecay m 1 ζ)
      (by linarith only [hg]) zero_lt_one (by positivity)
    have hscaled := htail.const_mul (1 + c ^ 2)
    refine IntegrableOn.congr_fun hscaled (fun r hr => ?_) measurableSet_Ioi
    have hr' : 0 < r := hr
    change (1 + c ^ 2) * (r ^ (2 * γ) * Real.exp (-(2 * circularDecay m 1 ζ) * r ^ (1 : ℝ))) =
      (circularG m 1 ζ r) ^ 2 + (circularF m 1 ζ r) ^ 2
    have hF : circularF m 1 ζ r = -c * circularG m 1 ζ r := by simp [circularF, c, γ]
    have hG : (circularG m 1 ζ r) ^ 2 =
        r ^ (2 * γ) * Real.exp (-(2 * circularDecay m 1 ζ) * r) := by
      change (r ^ γ * Real.exp (-circularDecay m 1 ζ * r)) ^ 2 = _
      rw [mul_pow, pow_two (r ^ γ), pow_two (Real.exp _), ← Real.rpow_add hr', ← Real.exp_add]
      congr 2 <;> ring
    rw [hF, Real.rpow_one, ← hG]
    ring

theorem dirac_1s_ratio_asymptotic :
    Tendsto (fun ζ : ℝ => ((1 - circularGamma 1 ζ) / ζ) / ζ) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hcont : ContinuousAt (fun ζ : ℝ => 1 / (1 + circularGamma 1 ζ)) 0 := by
    apply continuousAt_const.div
    · unfold circularGamma
      fun_prop
    · norm_num [circularGamma]
  have hlim := hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have he : ∀ᶠ ζ : ℝ in 𝓝[>] (0 : ℝ), 0 < ζ ∧ ζ < 1 :=
    eventually_mem_nhdsWithin.and ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds)
  have heq : (fun ζ : ℝ => 1 / (1 + circularGamma 1 ζ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ζ => ((1 - circularGamma 1 ζ) / ζ) / ζ) := by
    filter_upwards [he] with ζ hζ
    have hrat := circular_ratio_rationalized (k := 1) hζ.1 (by exact_mod_cast hζ.2)
    simp only [Nat.cast_one] at hrat
    rw [hrat]
    field_simp [hζ.1.ne']
  convert hlim.congr' heq using 1
  norm_num [circularGamma]

private def sommerfeldDenom (n k : ℕ) (u : ℝ) : ℝ :=
  ((n - k : ℕ) : ℝ) + Real.sqrt ((k : ℝ) ^ 2 - u)

def sommerfeldEnergySq (m : ℝ) (n k : ℕ) (u : ℝ) : ℝ :=
  m / Real.sqrt (1 + u / sommerfeldDenom n k u ^ 2)

def sommerfeldEnergy (m : ℝ) (n k : ℕ) (ζ : ℝ) : ℝ :=
  sommerfeldEnergySq m n k (ζ ^ 2)

theorem sommerfeld_circular_matches_ode (m : ℝ) (n : ℕ) {ζ : ℝ}
    (hζ : 0 < ζ) (hζn : ζ < (n : ℝ)) :
    sommerfeldEnergy m n n ζ = circularEnergy m n ζ := by
  obtain ⟨hγ, _, hs⟩ := circular_gamma_bounds hζ hζn
  have hn := hζ.trans hζn
  change m / Real.sqrt (1 + ζ ^ 2 / sommerfeldDenom n n (ζ ^ 2) ^ 2) =
    m * circularGamma n ζ / (n : ℝ)
  have hd : sommerfeldDenom n n (ζ ^ 2) = circularGamma n ζ := by
    simp [sommerfeldDenom, circularGamma]
  rw [hd]
  have h : 1 + ζ ^ 2 / circularGamma n ζ ^ 2 =
      ((n : ℝ) / circularGamma n ζ) ^ 2 := by
    field_simp
    nlinarith only [hs]
  rw [h, Real.sqrt_sq (div_nonneg hn.le hγ.le)]
  field_simp

theorem sommerfeld_bound_state_window {m ζ : ℝ} {n k : ℕ}
    (hm : 0 < m) (hζ : 0 < ζ) (hζk : ζ < (k : ℝ)) :
    0 < sommerfeldEnergy m n k ζ ∧ sommerfeldEnergy m n k ζ < m := by
  have hγ := (circular_gamma_bounds hζ hζk).1
  have hd : 0 < sommerfeldDenom n k (ζ ^ 2) :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hγ
  have hq : 0 < ζ ^ 2 / sommerfeldDenom n k (ζ ^ 2) ^ 2 := by positivity
  have hs : 1 < Real.sqrt (1 + ζ ^ 2 / sommerfeldDenom n k (ζ ^ 2) ^ 2) := by
    have hbase : (1 : ℝ) < 1 + ζ ^ 2 / sommerfeldDenom n k (ζ ^ 2) ^ 2 := by
      linarith only [hq]
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hbase
  have hs' : 0 < Real.sqrt (1 + ζ ^ 2 / sommerfeldDenom n k (ζ ^ 2) ^ 2) :=
    zero_lt_one.trans hs
  exact ⟨div_pos hm hs', (div_lt_iff₀ hs').2 (lt_mul_of_one_lt_right hm hs)⟩

theorem sommerfeld_ground_critical_limit (m : ℝ) :
    Tendsto (sommerfeldEnergy m 1 1) (𝓝[<] 1) (𝓝 0) := by
  have hcont : ContinuousAt (fun ζ : ℝ => m * Real.sqrt (1 - ζ ^ 2)) 1 := by fun_prop
  have hlim := hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  have he : ∀ᶠ ζ : ℝ in 𝓝[<] (1 : ℝ), 0 < ζ ∧ ζ < 1 :=
    ((eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds).and
      eventually_mem_nhdsWithin
  have heq : (fun ζ : ℝ => m * Real.sqrt (1 - ζ ^ 2)) =ᶠ[𝓝[<] (1 : ℝ)]
      sommerfeldEnergy m 1 1 := by
    filter_upwards [he] with ζ hζ
    rw [sommerfeld_circular_matches_ode m 1 hζ.1 (by exact_mod_cast hζ.2)]
    simp [circularEnergy, circularGamma]
  convert hlim.congr' heq using 1
  norm_num

theorem sommerfeld_strictly_increasing_in_k {m ζ : ℝ} {n k₁ k₂ : ℕ} (hm : 0 < m)
    (hk : k₁ < k₂) (hk₂ : k₂ ≤ n) (hζ : 0 < ζ) (hζk : ζ < (k₁ : ℝ)) :
    sommerfeldEnergy m n k₁ ζ < sommerfeldEnergy m n k₂ ζ := by
  have hk' : (k₁ : ℝ) < k₂ := by exact_mod_cast hk
  have hζk₂ := hζk.trans hk'
  have ⟨hγ₁, _, hs₁⟩ := circular_gamma_bounds hζ hζk
  have ⟨hγ₂, _, hs₂⟩ := circular_gamma_bounds hζ hζk₂
  have hg : circularGamma k₁ ζ < circularGamma k₂ ζ := by
    apply Real.sqrt_lt_sqrt (Real.sqrt_pos.1 hγ₁).le
    gcongr
  have loss (k : ℕ) (hγ : 0 < circularGamma k ζ)
      (hγsq : circularGamma k ζ ^ 2 = (k : ℝ) ^ 2 - ζ ^ 2) (hkz : ζ < (k : ℝ)) :
      (k : ℝ) - circularGamma k ζ = ζ ^ 2 / ((k : ℝ) + circularGamma k ζ) := by
    apply (eq_div_iff (add_pos (hζ.trans hkz) hγ).ne').2
    nlinarith only [hγsq]
  have hd : sommerfeldDenom n k₁ (ζ ^ 2) < sommerfeldDenom n k₂ (ζ ^ 2) := by
    have hp : (k₁ : ℝ) + circularGamma k₁ ζ < (k₂ : ℝ) + circularGamma k₂ ζ := add_lt_add hk' hg
    have hlt := div_lt_div_of_pos_left (sq_pos_of_pos hζ) (add_pos (hζ.trans hζk) hγ₁) hp
    rw [← loss k₁ hγ₁ hs₁ hζk, ← loss k₂ hγ₂ hs₂ hζk₂] at hlt
    unfold sommerfeldDenom
    rw [Nat.cast_sub (hk.le.trans hk₂), Nat.cast_sub hk₂]
    change (n : ℝ) - (k₁ : ℝ) + circularGamma k₁ ζ <
      (n : ℝ) - (k₂ : ℝ) + circularGamma k₂ ζ
    linarith only [hlt]
  have hd₁ : 0 < sommerfeldDenom n k₁ (ζ ^ 2) :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hγ₁
  have hd₂ := hd₁.trans hd
  have hq := div_lt_div_of_pos_left (sq_pos_of_pos hζ) (sq_pos_of_pos hd₁)
    (pow_lt_pow_left₀ hd hd₁.le (by decide : 2 ≠ 0))
  have hb₂ : 0 < 1 + ζ ^ 2 / sommerfeldDenom n k₂ (ζ ^ 2) ^ 2 := by positivity
  exact div_lt_div_of_pos_left hm (Real.sqrt_pos.2 hb₂)
    (Real.sqrt_lt_sqrt hb₂.le (add_lt_add_right hq 1))

private def sommerfeldBase (n k : ℕ) (u : ℝ) : ℝ :=
  1 + u * (sommerfeldDenom n k u)⁻¹ ^ 2

private def inverseDenomSlope (n k : ℕ) (u : ℝ) : ℝ :=
  (2 * Real.sqrt ((k : ℝ) ^ 2 - u) * sommerfeldDenom n k u ^ 2)⁻¹

private def sommerfeldBaseSlope (n k : ℕ) (u : ℝ) : ℝ :=
  (sommerfeldDenom n k u)⁻¹ ^ 2 +
    u * (2 * (sommerfeldDenom n k u)⁻¹ * inverseDenomSlope n k u)

private theorem inverseDenom_hasDerivAt (n k : ℕ) {u : ℝ} (hu : u < (k : ℝ) ^ 2) :
    HasDerivAt (fun v => (sommerfeldDenom n k v)⁻¹) (inverseDenomSlope n k u) u := by
  have hs := sub_pos.mpr hu
  have hsq : 0 < Real.sqrt ((k : ℝ) ^ 2 - u) := Real.sqrt_pos.2 hs
  have hd : 0 < sommerfeldDenom n k u := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hsq
  have hroot := ((hasDerivAt_id u).const_sub ((k : ℝ) ^ 2)).sqrt (by simpa using hs.ne')
  have hsum := hroot.const_add (((n - k : ℕ) : ℝ))
  have hinv := hsum.inv (by simpa [sommerfeldDenom] using hd.ne')
  convert hinv using 1
  · rfl
  · simp only [inverseDenomSlope, sommerfeldDenom, id_eq]
    have hdn : ((n - k : ℕ) : ℝ) + Real.sqrt ((k : ℝ) ^ 2 - u) ≠ 0 := hd.ne'
    field_simp

private theorem sommerfeldBase_hasDerivAt (n k : ℕ) {u : ℝ} (hu : u < (k : ℝ) ^ 2) :
    HasDerivAt (sommerfeldBase n k) (sommerfeldBaseSlope n k u) u := by
  have hinv := (inverseDenom_hasDerivAt n k hu).pow 2
  convert ((hasDerivAt_id u).mul hinv).const_add 1 using 1
  · rfl
  · simp only [sommerfeldBaseSlope, id_eq, Pi.pow_apply]
    ring

private theorem hasDerivAt_mul_left_zero {f : ℝ → ℝ} (hf : ContinuousAt f 0) :
    HasDerivAt (fun u => u * f u) (f 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope.2
  refine (hf.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := ({0}ᶜ : Set ℝ))] with u hu
  have hu' : u ≠ 0 := by simpa using hu
  simp [slope_def_field, hu', mul_div_cancel_left₀]

theorem sommerfeld_fourth_order_expansion (m : ℝ) (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    let g := sommerfeldEnergySq m n k
    g 0 = m ∧ HasDerivAt g (-m / (2 * (n : ℝ) ^ 2)) 0 ∧
      HasDerivAt (deriv g)
        (-m / (n : ℝ) ^ 3 * (1 / (k : ℝ) - 3 / (4 * (n : ℝ)))) 0 := by
  dsimp only
  let q := sommerfeldBase n k
  let q' := sommerfeldBaseSlope n k
  let d := sommerfeldDenom n k
  let d' := inverseDenomSlope n k
  have hk₀ : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hk₂ := sq_pos_of_pos hk₀
  have hd : d 0 = (n : ℝ) := by
    dsimp [d, sommerfeldDenom]
    rw [sub_zero, Real.sqrt_sq hk₀.le, Nat.cast_sub hkn, sub_add_cancel]
  have hd' : d' 0 = (2 * (k : ℝ) * (n : ℝ) ^ 2)⁻¹ := by
    change (2 * Real.sqrt ((k : ℝ) ^ 2 - 0) * d 0 ^ 2)⁻¹ = _
    rw [hd, sub_zero, Real.sqrt_sq hk₀.le]
  have hq : q 0 = 1 := by simp [q, sommerfeldBase]
  have hq' : q' 0 = (n : ℝ)⁻¹ ^ 2 := by
    change (d 0)⁻¹ ^ 2 + 0 * (2 * (d 0)⁻¹ * d' 0) = _
    rw [hd, zero_mul, add_zero]
  have hD := inverseDenom_hasDerivAt n k hk₂
  have hQ := sommerfeldBase_hasDerivAt n k hk₂
  have hs : ContinuousAt (fun u => Real.sqrt ((k : ℝ) ^ 2 - u)) 0 := by fun_prop
  have hc : ContinuousAt d' 0 := by
    unfold d' inverseDenomSlope
    apply ContinuousAt.inv₀ ((continuousAt_const.mul hs).mul (by
      exact (continuousAt_const.add hs).pow 2))
    change 2 * Real.sqrt ((k : ℝ) ^ 2 - 0) * d 0 ^ 2 ≠ 0
    rw [sub_zero, Real.sqrt_sq hk₀.le, hd]
    positivity
  have hQ' : HasDerivAt q' (4 * (d 0)⁻¹ * d' 0) 0 := by
    have hmul := hasDerivAt_mul_left_zero
      (((continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ)) 0).mul hD.continuousAt).mul hc)
    convert (hD.pow 2).add hmul using 1
    · rfl
    · change 4 * (d 0)⁻¹ * d' 0 = 2 * (d 0)⁻¹ ^ (2 - 1) * d' 0 + _
      norm_num
      ring
  have heq {u : ℝ} (hu : 0 < q u) :
      sommerfeldEnergySq m n k u = m * q u ^ (-(1 / 2) : ℝ) := by
    have hb : q u = 1 + u / d u ^ 2 := by
      unfold q sommerfeldBase
      rw [inv_pow, ← div_eq_mul_inv]
    rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, hb]
    rfl
  have hnear : ∀ᶠ u : ℝ in 𝓝 0, u < (k : ℝ) ^ 2 ∧ 0 < q u := by
    apply (eventually_lt_nhds hk₂).and
    have hq₀ : 0 < q 0 := by rw [hq]; norm_num
    exact hQ.continuousAt (Ioi_mem_nhds hq₀)
  have hG {u : ℝ} (hu : u < (k : ℝ) ^ 2) (hb : 0 < q u) :
      HasDerivAt (fun v => m * q v ^ (-(1 / 2) : ℝ))
        (-m / 2 * (q u ^ (-(3 / 2) : ℝ) * q' u)) u := by
    have H := ((sommerfeldBase_hasDerivAt n k hu).rpow_const (p := (-(1 / 2) : ℝ))
      (Or.inl hb.ne')).const_mul m
    convert H using 1
    change -m / 2 * (q u ^ (-(3 / 2) : ℝ) * q' u) =
      m * (q' u * (-(1 / 2)) * q u ^ ((-(1 / 2) : ℝ) - 1))
    rw [show (-(1 / 2) : ℝ) - 1 = -(3 / 2) by norm_num]
    ring
  have hGeq : sommerfeldEnergySq m n k =ᶠ[𝓝 (0 : ℝ)]
      (fun u => m * q u ^ (-(1 / 2) : ℝ)) := by
    filter_upwards [hnear] with u hu using heq hu.2
  have hdeq : deriv (sommerfeldEnergySq m n k) =ᶠ[𝓝 (0 : ℝ)]
      (fun u => -m / 2 * (q u ^ (-(3 / 2) : ℝ) * q' u)) := by
    filter_upwards [hGeq.eventuallyEq_nhds, hnear] with u hu hpos
    exact ((hG hpos.1 hpos.2).congr_of_eventuallyEq hu).deriv
  have hq₀ : 0 < q 0 := by rw [hq]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [heq hq₀, hq, Real.one_rpow, mul_one]
  · convert (hG hk₂ hq₀).congr_of_eventuallyEq hGeq using 1
    rw [hq, hq', Real.one_rpow, one_mul]
    field_simp
  · have hslope := (hQ.rpow_const (p := (-(3 / 2) : ℝ)) (Or.inl hq₀.ne')).mul hQ'
    convert (hslope.const_mul (-m / 2)).congr_of_eventuallyEq hdeq using 1
    change -m / (n : ℝ) ^ 3 * (1 / (k : ℝ) - 3 / (4 * (n : ℝ))) =
      -m / 2 * (q' 0 * (-(3 / 2)) * q 0 ^ ((-(3 / 2) : ℝ) - 1) * q' 0 +
        q 0 ^ (-(3 / 2) : ℝ) * (4 * (d 0)⁻¹ * d' 0))
    rw [hq, hq', hd, hd', Real.one_rpow, Real.one_rpow]
    field_simp
    ring

theorem sommerfeld_2p_splitting_coefficient (m : ℝ) :
    (1 / 2 : ℝ) * (deriv (deriv (sommerfeldEnergySq m 2 2)) 0 -
      deriv (deriv (sommerfeldEnergySq m 2 1)) 0) = m / 32 := by
  have h₂ := (sommerfeld_fourth_order_expansion m 2 2 (by decide) (by decide)).2.2.deriv
  have h₁ := (sommerfeld_fourth_order_expansion m 2 1 (by decide) (by decide)).2.2.deriv
  rw [h₂, h₁]
  norm_num
  ring

def jPlus {V : Type*} [Add V] [SMul ℝ V] (L A : Fin 3 → V) (i : Fin 3) : V :=
  (1 / 2 : ℝ) • (L i + A i)

def jMinus {V : Type*} [Sub V] [SMul ℝ V] (L A : Fin 3 → V) (i : Fin 3) : V :=
  (1 / 2 : ℝ) • (L i - A i)

private def epsilon (i j : Fin 3) : Fin 3 → ℝ :=
  crossProduct (Pi.single i 1) (Pi.single j 1)

def rungeLenzRotation {V : Type*} [AddCommMonoid V] [SMul ℝ V]
    (X : Fin 3 → V) (i j : Fin 3) : V := ∑ a, epsilon i j a • X a

private def rotationMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (i j : Fin 3) : (Fin 3 → V) →ₗ[ℝ] V where
  toFun X := rungeLenzRotation X i j
  map_add' X Y := by
    simp only [rungeLenzRotation, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [rungeLenzRotation, Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact smul_comm _ _ _

theorem runge_lenz_split_iff {V : Type*} [LieRing V] [LieAlgebra ℝ V]
    (L A : Fin 3 → V) :
    (∀ i j, ⁅L i, L j⁆ = rungeLenzRotation L i j ∧
      ⁅L i, A j⁆ = rungeLenzRotation A i j ∧ ⁅A i, A j⁆ = rungeLenzRotation L i j) ↔
    (∀ i j, ⁅jPlus L A i, jPlus L A j⁆ = rungeLenzRotation (jPlus L A) i j ∧
      ⁅jMinus L A i, jMinus L A j⁆ = rungeLenzRotation (jMinus L A) i j ∧
      ⁅jPlus L A i, jMinus L A j⁆ = 0) := by
  constructor
  · intro h i j
    obtain ⟨hll, hla, haa⟩ := h i j
    have hal : ⁅A i, L j⁆ = rungeLenzRotation A i j := by
      rw [← lie_skew, (h j i).2.1]
      simp only [rungeLenzRotation, epsilon, ← cross_anticomm (Pi.single i (1 : ℝ))
        (Pi.single j 1), Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_neg]
    have hp : rungeLenzRotation (jPlus L A) i j =
        (1 / 2 : ℝ) • (rungeLenzRotation L i j + rungeLenzRotation A i j) := by
      change rotationMap i j ((1 / 2 : ℝ) • (L + A)) = _
      rw [map_smul, map_add]
      rfl
    have hm : rungeLenzRotation (jMinus L A) i j =
        (1 / 2 : ℝ) • (rungeLenzRotation L i j - rungeLenzRotation A i j) := by
      change rotationMap i j ((1 / 2 : ℝ) • (L - A)) = _
      rw [map_smul, map_sub]
      rfl
    constructor
    · simp only [jPlus] at hp ⊢
      rw [hp]
      simp only [smul_lie, lie_smul, add_lie, lie_add, hll, hla, hal, haa]
      module
    constructor
    · simp only [jMinus] at hm ⊢
      rw [hm]
      simp only [smul_lie, lie_smul, sub_lie, lie_sub, hll, hla, hal, haa]
      module
    · simp only [jPlus, jMinus, smul_lie, lie_smul, add_lie, lie_sub, hll, hla, hal, haa]
      module
  · intro h
    let P := jPlus L A
    let M := jMinus L A
    have hL : L = P + M := by
      funext i
      change L i = (1 / 2 : ℝ) • (L i + A i) + (1 / 2 : ℝ) • (L i - A i)
      module
    have hA : A = P - M := by
      funext i
      change A i = (1 / 2 : ℝ) • (L i + A i) - (1 / 2 : ℝ) • (L i - A i)
      module
    intro i j
    obtain ⟨hpp, hmm, hpm⟩ := h i j
    change ⁅P i, P j⁆ = _ at hpp
    change ⁅M i, M j⁆ = _ at hmm
    change ⁅P i, M j⁆ = 0 at hpm
    have hmp : ⁅M i, P j⁆ = 0 := by rw [← lie_skew, (h j i).2.2, neg_zero]
    have hs := (rotationMap (V := V) i j).map_add P M
    have ht := (rotationMap (V := V) i j).map_sub P M
    change rungeLenzRotation (P + M) i j =
      rungeLenzRotation P i j + rungeLenzRotation M i j at hs
    change rungeLenzRotation (P - M) i j =
      rungeLenzRotation P i j - rungeLenzRotation M i j at ht
    have hsp : rungeLenzRotation P i j = ⁅P i, P j⁆ := hpp.symm
    have hsm : rungeLenzRotation M i j = ⁅M i, M j⁆ := hmm.symm
    rw [hL, hA, hs, ht, hsp, hsm]
    simp only [Pi.add_apply, Pi.sub_apply, add_lie, lie_add, sub_lie, lie_sub, hpm, hmp]
    exact ⟨by abel, by abel, by abel⟩

theorem runge_lenz_casimir_identities {R : Type*} [Ring R] [Algebra ℝ R]
    (L A : Fin 3 → R) (hcomm : ∀ i, L i * A i = A i * L i) :
    (∑ i, (L i ^ 2 + A i ^ 2)) = (2 : ℝ) • (∑ i, (jPlus L A i ^ 2 + jMinus L A i ^ 2)) ∧
      (∑ i, L i * A i) = (∑ i, (jPlus L A i ^ 2 - jMinus L A i ^ 2)) := by
  have hp (i : Fin 3) :
      jPlus L A i ^ 2 = (1 / 4 : ℝ) • ((L i + A i) * (L i + A i)) := by
    simp only [jPlus, pow_two, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    norm_num
  have hm (i : Fin 3) :
      jMinus L A i ^ 2 = (1 / 4 : ℝ) • ((L i - A i) * (L i - A i)) := by
    simp only [jMinus, pow_two, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    norm_num
  constructor
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp, hm]
    simp only [pow_two, add_mul, mul_add, sub_mul, mul_sub]
    module
  · apply Finset.sum_congr rfl
    intro i _
    rw [hp, hm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, hcomm]
    module

theorem bohr_energy_from_casimir {jLeft jRight : ℝ} (hjLeft : 0 ≤ jLeft)
    (hjRight : 0 ≤ jRight) (n : ℕ) (hn : (n : ℝ) = 2 * jLeft + 1)
    (horth : jLeft * (jLeft + 1) - jRight * (jRight + 1) = 0) (m α : ℝ) :
    let C := 2 * (jLeft * (jLeft + 1) + jRight * (jRight + 1))
    jLeft = jRight ∧ C = 4 * jLeft * (jLeft + 1) ∧ C = (n : ℝ) ^ 2 - 1 ∧
      -m * α ^ 2 / (2 * (C + 1)) = -m * α ^ 2 / (2 * (n : ℝ) ^ 2) := by
  dsimp only
  have hst : (jLeft - jRight) * (jLeft + jRight + 1) = 0 := by nlinarith only [horth]
  have hsum : jLeft + jRight + 1 ≠ 0 := by positivity
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hst).resolve_right hsum)
  subst jRight
  have hC : 2 * (jLeft * (jLeft + 1) + jLeft * (jLeft + 1)) = (n : ℝ) ^ 2 - 1 := by
    rw [hn]
    ring
  refine ⟨rfl, by ring, hC, ?_⟩
  rw [hC, sub_add_cancel]

end D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
