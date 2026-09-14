/- GID: D5/S3/Weil/Analytic/BaezDuarteContinuation
   generality: G
   mirror-B: D5/B/S3/Weil/Analytic/BaezDuarteContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual coefficient decay continues the Newton sum through the pole and implies RH. -/
import D5.S3.Weil.Analytic.BaezDuarteNewton
import D5.S3.Analytic.SeriesInequalities.BaezDuarteNewtonMajorant
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

/-!
The coefficient, polynomial and initial Newton identity retain their existing
owners. The continuation uses Mathlib's entire multiplier `riemannZeta₁`.
At one the analytic reciprocal is zero, not the totalized raw reciprocal.
The paper's positive exponent in its proof paragraph is not a premise: the
negative exponent in Theorem 1.1 and Proposition 2.1 is used here.
All finite prefixes and all compact sets, including the empty set, are kept.
The preregistered analytic product identity feeds the zero-exclusion theorem;
the normalization and convergence bindings are its companion results.
Utility none: these are general analytic statements, not finite certificates.
-/

open scoped BigOperators Topology
open Filter
open D5.S3.Weil.RieszBaezDuarte
open D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
open D5.S3.Analytic.SeriesInequalities.BaezDuarteNewtonMajorant
open D5.S3.Weil.Analytic.BaezDuarteNewton

namespace D5.S3.Weil.Analytic.BaezDuarteContinuation

local notation "H" => (Set.ofPred fun s : ℂ => (1 : ℝ) / 2 < Complex.re s)
local notation "F" => (fun s : ℂ => ∑' k : ℕ,
  (baezDuarte k : ℂ) * normalizedPochhammer k (s / 2))

variable (hdecay : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
  ∀ k : ℕ, N ≤ k → |baezDuarte k| ≤
    C * Real.rpow (k : ℝ) (-(3 : ℝ) / 4 + ε))

/-- The real coefficient is exactly the original complex finite sum. -/
theorem baez_duarte_complex_finite_sum (k : ℕ) :
    (baezDuarte k : ℂ) = ∑ j ∈ Finset.range (k + 1),
      (-1 : ℂ)^j * (Nat.choose k j : ℂ) / riemannZeta ((2*j+2 : ℕ) : ℂ) := by
  unfold baezDuarte
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have him := riemannZeta_im_eq_zero_of_one_lt
    (x := ((2*j+2 : ℕ) : ℝ)) (by norm_cast; omega)
  have hz : ((riemannZeta ((2*j+2 : ℕ) : ℂ)).re : ℂ) =
      riemannZeta ((2*j+2 : ℕ) : ℂ) := by
    apply Complex.ext <;> simp_all
  push_cast at hz
  rw [hz]

include hdecay

theorem baez_duarte_newton_summable {s : ℂ} (hs : s ∈ H) :
    Summable (fun k : ℕ => (baezDuarte k : ℂ) * normalizedPochhammer k (s/2)) := by
  obtain ⟨g, hg, _, hb⟩ := baez_duarte_newton_compact_majorant hdecay
    {s} (isCompact_singleton) (Set.singleton_subset_iff.mpr hs)
  exact (hg.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => hb k s (Set.mem_singleton s))).of_norm

theorem baez_duarte_newton_uniform (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ H) :
    TendstoUniformlyOn (fun N s => ∑ k ∈ Finset.range N,
      (baezDuarte k : ℂ) * normalizedPochhammer k (s/2)) F atTop K := by
  obtain ⟨g, hg, _, hb⟩ := baez_duarte_newton_compact_majorant hdecay K hK hKH
  exact tendstoUniformlyOn_tsum_nat hg hb

omit hdecay in
private theorem half_plane_open : IsOpen H :=
  isOpen_lt continuous_const Complex.continuous_re

theorem baez_duarte_newton_locally_uniform :
    TendstoLocallyUniformlyOn (fun N s => ∑ k ∈ Finset.range N,
      (baezDuarte k : ℂ) * normalizedPochhammer k (s/2)) F atTop H := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact half_plane_open).mpr
  intro K hKH hK
  exact baez_duarte_newton_uniform hdecay K hK hKH

omit hdecay in
private theorem differentiable_term (k : ℕ) :
    Differentiable ℂ (fun s : ℂ =>
      (baezDuarte k : ℂ) * normalizedPochhammer k (s/2)) := by
  simp only [normalized_pochhammer_eq_prod]
  fun_prop

theorem baez_duarte_newton_differentiable : DifferentiableOn ℂ F H := by
  apply (baez_duarte_newton_locally_uniform hdecay).differentiableOn
    (Filter.Eventually.of_forall fun N => ?_) half_plane_open
  exact (Differentiable.fun_sum fun k _ => differentiable_term k).differentiableOn

/-- Analytic uniqueness transports the initial Dirichlet identification across
the whole half-plane, including one. No zero-freeness hypothesis is used. -/
theorem baez_duarte_newton_regularized_product {s : ℂ} (hs : s ∈ H) :
    riemannZeta₁ s * F s = s - 1 := by
  have hF : AnalyticOnNhd ℂ F H :=
    (baez_duarte_newton_differentiable hdecay).analyticOnNhd half_plane_open
  have hprod : AnalyticOnNhd ℂ (fun z => riemannZeta₁ z * F z) H :=
    by
      intro z hz
      exact (differentiable_riemannZeta₁.analyticAt z).mul (hF z hz)
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) H := by
    intro z _
    fun_prop
  have hinitial : (fun z => riemannZeta₁ z * F z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => z - 1) := by
    have hnb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnb] with z hz
    have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hz
    have hzne := riemannZeta_ne_zero_of_one_lt_re hz
    rw [(baez_duarte_newton_hasSum hz).tsum_eq]
    have he := riemannZeta_eq_inv_sub_mul hz1
    have hmul : (z - 1) * riemannZeta z = riemannZeta₁ z := by
      rw [he, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz1), one_mul]
    rw [← hmul]
    field_simp
  exact hprod.eqOn_of_preconnected_of_eventuallyEq hlinear
    (convex_halfSpace_re_gt _).isPreconnected
    (show (2 : ℂ) ∈ H by change (1 : ℝ)/2 < (2 : ℂ).re; norm_num) hinitial hs

theorem baez_duarte_newton_at_one :
    HasSum (fun k : ℕ => (baezDuarte k : ℂ) *
      normalizedPochhammer k ((1 : ℂ)/2)) 0 := by
  have he := baez_duarte_newton_regularized_product hdecay
    (s := 1) (by change (1 : ℝ)/2 < (1 : ℂ).re; norm_num)
  have he0 : F 1 = 0 := by simpa using he
  simpa only [he0] using
    (baez_duarte_newton_summable hdecay (s := 1) (by change (1 : ℝ)/2 < (1 : ℂ).re; norm_num)).hasSum

private theorem multiplier_ne_zero {s : ℂ} (hs : s ∈ H) : riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    simp
  · intro hz
    have he := baez_duarte_newton_regularized_product hdecay hs
    rw [hz, zero_mul] at he
    exact sub_ne_zero.mpr hs1 he.symm

theorem baez_duarte_newton_reciprocal {s : ℂ} (hs : s ∈ H) :
    HasSum (fun k : ℕ => (baezDuarte k : ℂ) * normalizedPochhammer k (s/2))
      ((s-1) / riemannZeta₁ s) := by
  have he : F s = (s-1) / riemannZeta₁ s := by
    apply (eq_div_iff (multiplier_ne_zero hdecay hs)).mpr
    simpa only [mul_comm] using baez_duarte_newton_regularized_product hdecay hs
  rw [← he]
  exact (baez_duarte_newton_summable hdecay hs).hasSum

theorem baez_duarte_newton_reciprocal_off_one {s : ℂ} (hs : s ∈ H) (hs1 : s ≠ 1) :
    HasSum (fun k : ℕ => (baezDuarte k : ℂ) * normalizedPochhammer k (s/2))
      (1 / riemannZeta s) := by
  have he : 1 / riemannZeta s = (s-1) / riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    simp [mul_inv_rev, div_eq_mul_inv, mul_comm]
  rw [he]
  exact baez_duarte_newton_reciprocal hdecay hs

theorem baez_duarte_newton_reciprocal_uniform (K : Set ℂ) (hK : IsCompact K)
    (hKH : K ⊆ H) :
    TendstoUniformlyOn (fun N s => ∑ k ∈ Finset.range N,
      (baezDuarte k : ℂ) * normalizedPochhammer k (s/2))
      (fun s : ℂ => (s-1) / riemannZeta₁ s) atTop K := by
  apply (baez_duarte_newton_uniform hdecay K hK hKH).congr_right
  intro s hs
  exact (baez_duarte_newton_reciprocal hdecay (hKH hs)).tsum_eq

/-- The raw zeta product equals one only away from its pole. -/
theorem baez_duarte_newton_product_off_one {s : ℂ} (hs : s ∈ H) (hs1 : s ≠ 1) :
    riemannZeta s * F s = 1 := by
  rw [riemannZeta_eq_inv_sub_mul hs1, mul_assoc,
    baez_duarte_newton_regularized_product hdecay hs]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr hs1)

theorem baez_duarte_decay_implies_rh : RiemannHypothesis := by
  apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro s hz hs hlt
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hlt
  have hprod := baez_duarte_newton_product_off_one hdecay hs hs1
  simp only [hz, zero_mul, zero_ne_one] at hprod

omit hdecay in
/-- The paper's epsilon/2 convention quantifies the identical decay condition. -/
theorem baez_duarte_epsilon_half_iff :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ k : ℕ, N ≤ k → |baezDuarte k| ≤ C * Real.rpow (k : ℝ) (-(3 : ℝ)/4 + ε)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ k : ℕ, N ≤ k → |baezDuarte k| ≤ C * Real.rpow (k : ℝ) (-(3 : ℝ)/4 + ε/2)) := by
  constructor
  · intro h ε hε
    exact h (ε/2) (half_pos hε)
  · intro h ε hε
    simpa only [mul_div_cancel_left₀ ε (by norm_num : (2 : ℝ) ≠ 0)] using
      h (2*ε) (mul_pos (by norm_num) hε)

omit hdecay in
/-- The original complex finite-coefficient bound itself implies standard RH. -/
theorem baez_duarte_original_decay_implies_rh
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ k : ℕ, N ≤ k →
        ‖∑ j ∈ Finset.range (k+1), (-1 : ℂ)^j * (Nat.choose k j : ℂ) /
          riemannZeta ((2*j+2 : ℕ) : ℂ)‖ ≤
            C * Real.rpow (k : ℝ) (-(3 : ℝ)/4+ε)) : RiemannHypothesis := by
  apply baez_duarte_decay_implies_rh
  intro ε hε
  obtain ⟨C, hC, N, hN, hb⟩ := h ε hε
  refine ⟨C, hC, N, hN, fun k hk => ?_⟩
  simpa only [← baez_duarte_complex_finite_sum, Complex.norm_real,
    Real.norm_eq_abs] using hb k hk

end D5.S3.Weil.Analytic.BaezDuarteContinuation
