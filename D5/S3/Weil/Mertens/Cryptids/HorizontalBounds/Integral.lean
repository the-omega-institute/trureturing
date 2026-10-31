/- GID: D5/S3/Weil/Mertens/Cryptids/HorizontalBounds/Integral
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/HorizontalBounds/Integral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids HorizontalBounds analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/HorizontalBounds.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.HorizontalBounds.Foundation

/-! Original HorizontalBounds analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.HorizontalBounds

open Complex Filter MeasureTheory Set Asymptotics Metric MeromorphicOn ComplexConjugate
open scoped Real Topology ArithmeticFunction LSeries.notation

/-- **Explicit Backlund-Jensen Zero-Counting Bound for `riemannZeta₁` on Vertical Strips**:
For any `T : ℝ` and radii `0 < r < R < 2`, the number of zeros of `riemannZeta₁` (counted with
multiplicity) in `closedBall (2 + T * I) r` is at most
`Real.log (3 * (1 + (‖1 + T * I‖ + R) * (1 + (‖2 + T * I‖ + R) / (2 - R)))) / Real.log (R / r)`. -/
theorem sum_divisor_riemannZeta₁_closedBall_two_add_mul_I_le (T : ℝ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR2 : R < 2) :
    ∑ᶠ u, divisor riemannZeta₁ (closedBall (2 + (T : ℂ) * I) |r|) u ≤
      Real.log (3 * (1 + (‖(1 : ℂ) + (T : ℂ) * I‖ + R) *
        (1 + (‖(2 : ℂ) + (T : ℂ) * I‖ + R) / (2 - R)))) / Real.log (R / r) := by
  let c : ℂ := 2 + (T : ℂ) * I
  let M : ℝ := 1 + (‖(1 : ℂ) + (T : ℂ) * I‖ + R) * (1 + (‖c‖ + R) / (2 - R))
  have hc_re : c.re = 2 := by simp [c]
  have hc_sub : c - 1 = 1 + (T : ℂ) * I := by simp [c]; ring
  have hR_pos : 0 < R := hr.trans hrR
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    have : 0 ≤ (‖(1 : ℂ) + (T : ℂ) * I‖ + R) * (1 + (‖c‖ + R) / (2 - R)) :=
      mul_nonneg (by positivity) (add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith)))
    linarith
  have hc_norm : 1 / 3 ≤ ‖riemannZeta₁ c‖ :=
    one_third_le_norm_riemannZeta₁_of_re_eq_two hc_re
  have hc_ne : riemannZeta₁ c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc_norm
    linarith
  have h_jensen : ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u ≤
      Real.log (M / ‖riemannZeta₁ c‖) / Real.log (R / r) := by
    refine sum_divisor_riemannZeta₁_le (by rwa [abs_of_pos hr])
      (by rwa [abs_of_pos hr, abs_of_pos hR_pos]) hM_ge_one hc_ne ?_
    intro z hz
    rw [abs_of_pos hR_pos] at hz
    have h := norm_riemannZeta₁_le_on_sphere hR_pos.le (by linarith [hc_re]) hz
    rwa [hc_re, hc_sub] at h
  refine h_jensen.trans ?_
  have h_log_pos : 0 < Real.log (R / r) := Real.log_pos ( (one_lt_div hr).mpr hrR )
  refine div_le_div_of_nonneg_right ?_ h_log_pos.le
  refine Real.log_le_log (div_pos (by linarith) (norm_pos_iff.mpr hc_ne)) ?_
  rw [div_le_iff₀ (norm_pos_iff.mpr hc_ne)]
  calc
    M = 3 * M * (1 / 3) := by ring
    _ ≤ 3 * M * ‖riemannZeta₁ c‖ := by gcongr

/-- Every zero `z ∈ U` of `riemannZeta₁` has `1 ≤ divisor riemannZeta₁ U z`. -/
theorem one_le_divisor_riemannZeta₁ {U : Set ℂ} {z : ℂ} (hzU : z ∈ U)
    (hz0 : riemannZeta₁ z = 0) :
    1 ≤ divisor riemannZeta₁ U z := by
  have hAn : AnalyticOnNhd ℂ riemannZeta₁ U := analyticOnNhd_riemannZeta₁ U
  rw [hAn.divisor_apply hzU]
  have h_ne_top : analyticOrderAt riemannZeta₁ z ≠ ⊤ := analyticOrderAt_riemannZeta₁_ne_top z
  have h_ne_zero : analyticOrderAt riemannZeta₁ z ≠ 0 :=
    (hAn z hzU).analyticOrderAt_ne_zero.mpr hz0
  have h_nat : (analyticOrderNatAt riemannZeta₁ z : ℕ∞) = analyticOrderAt riemannZeta₁ z :=
    Nat.cast_analyticOrderNatAt h_ne_top
  have h_pos : 1 ≤ analyticOrderNatAt riemannZeta₁ z := by
    by_contra! hlt
    have h0 : analyticOrderNatAt riemannZeta₁ z = 0 := Nat.lt_one_iff.mp hlt
    rw [h0, Nat.cast_zero] at h_nat
    exact h_ne_zero h_nat.symm
  rw [← h_nat]
  simpa using h_pos

/-- For any finite set `F : Finset ℂ` of zeros of `riemannZeta₁` contained in `closedBall c |r|`,
its cardinality is at most `∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u`. -/
theorem card_finset_zeros_le_sum_divisor_riemannZeta₁ {c : ℂ} {r : ℝ} (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, ρ ∈ closedBall c |r| ∧ riemannZeta₁ ρ = 0) :
    (F.card : ℝ) ≤ (∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) := by
  have h_supp :=
    (divisor riemannZeta₁ (closedBall c |r|)).finiteSupport (isCompact_closedBall c |r|)
  have h_sub : F ⊆ h_supp.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have h1 := one_le_divisor_riemannZeta₁ (hF ρ hρ).1 (hF ρ hρ).2
    omega
  have h_int : (F.card : ℤ) ≤ ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u := by
    calc
      (F.card : ℤ) = ∑ _ρ ∈ F, (1 : ℤ) := by simp
      _ ≤ ∑ ρ ∈ F, divisor riemannZeta₁ (closedBall c |r|) ρ :=
        Finset.sum_le_sum fun ρ hρ ↦ one_le_divisor_riemannZeta₁ (hF ρ hρ).1 (hF ρ hρ).2
      _ ≤ ∑ u ∈ h_supp.toFinset, divisor riemannZeta₁ (closedBall c |r|) u :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub fun u _ _ ↦
          (analyticOnNhd_riemannZeta₁ _).divisor_nonneg u
      _ = ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u :=
        (finsum_eq_sum _ h_supp).symm
  exact_mod_cast h_int

/-- Every zero `ρ ≠ 1` of `riemannZeta` is a zero of `riemannZeta₁`. -/
theorem riemannZeta₁_eq_zero_of_riemannZeta_eq_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h1 : ρ ≠ 1) :
    riemannZeta₁ ρ = 0 := by
  have h_eq := riemannZeta_eq_inv_sub_mul h1
  rw [hζ] at h_eq
  rcases mul_eq_zero.mp h_eq.symm with hinv | hz1
  · exact absurd (inv_eq_zero.mp hinv) (sub_ne_zero.mpr h1)
  · exact hz1

/-- Finiteness of the set of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) with
`ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
theorem finite_criticalLineZerosInStrip (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)}.Finite := by
  have hcompact : IsCompact (Set.Icc (1 / 2 : ℝ) (1 / 2) ×ℂ Set.Icc (T - 1 / 2) (T + 3 / 2)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine hcompact.inter_riemannZetaZeros_finite.subset ?_
  rintro ρ ⟨hζ, hre, him⟩
  exact ⟨⟨⟨hre.symm.le, hre.le⟩, him⟩, hζ⟩

/-- The canonical `Finset ℂ` of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) with
`ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
noncomputable def criticalLineZerosInStrip (T : ℝ) : Finset ℂ :=
  (finite_criticalLineZerosInStrip T).toFinset

@[simp]
theorem mem_criticalLineZerosInStrip {T : ℝ} {ρ : ℂ} :
    ρ ∈ criticalLineZerosInStrip T ↔
      riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2) :=
  Set.Finite.mem_toFinset (finite_criticalLineZerosInStrip T)

/-- Finiteness of the symmetric set of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`)
with `|ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
theorem finite_symmetricCriticalLineZerosInStrip (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧
      |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)}.Finite := by
  have hcompact : IsCompact (Set.Icc (1 / 2 : ℝ) (1 / 2) ×ℂ Set.Icc (-(T + 3 / 2)) (T + 3 / 2)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine hcompact.inter_riemannZetaZeros_finite.subset ?_
  rintro ρ ⟨hζ, hre, him⟩
  exact ⟨⟨⟨hre.symm.le, hre.le⟩, abs_le.mp him.2⟩, hζ⟩

/-- The canonical `Finset ℂ` of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) with
`|ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
noncomputable def symmetricCriticalLineZerosInStrip (T : ℝ) : Finset ℂ :=
  (finite_symmetricCriticalLineZerosInStrip T).toFinset

@[simp]
theorem mem_symmetricCriticalLineZerosInStrip {T : ℝ} {ρ : ℂ} :
    ρ ∈ symmetricCriticalLineZerosInStrip T ↔
      riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2) :=
  Set.Finite.mem_toFinset (finite_symmetricCriticalLineZerosInStrip T)

/-- The finite set of absolute heights `|ρ.im|` of critical-line zeros in the local strip
`[T - 1 / 2, T + 3 / 2]`. -/
noncomputable def localZeroHeights (T : ℝ) : Finset ℝ :=
  (symmetricCriticalLineZerosInStrip T).image (fun ρ ↦ |ρ.im|)

@[simp]
theorem mem_localZeroHeights {T : ℝ} {γ : ℝ} :
    γ ∈ localZeroHeights T ↔
      ∃ ρ : ℂ, (riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)) ∧
        |ρ.im| = γ := by
  simp [localZeroHeights]

/-- Every critical-line zero `ρ` with `ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)` lies in
`Metric.closedBall (2 + ((T + 1 / 2 : ℝ) : ℂ) * I) |(19 / 10 : ℝ)|`. -/
theorem mem_closedBall_nineteen_tenths_of_mem_criticalLineZerosInStrip {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ criticalLineZerosInStrip T) :
    ρ ∈ Metric.closedBall (2 + ((T + 1 / 2 : ℝ) : ℂ) * I) |(19 / 10 : ℝ)| := by
  obtain ⟨_, hre, him1, him2⟩ := mem_criticalLineZerosInStrip.mp hρ
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 19 / 10), mem_closedBall_iff_norm]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 19 / 10)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  have h_re : (ρ - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I)).re = -3 / 2 := by
    simp [hre]
    ring
  have h_im : (ρ - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I)).im = ρ.im - (T + 1 / 2) := by
    simp
  rw [h_re, h_im]
  have h_im_sq : (ρ.im - (T + 1 / 2)) * (ρ.im - (T + 1 / 2)) ≤ 1 := by
    nlinarith
  nlinarith

/-- Explicit lower bound `1 / 39 ≤ Real.log (39 / 38)`. -/
theorem one_div_thirty_nine_le_log_thirty_nine_div_thirty_eight :
    (1 / 39 : ℝ) ≤ Real.log (39 / 38) := by
  have h_exp : (38 / 39 : ℝ) ≤ Real.exp (-1 / 39) := by
    linarith [Real.add_one_le_exp (-1 / 39 : ℝ)]
  have h_log := Real.log_le_log (by norm_num) h_exp
  rw [Real.log_exp, show (38 / 39 : ℝ) = (39 / 38 : ℝ)⁻¹ by norm_num, Real.log_inv] at h_log
  linarith

/-- **Explicit Local Zero Count Bound (`156 * Real.log (T + 10)`)**:
For every `T ≥ 0`, the number of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`)
with `ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)` is at most `156 * Real.log (T + 10)`. -/
theorem card_criticalLineZerosInStrip_le {T : ℝ} (hT : 0 ≤ T) :
    ((criticalLineZerosInStrip T).card : ℝ) ≤ 156 * Real.log (T + 10) := by
  let T' : ℝ := T + 1 / 2
  let r : ℝ := 19 / 10
  let R : ℝ := 39 / 20
  have hr : 0 < r := by dsimp [r]; norm_num
  have hrR : r < R := by dsimp [r, R]; norm_num
  have hR2 : R < 2 := by dsimp [R]; norm_num
  have h_card_le : ((criticalLineZerosInStrip T).card : ℝ) ≤
      (∑ᶠ u, divisor riemannZeta₁ (closedBall (2 + (T' : ℂ) * I) |r|) u : ℤ) := by
    refine card_finset_zeros_le_sum_divisor_riemannZeta₁ (criticalLineZerosInStrip T) ?_
    intro ρ hρ
    refine ⟨mem_closedBall_nineteen_tenths_of_mem_criticalLineZerosInStrip hρ, ?_⟩
    obtain ⟨hζ, hre, _⟩ := mem_criticalLineZerosInStrip.mp hρ
    refine riemannZeta₁_eq_zero_of_riemannZeta_eq_zero hζ ?_
    intro h1
    rw [h1] at hre
    norm_num at hre
  have h_jensen := sum_divisor_riemannZeta₁_closedBall_two_add_mul_I_le T' hr hrR hR2
  have h_norm1 : ‖(1 : ℂ) + (T' : ℂ) * I‖ + R ≤ T + 10 := by
    have h1 : ‖(1 : ℂ) + (T' : ℂ) * I‖ ≤ 1 + T' := by
      calc
        ‖(1 : ℂ) + (T' : ℂ) * I‖ ≤ ‖(1 : ℂ)‖ + ‖(T' : ℂ) * I‖ := norm_add_le _ _
        _ = 1 + |T'| := by simp
        _ = 1 + T' := by rw [abs_of_pos (by dsimp [T']; linarith)]
    dsimp [T', R] at h1 ⊢
    linarith
  have h_norm2 : ‖(2 : ℂ) + (T' : ℂ) * I‖ + R ≤ T + 10 := by
    have h2 : ‖(2 : ℂ) + (T' : ℂ) * I‖ ≤ 2 + T' := by
      calc
        ‖(2 : ℂ) + (T' : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(T' : ℂ) * I‖ := norm_add_le _ _
        _ = 2 + |T'| := by simp
        _ = 2 + T' := by rw [abs_of_pos (by dsimp [T']; linarith)]
    dsimp [T', R] at h2 ⊢
    linarith
  have h_div2 : 1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R) ≤ 21 * (T + 10) := by
    have h_sub : 2 - R = 1 / 20 := by dsimp [R]; norm_num
    rw [h_sub]
    have h_eq : 1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (1 / 20) =
        1 + 20 * (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) := by ring
    rw [h_eq]
    linarith
  have h_prod : 3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
      (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R))) ≤ (T + 10) ^ 4 := by
    have h_a_nonneg : 0 ≤ ‖(1 : ℂ) + (T' : ℂ) * I‖ + R := by dsimp [R]; positivity
    have h_b_nonneg : 0 ≤ 1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R) := by
      dsimp [R]; positivity
    have h_mul : (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
        (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R)) ≤
        (T + 10) * (21 * (T + 10)) :=
      mul_le_mul h_norm1 h_div2 h_b_nonneg (by linarith)
    have h_sq : 100 ≤ (T + 10) ^ 2 := by nlinarith
    have h_pow4 : (T + 10) ^ 4 = (T + 10) ^ 2 * (T + 10) ^ 2 := by ring
    nlinarith
  have h_pos_lhs : 0 < 3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
      (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R))) := by
    dsimp [R]; positivity
  have h_log_num : Real.log (3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
      (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R)))) ≤ 4 * Real.log (T + 10) := by
    calc
      Real.log (3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
          (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R))))
        ≤ Real.log ((T + 10) ^ 4) := Real.log_le_log h_pos_lhs h_prod
      _ = 4 * Real.log (T + 10) := by rw [Real.log_pow]; push_cast; ring
  have h_Rr : R / r = 39 / 38 := by dsimp [r, R]; norm_num
  have h_log_den : (1 / 39 : ℝ) ≤ Real.log (R / r) := by
    rw [h_Rr]
    exact one_div_thirty_nine_le_log_thirty_nine_div_thirty_eight
  have h_logT10_nonneg : 0 ≤ 4 * Real.log (T + 10) := by
    have : 1 ≤ T + 10 := by linarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg this)
  calc
    ((criticalLineZerosInStrip T).card : ℝ)
      ≤ Real.log (3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
          (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R)))) / Real.log (R / r) :=
        h_card_le.trans h_jensen
    _ ≤ (4 * Real.log (T + 10)) / (1 / 39) :=
        div_le_div₀ h_logT10_nonneg h_log_num (by norm_num) h_log_den
    _ = 156 * Real.log (T + 10) := by ring

/-- Every `γ ∈ localZeroHeights T` maps under `γ ↦ (1 / 2 : ℂ) + (γ : ℂ) * I` into
`criticalLineZerosInStrip T`. -/
theorem half_add_mul_I_mem_criticalLineZerosInStrip_of_mem_localZeroHeights {T γ : ℝ}
    (hγ : γ ∈ localZeroHeights T) :
    (1 / 2 : ℂ) + (γ : ℂ) * I ∈ criticalLineZerosInStrip T := by
  obtain ⟨ρ, ⟨hζ, hre, him⟩, rfl⟩ := mem_localZeroHeights.mp hγ
  refine mem_criticalLineZerosInStrip.mpr ⟨?_, by simp, by simpa using him⟩
  rcases le_or_gt 0 ρ.im with h_nonneg | h_neg
  · have h_eq : (1 / 2 : ℂ) + ((|ρ.im| : ℝ) : ℂ) * I = ρ := by
      rw [abs_of_nonneg h_nonneg]
      apply Complex.ext <;> simp [hre]
    rw [h_eq]
    exact hζ
  · have h_eq : (1 / 2 : ℂ) + ((|ρ.im| : ℝ) : ℂ) * I = conj ρ := by
      rw [abs_of_neg h_neg]
      apply Complex.ext <;> simp [hre]
    rw [h_eq, riemannZeta_conj, hζ, map_zero]

/-- The cardinality of `localZeroHeights T` is at most the cardinality of
`criticalLineZerosInStrip T`. -/
theorem card_localZeroHeights_le_card_criticalLineZerosInStrip (T : ℝ) :
    (localZeroHeights T).card ≤ (criticalLineZerosInStrip T).card := by
  refine Finset.card_le_card_of_injOn (fun γ : ℝ ↦ (1 / 2 : ℂ) + (γ : ℂ) * I) ?_ ?_
  · intro γ hγ
    exact Finset.mem_coe.mpr
      (half_add_mul_I_mem_criticalLineZerosInStrip_of_mem_localZeroHeights (Finset.mem_coe.mp hγ))
  · intro γ₁ _ γ₂ _ h_eq
    have h_im := congrArg Complex.im h_eq
    simpa using h_im

/-- **Explicit Bound on `(localZeroHeights T).card`**:
For every `T ≥ 0`, `((localZeroHeights T).card : ℝ) ≤ 156 * Real.log (T + 10)`. -/
theorem card_localZeroHeights_le {T : ℝ} (hT : 0 ≤ T) :
    ((localZeroHeights T).card : ℝ) ≤ 156 * Real.log (T + 10) := by
  have h1 : ((localZeroHeights T).card : ℝ) ≤ ((criticalLineZerosInStrip T).card : ℝ) := by
    exact_mod_cast card_localZeroHeights_le_card_criticalLineZerosInStrip T
  exact h1.trans (card_criticalLineZerosInStrip_le hT)

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ` of `riemannZeta` has `ρ.re = 1 / 2`. -/
theorem re_eq_half_of_isNontrivialZetaZero (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    ρ.re = 1 / 2 :=
  hRH ρ hρ.1 hρ.2.1 hρ.2.2

/-- For any `y U : ℝ` with `0 ≤ U`, `|(|y| - U)| ≤ |y - U|`. -/
theorem abs_abs_sub_le_abs_sub_of_nonneg {y U : ℝ} (hU : 0 ≤ U) :
    |(|y| - U)| ≤ |y - U| := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy, abs_of_neg (by linarith : y - U < 0), abs_le]
    constructor <;> linarith

/-- For any `y U : ℝ` with `0 ≤ U`, `|(|y| - U)| ≤ |y - (-U)|`. -/
theorem abs_abs_sub_le_abs_sub_neg_of_nonneg {y U : ℝ} (hU : 0 ≤ U) :
    |(|y| - U)| ≤ |y - (-U)| := by
  have h := abs_abs_sub_le_abs_sub_of_nonneg (y := -y) hU
  rwa [abs_neg, show -y - U = -(y - (-U)) by ring, abs_neg] at h

/-- **Existence of a Symmetric Zero-Free Height `U ∈ [T, T + 1]`**:
For every `T ≥ 0`, there exist `U ∈ Set.Icc T (T + 1)` and `Δ : ℝ` such that:
1. `0 < Δ` and `Δ ≤ 1 / 2`,
2. `1 / (314 * Real.log (T + 10)) ≤ Δ`,
3. For **all** critical-line zeros `ρ : ℂ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`),
   `Δ ≤ |(|ρ.im| - U)|`, `Δ ≤ |ρ.im - U|`, and `Δ ≤ |ρ.im - (-U)|`. -/
theorem exists_zero_free_height_in_Icc {T : ℝ} (hT : 0 ≤ T) :
    ∃ U ∈ Set.Icc T (T + 1), ∃ Δ : ℝ,
      0 < Δ ∧ Δ ≤ 1 / 2 ∧
      1 / (314 * Real.log (T + 10)) ≤ Δ ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
        Δ ≤ |(|ρ.im| - U)| ∧ Δ ≤ |ρ.im - U| ∧ Δ ≤ |ρ.im - (-U)|) := by
  let S := localZeroHeights T
  obtain ⟨U, hU_mem, hU_gap⟩ := exists_zero_free_gap_in_Icc S T
  let Δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1))
  have hU_nonneg : 0 ≤ U := hT.trans hU_mem.1
  have hS_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 2 := by
    dsimp [Δ]
    exact one_div_le_one_div_of_le two_pos (by linarith)
  have h_log_ge_one : 1 ≤ Real.log (T + 10) := by
    have h_exp : Real.exp 1 ≤ T + 10 := by
      linarith [Real.exp_one_lt_d9]
    have h_log := Real.log_le_log (Real.exp_pos 1) h_exp
    rwa [Real.log_exp] at h_log
  have hS_le : (S.card : ℝ) ≤ 156 * Real.log (T + 10) := card_localZeroHeights_le hT
  have hΔ_lb : 1 / (314 * Real.log (T + 10)) ≤ Δ := by
    dsimp [Δ]
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith
  refine ⟨U, hU_mem, Δ, hΔ_pos, hΔ_le, hΔ_lb, ?_⟩
  intro ρ hζ hre
  have h_abs_gap : Δ ≤ |(|ρ.im| - U)| := by
    by_cases h_strip : |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)
    · refine hU_gap |ρ.im| ?_
      exact mem_localZeroHeights.mpr ⟨ρ, ⟨hζ, hre, h_strip⟩, rfl⟩
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h_strip
      rcases h_strip with h_lt | h_gt
      · have h1 : 1 / 2 ≤ U - |ρ.im| := by linarith [hU_mem.1]
        have h2 : U - |ρ.im| ≤ |(|ρ.im| - U)| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      · have h1 : 1 / 2 ≤ |ρ.im| - U := by linarith [hU_mem.2]
        have h2 : |ρ.im| - U ≤ |(|ρ.im| - U)| := le_abs_self _
        linarith
  exact ⟨h_abs_gap,
    h_abs_gap.trans (abs_abs_sub_le_abs_sub_of_nonneg hU_nonneg),
    h_abs_gap.trans (abs_abs_sub_le_abs_sub_neg_of_nonneg hU_nonneg)⟩

/-!
## Section 9: Trigonometric `tan` Bound and Binet `digamma` Bound on Horizontal Lines
-/

/-- Exact identity for `Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I))`:
for all `x y : ℝ`,
$$\operatorname{normSq}(\sin(x + y i)) = \sin^2 x + \sinh^2 y.$$ -/
theorem normSq_sin_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) =
      Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.normSq_apply]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, zero_mul,
    add_zero, I_im, mul_one, sub_self, add_im, mul_im]
  calc
    Real.sin x * Real.cosh y * (Real.sin x * Real.cosh y) +
        (0 + Real.cos x * Real.sinh y) * (0 + Real.cos x * Real.sinh y)
      = Real.sin x ^ 2 * (Real.cosh y ^ 2 - Real.sinh y ^ 2) +
          (Real.sin x ^ 2 + Real.cos x ^ 2) * Real.sinh y ^ 2 := by ring
    _ = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
      rw [Real.cosh_sq_sub_sinh_sq y, Real.sin_sq_add_cos_sq x]
      ring

/-- Exact identity for `Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I))`:
for all `x y : ℝ`,
$$\operatorname{normSq}(\cos(x + y i)) = \cos^2 x + \sinh^2 y.$$ -/
theorem normSq_cos_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) =
      Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.normSq_apply]
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, zero_mul,
    add_zero, I_im, mul_one, sub_self, sub_im, mul_im]
  calc
    Real.cos x * Real.cosh y * (Real.cos x * Real.cosh y) +
        (0 - Real.sin x * Real.sinh y) * (0 - Real.sin x * Real.sinh y)
      = Real.cos x ^ 2 * (Real.cosh y ^ 2 - Real.sinh y ^ 2) +
          (Real.sin x ^ 2 + Real.cos x ^ 2) * Real.sinh y ^ 2 := by ring
    _ = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
      rw [Real.cosh_sq_sub_sinh_sq y, Real.sin_sq_add_cos_sq x]
      ring

/-- For `1 ≤ |y|`, `9 / 16 ≤ Real.sinh y ^ 2`. -/
theorem nine_sixteenths_le_sinh_sq_of_one_le_abs {y : ℝ} (hy : 1 ≤ |y|) :
    9 / 16 ≤ Real.sinh y ^ 2 := by
  have h_exp_ge : 2 ≤ Real.exp |y| := by
    linarith [Real.add_one_le_exp |y|]
  have h_exp_neg_le : Real.exp (-|y|) ≤ 1 / 2 := by
    have h_prod : Real.exp (-|y|) * Real.exp |y| = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h_pos : 0 < Real.exp (-|y|) := Real.exp_pos _
    nlinarith
  have h_sinh_abs : 3 / 4 ≤ Real.sinh |y| := by
    rw [Real.sinh_eq]
    linarith
  have h_sq_eq : Real.sinh y ^ 2 = Real.sinh |y| ^ 2 := by
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, Real.sinh_neg, neg_sq]
  rw [h_sq_eq]
  nlinarith

/-- **Explicit Horizontal `Complex.tan` Bound (`‖tan (π * (σ + V * I) / 2)‖ ≤ 2`)**:
For all `σ : ℝ` and `V : ℝ` with `2 ≤ |V|`,
`Complex.cos (π * ((σ : ℂ) + (V : ℂ) * I) / 2) ≠ 0` and
`‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2`. -/
theorem cos_ne_zero_and_norm_tan_le_two_of_two_le_abs (σ : ℝ) {V : ℝ} (hV : 2 ≤ |V|) :
    Complex.cos (π * ((σ : ℂ) + (V : ℂ) * I) / 2) ≠ 0 ∧
      ‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2 := by
  set x : ℝ := Real.pi * σ / 2
  set y : ℝ := Real.pi * V / 2
  have h_arg : π * ((σ : ℂ) + (V : ℂ) * I) / 2 = (x : ℂ) + (y : ℂ) * I := by
    dsimp [x, y]
    push_cast
    ring
  rw [h_arg]
  have hy : 1 ≤ |y| := by
    have h1 : |y| = Real.pi * |V| / 2 := by
      dsimp [y]
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(2 : ℝ)| = 2 by norm_num]
    have hpi : 2 ≤ Real.pi := Real.two_le_pi
    nlinarith
  have h_sinh_sq := nine_sixteenths_le_sinh_sq_of_one_le_abs hy
  have h_sin_sq := normSq_sin_add_mul_I x y
  have h_cos_sq := normSq_cos_add_mul_I x y
  have h_cos_nonneg : 0 ≤ Real.cos x ^ 2 := sq_nonneg _
  have h_sin_le_one : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have h_cos_pos : 0 < Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) := by linarith
  have h_cos_ne : Complex.cos ((x : ℂ) + (y : ℂ) * I) ≠ 0 :=
    Complex.normSq_pos.mp h_cos_pos
  refine ⟨h_cos_ne, ?_⟩
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  have h_norm_cos_pos : 0 < ‖Complex.cos ((x : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr h_cos_ne
  rw [div_le_iff₀ h_norm_cos_pos]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  linarith

/-- Corollary: `‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2` for `2 ≤ |V|`. -/
theorem norm_tan_pi_mul_div_two_le_two (σ : ℝ) {V : ℝ} (hV : 2 ≤ |V|) :
    ‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2 :=
  (cos_ne_zero_and_norm_tan_le_two_of_two_le_abs σ hV).2

/-- Bound on `‖Complex.log (((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I)‖` for `σ ∈ [-1 / 4, 1 / 2]`:
`‖Complex.log (((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi`. -/
theorem norm_log_horizontal_add_one_le {σ V : ℝ} (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)) :
    ‖Complex.log (((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi := by
  set w : ℂ := ((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I
  have hw_re : w.re = σ + 1 := by simp [w]
  have hw_im : w.im = V := by simp [w]
  have hw_re_ge : 3 / 4 ≤ w.re := by linarith [hσ.1]
  have hw_re_le : w.re ≤ 3 / 2 := by linarith [hσ.2]
  have hw_norm_ge : 3 / 4 ≤ ‖w‖ := hw_re_ge.trans (Complex.re_le_norm w)
  have hw_norm_le : ‖w‖ ≤ |V| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hw_re, hw_im, abs_of_pos (by linarith : 0 < σ + 1)] at h
    linarith [hσ.2]
  have hw_norm_pos : 0 < ‖w‖ := by linarith
  have h_inv_le : (|V| + 2)⁻¹ ≤ ‖w‖ := by
    have h1 : (|V| + 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith [abs_nonneg V])
    linarith
  have h_abs_log : |Real.log ‖w‖| ≤ Real.log (|V| + 2) := by
    rw [abs_le]
    refine ⟨?_, Real.log_le_log hw_norm_pos hw_norm_le⟩
    rw [← Real.log_inv]
    exact Real.log_le_log (by positivity) h_inv_le
  rw [Complex.log]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_I, mul_one]
  exact add_le_add h_abs_log (Complex.abs_arg_le_pi w)

/-- **Uniform Horizontal `Complex.digamma` Bound on `σ ∈ [-1 / 4, 1 / 2]` for `2 ≤ |V|`**:
For all `σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)` and `2 ≤ |V|`,
`‖Complex.digamma ((σ : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi + 11 / 6`. -/
theorem norm_digamma_horizontal_le {σ V : ℝ} (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2))
    (hV : 2 ≤ |V|) :
    ‖Complex.digamma ((σ : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi + 11 / 6 := by
  set s : ℂ := (σ : ℂ) + (V : ℂ) * I
  set w : ℂ := ((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I
  have h_sw : s + 1 = w := by dsimp [s, w]; push_cast; ring
  have hs_nat : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.im hm
    have hV0 : V = 0 := by simpa [s] using him
    rw [hV0, abs_zero] at hV
    linarith
  have h_step : Complex.digamma s = (Complex.digamma w - Complex.log w) + Complex.log w - s⁻¹ := by
    have h := Complex.digamma_apply_add_one s hs_nat
    rw [h_sw] at h
    linear_combination -h
  have hw_re_ge : 3 / 4 ≤ w.re := by simp [w]; linarith [hσ.1]
  have hw_re_pos : 0 < w.re := by linarith
  have hw_norm_ge : 3 / 4 ≤ ‖w‖ := hw_re_ge.trans (Complex.re_le_norm w)
  have hs_norm_ge : 2 ≤ ‖s‖ := by
    have h : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    simp [s] at h
    linarith
  have h1 : ‖Complex.digamma w - Complex.log w‖ ≤ 4 / 3 := by
    refine (norm_digamma_sub_log_le_norm_add_re hw_re_pos).trans ?_
    have h_a : 1 / (2 * ‖w‖) ≤ 2 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h_b : 1 / (2 * w.re) ≤ 2 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have h2 : ‖Complex.log w‖ ≤ Real.log (|V| + 2) + Real.pi :=
    norm_log_horizontal_add_one_le hσ
  have h3 : ‖s⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, one_div]
    exact inv_anti₀ two_pos hs_norm_ge
  rw [h_step]
  have h_tri1 := norm_sub_le ((Complex.digamma w - Complex.log w) + Complex.log w) s⁻¹
  have h_tri2 := norm_add_le (Complex.digamma w - Complex.log w) (Complex.log w)
  linarith

/-!
## Section 10: Full Horizontal Segment Bounds on `[-1 / 4, 2] ± U * I`
-/

/-- For any `σ V : ℝ` with `V ≠ 0` and any `n : ℤ`, `(σ : ℂ) + (V : ℂ) * I ≠ (n : ℂ)`. -/
theorem ofReal_add_mul_I_ne_intCast (σ : ℝ) {V : ℝ} (hV : V ≠ 0) (n : ℤ) :
    (σ : ℂ) + (V : ℂ) * I ≠ (n : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  exact hV (by simpa using him)

/-- Under `RiemannHypothesis`, if `V ≠ 0` has a positive gap `0 < Δ` from all critical-line zeros
(`∀ ρ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|`), then
`riemannZeta ((σ : ℂ) + (V : ℂ) * I) ≠ 0` for all `σ : ℝ`. -/
theorem riemannZeta_ofReal_add_mul_I_ne_zero_of_gap (hRH : RiemannHypothesis) (σ : ℝ)
    {V Δ : ℝ} (hV : V ≠ 0) (hΔ_pos : 0 < Δ)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|) :
    riemannZeta ((σ : ℂ) + (V : ℂ) * I) ≠ 0 := by
  set s : ℂ := (σ : ℂ) + (V : ℂ) * I
  intro hz
  have hs_im : s.im = V := by simp [s]
  have hs_triv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    exact hV (by simpa [s] using him)
  have hs_one : s ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    exact hV (by simpa [s] using him)
  have hs_re : s.re = 1 / 2 := hRH s hz hs_triv hs_one
  have h_le := hgap s hz hs_re
  rw [hs_im, sub_self, abs_zero] at h_le
  linarith

/-- **Horizontal Bound on `‖deriv riemannZeta / riemannZeta‖` Across `σ ∈ [-1 / 4, 1 / 2]`**:
Under `RiemannHypothesis` and symmetric zero-free gaps `0 < Δ ≤ 1 / 2` at `±V` (`2 ≤ |V|`),
for every `σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)`,
`‖deriv riemannZeta (σ + V * I) / riemannZeta (σ + V * I)‖ ≤`
`(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14`. -/
theorem norm_logDeriv_riemannZeta_le_on_Icc_left_of_gap (hRH : RiemannHypothesis) {V Δ σ : ℝ}
    (hV : 2 ≤ |V|) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap_pos : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|)
    (hgap_neg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - (-V)|)
    (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + (V : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (V : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14 := by
  set s : ℂ := (σ : ℂ) + (V : ℂ) * I
  have hV_ne : V ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hV; linarith
  have h_negV_ne : -V ≠ 0 := neg_ne_zero.mpr hV_ne
  have hs_int : ∀ n : ℤ, s ≠ (n : ℂ) := ofReal_add_mul_I_ne_intCast σ hV_ne
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ofReal_add_mul_I_ne_zero_of_gap hRH σ hV_ne hΔ_pos hgap_pos
  have h_fe := logDeriv_riemannZeta_one_sub hs_int hz
  rw [← logDeriv_apply]
  have h_1s_eq : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-V : ℝ) : ℂ) * I := by
    dsimp [s]; push_cast; ring
  have h_1σ_mem : 1 - σ ∈ Set.Icc (1 / 2 : ℝ) 2 :=
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have h1 : ‖-logDeriv riemannZeta (1 - s)‖ ≤
      (2048 / Δ ^ 4) * Real.log (14 * (1 + |V|)) + 1 / |V| := by
    rw [norm_neg, logDeriv_apply, h_1s_eq]
    have h_right := norm_logDeriv_riemannZeta_le_on_Icc_of_gap hRH h_negV_ne hΔ_pos hΔ_le
      hgap_neg h_1σ_mem
    rwa [abs_neg] at h_right
  have h_inv_V : 1 / |V| ≤ 1 / 2 :=
    one_div_le_one_div_of_le two_pos hV
  have h2 : ‖Complex.log (2 * π)‖ ≤ 3 := by
    have h_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have h_gt1 : 1 < 2 * Real.pi := by linarith [Real.two_le_pi]
    rw [show (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log h_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos h_gt1)]
    have h_le_exp : 2 * Real.pi ≤ Real.exp 3 := by
      have h_pi : Real.pi ≤ 4 := Real.pi_le_four
      have h_e1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h_e2 : (4 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
      have h_e3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by ring, Real.exp_add, Real.exp_add]
      nlinarith
    have h_log_le := Real.log_le_log h_pos h_le_exp
    rwa [Real.log_exp] at h_log_le
  have h3 : ‖Complex.digamma s‖ ≤ Real.log (14 * (1 + |V|)) + 6 := by
    have hd : ‖Complex.digamma s‖ ≤ Real.log (|V| + 2) + Real.pi + 11 / 6 :=
      norm_digamma_horizontal_le hσ hV
    have h_log_le : Real.log (|V| + 2) ≤ Real.log (14 * (1 + |V|)) :=
      Real.log_le_log (by positivity) (by linarith [abs_nonneg V])
    have h_pi : Real.pi ≤ 4 := Real.pi_le_four
    linarith
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 4 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_ofNat]
    have h_tan := norm_tan_pi_mul_div_two_le_two σ hV
    have h_pi : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [Real.pi_pos]
  rw [h_fe]
  have h_tri1 :=
    norm_add_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s)
      (π / 2 * Complex.tan (π * s / 2))
  have h_tri2 :=
    norm_sub_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π)) (Complex.digamma s)
  have h_tri3 := norm_add_le (-logDeriv riemannZeta (1 - s)) (Complex.log (2 * π))
  linarith

/-- **Full Horizontal Segment Bound on `‖deriv riemannZeta / riemannZeta‖`
Across `σ ∈ [-1 / 4, 2]`**:
Under `RiemannHypothesis` and symmetric zero-free gaps `0 < Δ ≤ 1 / 2` at `±V` (`2 ≤ |V|`),
for every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2`,
`‖deriv riemannZeta (σ + V * I) / riemannZeta (σ + V * I)‖ ≤`
`(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14`. -/
theorem norm_logDeriv_riemannZeta_le_on_Icc_neg_quarter_two_of_gap (hRH : RiemannHypothesis)
    {V Δ σ : ℝ} (hV : 2 ≤ |V|) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap_pos : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|)
    (hgap_neg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - (-V)|)
    (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) 2) :
    ‖deriv riemannZeta ((σ : ℂ) + (V : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (V : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14 := by
  rcases le_or_gt σ (1 / 2) with h_left | h_right
  · exact norm_logDeriv_riemannZeta_le_on_Icc_left_of_gap hRH hV hΔ_pos hΔ_le
      hgap_pos hgap_neg ⟨hσ.1, h_left⟩
  · have hV_ne : V ≠ 0 := by intro h0; rw [h0, abs_zero] at hV; linarith
    have h_r := norm_logDeriv_riemannZeta_le_on_Icc_of_gap hRH hV_ne hΔ_pos hΔ_le
      hgap_pos ⟨h_right.le, hσ.2⟩
    have h_inv_V : 1 / |V| ≤ 1 / 2 := one_div_le_one_div_of_le two_pos hV
    have h_log_pos : 0 ≤ Real.log (14 * (1 + |V|)) :=
      Real.log_nonneg (by linarith [abs_nonneg V])
    linarith

/-- **Simultaneous Top and Bottom Horizontal Segment Bounds at Zero-Free Height `U ≥ 2`**:
Under `RiemannHypothesis`, if `2 ≤ U`, `0 < Δ ≤ 1 / 2`, and every critical-line zero `ρ` satisfies
both `Δ ≤ |ρ.im - U|` and `Δ ≤ |ρ.im - (-U)|`, then for every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2`,
both `‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) / riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖` and
`‖deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) / riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖` are at most
`(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14`. -/
theorem norm_logDeriv_riemannZeta_top_and_bot_le_of_gap (hRH : RiemannHypothesis)
    {U Δ σ : ℝ} (hU : 2 ≤ U) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap_pos : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hgap_neg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - (-U)|)
    (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) 2) :
    ‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 ∧
    ‖deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 := by
  have hU_abs : |U| = U := abs_of_pos (by linarith)
  have hV_top : 2 ≤ |U| := by linarith
  have hV_bot : 2 ≤ |-U| := by rw [abs_neg]; linarith
  constructor
  · have h := norm_logDeriv_riemannZeta_le_on_Icc_neg_quarter_two_of_gap hRH hV_top hΔ_pos hΔ_le
      hgap_pos hgap_neg hσ
    rwa [hU_abs] at h
  · have h_sub_eq : (σ : ℂ) - (U : ℂ) * I = (σ : ℂ) + ((-U : ℝ) : ℂ) * I := by push_cast; ring
    rw [h_sub_eq]
    have h := norm_logDeriv_riemannZeta_le_on_Icc_neg_quarter_two_of_gap hRH hV_bot hΔ_pos hΔ_le
      hgap_neg (by simpa [neg_neg] using hgap_pos) hσ
    rwa [abs_neg, hU_abs] at h

/-- **Main Existential Theorem: Symmetric Zero-Free Height `U ∈ [T, T + 1]`
with Full Horizontal Bounds**:
For every `T ≥ 2`, under `RiemannHypothesis`, there exist `U ∈ Set.Icc T (T + 1)` and `Δ : ℝ`
such that:
1. `0 < Δ ≤ 1 / 2` and `1 / (314 * Real.log (T + 10)) ≤ Δ`,
2. Every critical-line zero `ρ` satisfies `Δ ≤ |(|ρ.im| - U)|`, `Δ ≤ |ρ.im - U|`,
   and `Δ ≤ |ρ.im - (-U)|`,
3. Every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2` satisfies both top and bottom horizontal bounds:
   `‖deriv riemannZeta (σ ± U * I) / riemannZeta (σ ± U * I)‖ ≤`
   `(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14`. -/
theorem exists_zero_free_height_with_horizontal_bounds (hRH : RiemannHypothesis)
    {T : ℝ} (hT : 2 ≤ T) :
    ∃ U ∈ Set.Icc T (T + 1), ∃ Δ : ℝ,
      0 < Δ ∧ Δ ≤ 1 / 2 ∧
      1 / (314 * Real.log (T + 10)) ≤ Δ ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
        Δ ≤ |(|ρ.im| - U)| ∧ Δ ≤ |ρ.im - U| ∧ Δ ≤ |ρ.im - (-U)|) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤
          (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 ∧
        ‖deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
            riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤
          (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14) := by
  obtain ⟨U, hU_mem, Δ, hΔ_pos, hΔ_le, hΔ_lb, hgap⟩ :=
    exists_zero_free_height_in_Icc (by linarith : 0 ≤ T)
  have hU_ge2 : 2 ≤ U := hT.trans hU_mem.1
  refine ⟨U, hU_mem, Δ, hΔ_pos, hΔ_le, hΔ_lb, hgap, ?_⟩
  intro σ hσ
  exact norm_logDeriv_riemannZeta_top_and_bot_le_of_gap hRH hU_ge2 hΔ_pos hΔ_le
    (fun ρ hζ hre ↦ (hgap ρ hζ hre).2.1)
    (fun ρ hζ hre ↦ (hgap ρ hζ hre).2.2) hσ

/-!
## Section 11: `nontrivialZetaZerosUpTo` and `O((log U) ^ 5)` Horizontal Bound Corollary
-/

end ConjectureMachines.Semantics.Riemann.HorizontalBounds
