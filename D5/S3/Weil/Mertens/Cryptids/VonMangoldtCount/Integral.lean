/- GID: D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Integral
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Integral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids VonMangoldtCount analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/VonMangoldtCount.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount.Foundation

/-! Original VonMangoldtCount analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.VonMangoldtCount

open Complex Finset Filter MeasureTheory Set Asymptotics Metric MeromorphicOn
open scoped Real Topology ArithmeticFunction LSeries.notation

/-- Under `RiemannHypothesis`, `nontrivialZetaZerosUpTo T = ∅` for all `T ≤ 6`. -/
theorem nontrivialZetaZerosUpTo_eq_empty_of_le_six (hRH : RiemannHypothesis) {T : ℝ}
    (hT : T ≤ 6) :
    nontrivialZetaZerosUpTo T = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ρ hρ
  rw [mem_nontrivialZetaZerosUpTo] at hρ
  have h6 := six_lt_abs_im_of_riemannHypothesis hRH hρ.1
  linarith [hρ.2]

/-- `riemannZeta₁` is analytic on a neighborhood of every set `U : Set ℂ`. -/
theorem analyticOnNhd_riemannZeta₁ (U : Set ℂ) : AnalyticOnNhd ℂ riemannZeta₁ U :=
  (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ U)

/-- `riemannZeta₁` is analytic at every point `s : ℂ`. -/
theorem analyticAt_riemannZeta₁ (s : ℂ) : AnalyticAt ℂ riemannZeta₁ s :=
  analyticOnNhd_riemannZeta₁ univ s (mem_univ s)

/-- On the punctured plane `{1}ᶜ`, `riemannZeta` and `(s - 1)⁻¹ * riemannZeta₁ s` agree in a
neighborhood of any `s₀ ≠ 1`. -/
theorem riemannZeta_eventuallyEq_inv_sub_mul_riemannZeta₁ {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    riemannZeta =ᶠ[𝓝 s₀] fun s ↦ (s - 1)⁻¹ * riemannZeta₁ s := by
  filter_upwards [isOpen_ne.mem_nhds hs₀] with s hs
  exact riemannZeta_eq_inv_sub_mul hs

/-- **Equality of Analytic Orders Away from `s = 1`**:
For every `s₀ ≠ 1`, `analyticOrderAt riemannZeta s₀ = analyticOrderAt riemannZeta₁ s₀`. -/
theorem analyticOrderAt_riemannZeta_eq_analyticOrderAt_riemannZeta₁ {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    analyticOrderAt riemannZeta s₀ = analyticOrderAt riemannZeta₁ s₀ := by
  have h_inv_an : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1)⁻¹) s₀ :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs₀)
  have h_inv_ne : (s₀ - 1)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hs₀)
  have h_ord_inv : analyticOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) s₀ = 0 :=
    h_inv_an.analyticOrderAt_eq_zero.mpr h_inv_ne
  rw [analyticOrderAt_congr (riemannZeta_eventuallyEq_inv_sub_mul_riemannZeta₁ hs₀)]
  change analyticOrderAt ((fun s : ℂ ↦ (s - 1)⁻¹) * riemannZeta₁) s₀ =
    analyticOrderAt riemannZeta₁ s₀
  rw [analyticOrderAt_mul h_inv_an (analyticAt_riemannZeta₁ s₀), h_ord_inv, zero_add]

/-- For every `s₀ ≠ 1`, `analyticOrderNatAt riemannZeta s₀ = analyticOrderNatAt riemannZeta₁ s₀`. -/
theorem analyticOrderNatAt_riemannZeta_eq_analyticOrderNatAt_riemannZeta₁ {s₀ : ℂ}
    (hs₀ : s₀ ≠ 1) :
    analyticOrderNatAt riemannZeta s₀ = analyticOrderNatAt riemannZeta₁ s₀ := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_eq_analyticOrderAt_riemannZeta₁ hs₀]

/-- Helper lemma: for any `o : ℕ∞`, `(ENat.map (Nat.cast : ℕ → ℤ) o).untop₀ = (o.toNat : ℤ)`. -/
theorem enat_map_natCast_untop₀ (o : ℕ∞) :
    (ENat.map (Nat.cast : ℕ → ℤ) o).untop₀ = (o.toNat : ℤ) := by
  cases o <;> rfl

/-- **Divisor of `riemannZeta₁` Equals `analyticOrderNatAt riemannZeta`**:
For any set `U : Set ℂ` and any `ρ ∈ U` with `ρ ≠ 1`,
`divisor riemannZeta₁ U ρ = (analyticOrderNatAt riemannZeta ρ : ℤ)`. -/
theorem divisor_riemannZeta₁_eq_analyticOrderNatAt_riemannZeta (U : Set ℂ) {ρ : ℂ}
    (hρU : ρ ∈ U) (hρ1 : ρ ≠ 1) :
    divisor riemannZeta₁ U ρ = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
  rw [(analyticOnNhd_riemannZeta₁ U).divisor_apply hρU, enat_map_natCast_untop₀]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_eq_analyticOrderAt_riemannZeta₁ hρ1]

/-- `analyticOrderAt riemannZeta₁ s ≠ ⊤` for every `s : ℂ` (since `riemannZeta₁ 1 = 1 ≠ 0`). -/
theorem analyticOrderAt_riemannZeta₁_ne_top (s : ℂ) :
    analyticOrderAt riemannZeta₁ s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have h_zero : EqOn riemannZeta₁ 0 univ :=
    (analyticOnNhd_riemannZeta₁ univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ s) htop
  have h1 : riemannZeta₁ 1 = 0 := h_zero (mem_univ 1)
  rw [riemannZeta₁_one] at h1
  exact one_ne_zero h1

/-- Every nontrivial zero `ρ` of `riemannZeta` has multiplicity
`1 ≤ analyticOrderNatAt riemannZeta ρ`. -/
theorem one_le_analyticOrderNatAt_of_isNontrivialZetaZero {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    1 ≤ analyticOrderNatAt riemannZeta ρ := by
  rw [analyticOrderNatAt_riemannZeta_eq_analyticOrderNatAt_riemannZeta₁ hρ.2.2]
  have hζ₁ : riemannZeta₁ ρ = 0 := by
    have h := riemannZeta_eq_inv_sub_mul hρ.2.2
    rw [hρ.1] at h
    rcases mul_eq_zero.mp h.symm with hinv | h1
    · exact absurd hinv (inv_ne_zero (sub_ne_zero.mpr hρ.2.2))
    · exact h1
  have h_ne_zero : analyticOrderAt riemannZeta₁ ρ ≠ 0 :=
    (analyticAt_riemannZeta₁ ρ).analyticOrderAt_ne_zero.mpr hζ₁
  have h_ne_top : analyticOrderAt riemannZeta₁ ρ ≠ ⊤ :=
    analyticOrderAt_riemannZeta₁_ne_top ρ
  unfold analyticOrderNatAt
  cases h_ord : analyticOrderAt riemannZeta₁ ρ with
  | top => exact absurd h_ord h_ne_top
  | coe n =>
    rw [h_ord] at h_ne_zero
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h_ne_zero)

/-- For any finite set `S : Finset ℂ` and any nonnegative finitely-supported function `f : ℂ → ℤ`,
`∑ z ∈ S, f z ≤ ∑ᶠ u, f u`. -/
theorem sum_le_finsum_of_nonneg (S : Finset ℂ) {f : ℂ → ℤ}
    (hf : (Function.support f).Finite) (h0 : ∀ z, 0 ≤ f z) :
    ∑ z ∈ S, f z ≤ ∑ᶠ u, f u := by
  classical
  rw [finsum_eq_sum_of_support_toFinset_subset f hf (Finset.subset_union_right (s₁ := S))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ ↦ h0 z)

/-- **Multiplicity-Weighted Sum Bound via `divisor riemannZeta₁`**:
For any `S : Finset ℂ`, center `c : ℂ`, and radius `r : ℝ`, if every `ρ ∈ S` satisfies
`ρ ∈ closedBall c |r|` and `ρ ≠ 1`, then
`((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤`
`((∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) : ℝ)`. -/
theorem sum_analyticOrderNatAt_le_finsum_divisor_riemannZeta₁ (S : Finset ℂ) (c : ℂ) (r : ℝ)
    (hS : ∀ ρ ∈ S, ρ ∈ closedBall c |r| ∧ ρ ≠ 1) :
    ((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) : ℝ) := by
  have h_int :
      (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℤ)) ≤
        ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u := by
    have h_eq :
        ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℤ) =
          ∑ ρ ∈ S, divisor riemannZeta₁ (closedBall c |r|) ρ := by
      refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
      exact (divisor_riemannZeta₁_eq_analyticOrderNatAt_riemannZeta
        (closedBall c |r|) (hS ρ hρ).1 (hS ρ hρ).2).symm
    rw [h_eq]
    exact sum_le_finsum_of_nonneg S
      ((divisor riemannZeta₁ (closedBall c |r|)).finiteSupport (isCompact_closedBall c |r|))
      ((analyticOnNhd_riemannZeta₁ (closedBall c |r|)).divisor_nonneg)
  exact_mod_cast h_int

/-- **Nontrivial Zeros Between Heights `T` and `U`**:
The `Finset ℂ` of nontrivial zeros `ρ` of `riemannZeta` with `T < |ρ.im| ≤ U`. -/
noncomputable def nontrivialZetaZerosBetween (T U : ℝ) : Finset ℂ :=
  (nontrivialZetaZerosUpTo U).filter (fun ρ ↦ T < |ρ.im|)

@[simp]
theorem mem_nontrivialZetaZerosBetween {T U : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosBetween T U ↔
      IsNontrivialZetaZero ρ ∧ |ρ.im| ≤ U ∧ T < |ρ.im| := by
  simp [nontrivialZetaZerosBetween, and_assoc]

/-- Complementary filter characterization: for `T ≤ U`, filtering `nontrivialZetaZerosUpTo U`
by `¬ (T < |ρ.im|)` recovers `nontrivialZetaZerosUpTo T`. -/
theorem filter_not_lt_abs_im_nontrivialZetaZerosUpTo {T U : ℝ} (hTU : T ≤ U) :
    (nontrivialZetaZerosUpTo U).filter (fun ρ ↦ ¬ T < |ρ.im|) =
      nontrivialZetaZerosUpTo T := by
  ext ρ
  simp only [mem_filter, mem_nontrivialZetaZerosUpTo, not_lt]
  exact ⟨fun ⟨⟨h1, _⟩, h3⟩ ↦ ⟨h1, h3⟩, fun ⟨h1, h2⟩ ↦ ⟨⟨h1, h2.trans hTU⟩, h2⟩⟩

/-- Filtering `nontrivialZetaZerosBetween T U` by `|ρ.im| ≤ t` for `t ≤ U` recovers
`nontrivialZetaZerosBetween T t`. -/
theorem filter_abs_im_le_nontrivialZetaZerosBetween {T t U : ℝ} (htU : t ≤ U) :
    (nontrivialZetaZerosBetween T U).filter (fun ρ ↦ |ρ.im| ≤ t) =
      nontrivialZetaZerosBetween T t := by
  ext ρ
  simp only [mem_filter, mem_nontrivialZetaZerosBetween]
  exact ⟨fun ⟨⟨h1, _, h3⟩, h4⟩ ↦ ⟨h1, h4, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, h2.trans htU, h3⟩, h2⟩⟩

/-- For `T < γ ≤ U` and any function `g, g' : ℝ → ℝ` with `HasDerivAt g (g' t) t` on `[T, U]`
and `ContinuousOn g' (Set.Icc T U)`, the set integral of `(Set.Ici γ).indicator g'` over
`Set.Ioc T U` equals `g U - g γ`. -/
theorem setIntegral_indicator_deriv_eq_sub {T γ U : ℝ} (hγ : T < γ) (hγU : γ ≤ U)
    {g g' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc T U, HasDerivAt g (g' t) t)
    (hcont : ContinuousOn g' (Set.Icc T U)) :
    (∫ t in Set.Ioc T U, (Set.Ici γ).indicator g' t) = g U - g γ := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hinter : Set.Ioc T U ∩ Set.Ici γ = Set.Icc γ U := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ ↦ ⟨h3, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨⟨hγ.trans_le h1, h2⟩, h1⟩⟩
  rw [hinter, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hγU]
  have hsub : Set.Icc γ U ⊆ Set.Icc T U := Set.Icc_subset_Icc_left hγ.le
  have hd_sub : ∀ t ∈ Set.uIcc γ U, HasDerivAt g (g' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hγU] at ht
    exact hderiv t (hsub ht)
  have hint_sub : IntervalIntegrable g' volume γ U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hγU]
    exact (hcont.mono hsub).integrableOn_Icc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd_sub hint_sub

/-- Integrability of `(Set.Ici γ).indicator g'` on `Set.Ioc T U` for `T < γ` when `g'` is
continuous on `Set.Icc T U`. -/
theorem integrableOn_indicator_of_continuousOn {T γ U : ℝ} (hγ : T < γ)
    {g' : ℝ → ℝ} (hcont : ContinuousOn g' (Set.Icc T U)) :
    IntegrableOn ((Set.Ici γ).indicator g') (Set.Ioc T U) := by
  rw [integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet]
  have hinter : Set.Ici γ ∩ Set.Ioc T U = Set.Icc γ U := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    exact ⟨fun ⟨h1, _, h3⟩ ↦ ⟨h1, h3⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, hγ.trans_le h1, h2⟩⟩
  rw [hinter]
  exact (hcont.mono (Set.Icc_subset_Icc_left hγ.le)).integrableOn_Icc

/-- Derivative of `1 / t` at `t ≠ 0` is `-1 / t ^ 2`. -/
theorem hasDerivAt_one_div {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 1 / x) (-1 / t ^ 2) t := by
  simp only [one_div]
  exact (hasDerivAt_inv ht).congr_deriv (by ring)

/-- **Closed-Form Evaluation of the Quadratic Riemann–von Mangoldt Stieltjes Integral**:
For `0 < t₀ ≤ T` and any constants `a, C, D : ℝ`,
$$\int_{t_0}^T \frac{a t \log t + C t + D}{t^2} \, dt
  = \left(\frac{a}{2} (\log T)^2 + C \log T - \frac{D}{T}\right)
    - \left(\frac{a}{2} (\log t_0)^2 + C \log t_0 - \frac{D}{t_0}\right).$$ -/
theorem intervalIntegral_riemannVonMangoldt_div_sq {t₀ T : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (a C D : ℝ) :
    (∫ t : ℝ in t₀..T, (a * t * Real.log t + C * t + D) / t ^ 2) =
      (a / 2 * (Real.log T) ^ 2 + C * Real.log T - D / T) -
        (a / 2 * (Real.log t₀) ^ 2 + C * Real.log t₀ - D / t₀) := by
  have hderiv : ∀ t ∈ Set.uIcc t₀ T,
      HasDerivAt (fun x : ℝ ↦ a / 2 * (Real.log x) ^ 2 + C * Real.log x - D * x⁻¹)
        ((a * t * Real.log t + C * t + D) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le ht₀T] at ht
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hd_log_sq :
        HasDerivAt (fun x : ℝ ↦ (Real.log x) ^ 2) (2 * (Real.log t) ^ (2 - 1) * t⁻¹) t :=
      (Real.hasDerivAt_log ht_ne).pow 2
    have hd1 : HasDerivAt (fun x : ℝ ↦ a / 2 * (Real.log x) ^ 2)
        (a / 2 * (2 * (Real.log t) ^ (2 - 1) * t⁻¹)) t :=
      hd_log_sq.const_mul (a / 2)
    have hd2 : HasDerivAt (fun x : ℝ ↦ C * Real.log x) (C * t⁻¹) t :=
      (Real.hasDerivAt_log ht_ne).const_mul C
    have hd3 : HasDerivAt (fun x : ℝ ↦ D * x⁻¹) (D * -(t ^ 2)⁻¹) t :=
      (hasDerivAt_inv ht_ne).const_mul D
    refine ((hd1.add hd2).sub hd3).congr_deriv ?_
    field_simp [ht_ne]
    ring
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 2) volume t₀ T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀T]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 2) (pow_ne_zero 2 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- **Multiplicity-Weighted Zero-Counting Function `N_w(U)`**:
The sum of the analytic multiplicities `analyticOrderNatAt riemannZeta ρ` over all nontrivial
zeros `ρ` of `riemannZeta` with `|ρ.im| ≤ U`. -/
noncomputable def weightedZeroCountingFunction (U : ℝ) : ℕ :=
  ∑ ρ ∈ nontrivialZetaZerosUpTo U, analyticOrderNatAt riemannZeta ρ

/-- The open half-plane `{z : ℂ | -3 < z.re}` is preconnected. -/
theorem isPreconnected_neg_three_lt_re : IsPreconnected {z : ℂ | -3 < z.re} := by
  have hConv : Convex ℝ {z : ℂ | -3 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp only [zero_mul, zero_add] at hab ⊢
      subst hab
      simpa using hy
    · rcases eq_or_lt_of_le hb with rfl | hb_pos
      · simp only [zero_mul, add_zero] at hab ⊢
        subst hab
        simpa using hx
      · have h1 : a * (-3) < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
        have h2 : b * (-3) < b * y.re := mul_lt_mul_of_pos_left hy hb_pos
        linarith
  exact hConv.isPreconnected

/-- **Cleared-Denominator Quartic Euler–Maclaurin Identity on `-3 < s.re`**:
For every `s : ℂ` with `-3 < s.re`,
$$24\,\operatorname{riemannZeta}_1(s)
  = 2 (s + 2) (s + 3) - (s - 1) s (s + 1) (s + 2) (s + 3)
      \operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3)).$$ -/
theorem twenty_four_mul_riemannZeta₁_eq_of_neg_three_lt_re {s : ℂ} (hs : -3 < s.re) :
    24 * riemannZeta₁ s =
      2 * (s + 2) * (s + 3) -
        (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * mellin quarticKernel (-(s + 3)) := by
  have hOpen : IsOpen {z : ℂ | -3 < z.re} := isOpen_lt continuous_const continuous_re
  have hAn1 : AnalyticOnNhd ℂ (fun z : ℂ ↦ 24 * riemannZeta₁ z) {z : ℂ | -3 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z _ ↦ ?_) hOpen
    exact ((differentiableAt_const 24).mul (differentiable_riemannZeta₁ z)).differentiableWithinAt
  have hAn2 : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ 2 * (z + 2) * (z + 3) -
        (z - 1) * z * (z + 1) * (z + 2) * (z + 3) * mellin quarticKernel (-(z + 3)))
      {z : ℂ | -3 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.sub ?_ ?_)
    · exact (((differentiableAt_const 2).mul (differentiableAt_id.add_const 2)).mul
        (differentiableAt_id.add_const 3))
    · refine DifferentiableAt.mul ?_ ?_
      · exact (((((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
          (differentiableAt_id.add_const 1)).mul (differentiableAt_id.add_const 2)).mul
          (differentiableAt_id.add_const 3))
      · exact (differentiableAt_mellin_quarticKernel
          (by simp only [neg_re, add_re]; norm_num; linarith [show -3 < z.re from hz])).comp z
          (differentiableAt_id.add_const 3).neg
  have hEv : (fun z : ℂ ↦ 24 * riemannZeta₁ z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ 2 * (z + 2) * (z + 3) -
        (z - 1) * z * (z + 1) * (z + 2) * (z + 3) * mellin quarticKernel (-(z + 3))) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := by intro h; subst h; simp at hz
    have hz1_sub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hz0 : z ≠ 0 := by intro h; subst h; norm_num at hz
    have hza1 : z + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 1 < z.re from hz]
    have hza2 : z + 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 1 < z.re from hz]
    have hza3 : z + 3 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 1 < z.re from hz]
    have hzeta1 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ hz1_sub, one_mul]
    rw [mellin_quarticKernel_neg_add_three_eq_of_one_lt_re hz, hzeta1]
    field_simp [hz1_sub, hz0, hza1, hza2, hza3]
    ring
  exact hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 isPreconnected_neg_three_lt_re
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | -3 < z.re}) hEv hs

/-- **Uniform Norm Bound on `mellin quarticKernel (-(s + 3))` for `-3 < s.re`**:
For every `s : ℂ` with `-3 < s.re`,
`‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / (16 * (s.re + 3))`. -/
theorem norm_mellin_quarticKernel_neg_add_three_le_of_neg_three_lt_re {s : ℂ} (hs : -3 < s.re) :
    ‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / (16 * (s.re + 3)) := by
  rw [mellin_quarticKernel_neg_add_three_eq]
  have hexp_lt : -(s.re + 4) < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ ↦ (1 / 16 : ℝ) * t ^ (-(s.re + 4))) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hexp_lt zero_lt_one).const_mul (1 / 16)
  have hnorm_le :
      ‖∫ t in Ioi (1 : ℝ),
        (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4))‖ ≤
      ∫ t in Ioi (1 : ℝ), (1 / 16 : ℝ) * t ^ (-(s.re + 4)) := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, h1⟩ := quartic_floor_bounds ht_pos.le
    rw [norm_mul, norm_real, Real.norm_of_nonneg h0, norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hre : (-(s + 4)).re = -(s.re + 4) := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
  refine hnorm_le.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp_lt zero_lt_one, Real.one_rpow]
  have hs3 : s.re + 3 ≠ 0 := by linarith
  have h_exp_add : -(s.re + 4) + 1 = -(s.re + 3) := by ring
  rw [h_exp_add]
  field_simp [hs3]

/-- For every `s : ℂ` with `-14 / 5 ≤ s.re`,
`‖mellin quarticKernel (-(s + 3))‖ ≤ 5 / 16`. -/
theorem norm_mellin_quarticKernel_neg_add_three_le_five_sixteenths {s : ℂ} (hs : -14 / 5 ≤ s.re) :
    ‖mellin quarticKernel (-(s + 3))‖ ≤ 5 / 16 := by
  have hs3 : -3 < s.re := by linarith
  refine (norm_mellin_quarticKernel_neg_add_three_le_of_neg_three_lt_re hs3).trans ?_
  have h_pos : (0 : ℝ) < 16 / 5 := by norm_num
  have h_le : (16 / 5 : ℝ) ≤ 16 * (s.re + 3) := by linarith
  have h_div := one_div_le_one_div_of_le h_pos h_le
  exact h_div.trans_eq (by norm_num)

/-- Summability of `n ↦ 1 / (n + 1 : ℝ) ^ 2` with sum `π ^ 2 / 6`. -/
theorem hasSum_one_div_nat_add_one_sq :
    HasSum (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- Summability of `n ↦ 1 / (n + 2 : ℝ) ^ 2` with sum `π ^ 2 / 6 - 1`. -/
theorem hasSum_one_div_nat_add_two_sq :
    HasSum (fun n : ℕ ↦ 1 / (n + 2 : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_one_div_nat_add_one_sq
  convert h using 1
  · ext n
    push_cast
    ring
  · norm_num

/-- Explicit numerical bound `π ^ 2 / 6 - 1 ≤ 3 / 4` (using `Real.pi_lt_d2 : π < 3.15`). -/
theorem pi_sq_div_six_sub_one_le_three_fourths :
    Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
  have hpi_pos : 0 ≤ Real.pi := Real.pi_pos.le
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  nlinarith

/-- For `1 < s.re`, `riemannZeta s - 1 = ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s`. -/
theorem riemannZeta_sub_one_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s - 1 = ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s := by
  have h_sum : Summable (fun n : ℕ ↦ 1 / (n + 1 : ℂ) ^ s) := by
    have h0 : Summable (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    simpa using (summable_nat_add_iff 1).mpr h0
  have h_zeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  rw [h_zeta, h_sum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, one_cpow, div_one, add_sub_cancel_left]
  refine tsum_congr fun n ↦ ?_
  push_cast
  ring_nf

/-- For every `s : ℂ` with `2 ≤ s.re` and every `n : ℕ`,
`‖1 / (n + 2 : ℂ) ^ s‖ ≤ 1 / (n + 2 : ℝ) ^ 2`. -/
theorem norm_one_div_nat_add_two_cpow_le {s : ℂ} (hs : 2 ≤ s.re) (n : ℕ) :
    ‖1 / (n + 2 : ℂ) ^ s‖ ≤ 1 / (n + 2 : ℝ) ^ 2 := by
  have hn_pos : (0 : ℝ) < n + 2 := by positivity
  have hn_ge_one : (1 : ℝ) ≤ n + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h_cast : (n + 2 : ℂ) = ((n + 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [norm_div, norm_one, h_cast, norm_cpow_eq_rpow_re_of_pos hn_pos]
  have hrpow : (n + 2 : ℝ) ^ (2 : ℝ) ≤ (n + 2 : ℝ) ^ s.re :=
    Real.rpow_le_rpow_of_exponent_le hn_ge_one hs
  have hrpow_sq : (n + 2 : ℝ) ^ (2 : ℝ) = (n + 2 : ℝ) ^ 2 := Real.rpow_two (n + 2 : ℝ)
  rw [← hrpow_sq]
  exact one_div_le_one_div_of_le (by positivity) hrpow

/-- For every `s : ℂ` with `2 ≤ s.re`, `‖riemannZeta s - 1‖ ≤ 3 / 4`. -/
theorem norm_riemannZeta_sub_one_le_three_fourths {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 / 4 := by
  have hs1 : 1 < s.re := by linarith
  rw [riemannZeta_sub_one_eq_tsum hs1]
  have h_sum_real : Summable (fun n : ℕ ↦ 1 / (n + 2 : ℝ) ^ 2) :=
    hasSum_one_div_nat_add_two_sq.summable
  have h_sum_norm : Summable (fun n : ℕ ↦ ‖1 / (n + 2 : ℂ) ^ s‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_one_div_nat_add_two_cpow_le hs) h_sum_real
  calc
    ‖∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / (n + 2 : ℂ) ^ s‖ := norm_tsum_le_tsum_norm h_sum_norm
    _ ≤ ∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2 :=
        h_sum_norm.tsum_le_tsum (norm_one_div_nat_add_two_cpow_le hs) h_sum_real
    _ = Real.pi ^ 2 / 6 - 1 := hasSum_one_div_nat_add_two_sq.tsum_eq
    _ ≤ 3 / 4 := pi_sq_div_six_sub_one_le_three_fourths

/-- For every `s : ℂ` with `2 ≤ s.re`, `1 / 4 ≤ ‖riemannZeta s‖`. -/
theorem one_fourth_le_norm_riemannZeta_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 4 ≤ ‖riemannZeta s‖ := by
  have h_norm := norm_riemannZeta_sub_one_le_three_fourths hs
  have h_tri : ‖(1 : ℂ)‖ ≤ ‖riemannZeta s‖ + ‖riemannZeta s - 1‖ := by
    have h := norm_sub_le (riemannZeta s) (riemannZeta s - 1)
    simpa using h
  rw [norm_one] at h_tri
  linarith

/-- For every `y : ℝ`,
`1 / 4 * ‖(1 : ℂ) + (y : ℂ) * I‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖`. -/
theorem one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I (y : ℝ) :
    1 / 4 * ‖(1 : ℂ) + (y : ℂ) * I‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ := by
  have hc_ne_one : (2 : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hc_sub : (2 : ℂ) + (y : ℂ) * I - 1 = (1 : ℂ) + (y : ℂ) * I := by ring
  have hc_sub_ne : (2 : ℂ) + (y : ℂ) * I - 1 ≠ 0 := sub_ne_zero.mpr hc_ne_one
  have hzeta1 : riemannZeta₁ (2 + (y : ℂ) * I) =
      ((1 : ℂ) + (y : ℂ) * I) * riemannZeta (2 + (y : ℂ) * I) := by
    rw [riemannZeta_eq_inv_sub_mul hc_ne_one, ← hc_sub, ← mul_assoc,
      mul_inv_cancel₀ hc_sub_ne, one_mul]
  rw [hzeta1, norm_mul, mul_comm (1 / 4)]
  exact mul_le_mul_of_nonneg_left
    (one_fourth_le_norm_riemannZeta_of_two_le_re (by simp))
    (norm_nonneg _)

/-- For every `y : ℝ`, `1 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖` and `|y| ≤ ‖(1 : ℂ) + (y : ℂ) * I‖`. -/
theorem one_and_abs_le_norm_one_add_mul_I (y : ℝ) :
    1 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ ∧ |y| ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ := by
  refine ⟨?_, ?_⟩
  · have h := abs_re_le_norm ((1 : ℂ) + (y : ℂ) * I)
    simpa using h
  · have h := abs_im_le_norm ((1 : ℂ) + (y : ℂ) * I)
    simpa using h

/-- For every `y : ℝ`, `riemannZeta₁ (2 + (y : ℂ) * I) ≠ 0`. -/
theorem riemannZeta₁_two_add_mul_I_ne_zero (y : ℝ) :
    riemannZeta₁ (2 + (y : ℂ) * I) ≠ 0 := by
  have h1 := (one_and_abs_le_norm_one_add_mul_I y).1
  have h2 := one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I y
  exact norm_pos_iff.mp (by linarith)

/-- For `8 ≤ |y|` and `z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)`,
`-14 / 5 ≤ z.re`, `‖z - 1‖ ≤ (8 / 5) * ‖(1 : ℂ) + (y : ℂ) * I‖`, and for `0 ≤ a ≤ 3`,
`‖z + (a : ℂ)‖ ≤ (3 / 2) * (|y| + 4)`. -/
theorem closedBall_two_add_mul_I_bounds {y : ℝ} (hy : 8 ≤ |y|) {z : ℂ}
    (hz : z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)) :
    -14 / 5 ≤ z.re ∧
      ‖z - 1‖ ≤ (8 / 5) * ‖(1 : ℂ) + (y : ℂ) * I‖ ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 3 → ‖z + (a : ℂ)‖ ≤ (3 / 2) * (|y| + 4) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hy_norm : 8 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ :=
    hy.trans (one_and_abs_le_norm_one_add_mul_I y).2
  refine ⟨?_, ?_, ?_⟩
  · have hre_diff : |(z - (2 + (y : ℂ) * I)).re| ≤ 24 / 5 :=
      (abs_re_le_norm _).trans hz
    have hre_eq : (z - (2 + (y : ℂ) * I)).re = z.re - 2 := by simp
    rw [hre_eq] at hre_diff
    linarith [(abs_le.mp hre_diff).1]
  · have h_decomp : z - 1 = (z - (2 + (y : ℂ) * I)) + ((1 : ℂ) + (y : ℂ) * I) := by ring
    have h_tri : ‖z - 1‖ ≤ ‖z - (2 + (y : ℂ) * I)‖ + ‖(1 : ℂ) + (y : ℂ) * I‖ := by
      rw [h_decomp]
      exact norm_add_le _ _
    linarith
  · intro a ha0 ha3
    have h_decomp : z + (a : ℂ) =
        (z - (2 + (y : ℂ) * I)) + (((2 + a : ℝ) : ℂ) + (y : ℂ) * I) := by
      push_cast
      ring
    have h_tri1 : ‖z + (a : ℂ)‖ ≤
        ‖z - (2 + (y : ℂ) * I)‖ + ‖((2 + a : ℝ) : ℂ) + (y : ℂ) * I‖ := by
      rw [h_decomp]
      exact norm_add_le _ _
    have h_tri2 : ‖((2 + a : ℝ) : ℂ) + (y : ℂ) * I‖ ≤ (2 + a) + |y| := by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖((2 + a : ℝ) : ℂ)‖ = 2 + a := by
        rw [norm_real, Real.norm_of_nonneg (by linarith)]
      have h2 : ‖(y : ℂ) * I‖ = |y| := by
        rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      linarith
    linarith

/-- **Key Ratio Bound on `closedBall (2 + (y : ℂ) * I) (24 / 5)` for `8 ≤ |y|`**:
For every `y : ℝ` with `8 ≤ |y|` and every `z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)`,
`‖riemannZeta₁ z‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ * (|y| + 4) ^ 4`. -/
theorem norm_riemannZeta₁_le_on_closedBall_two_add_mul_I {y : ℝ} (hy : 8 ≤ |y|) {z : ℂ}
    (hz : z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)) :
    ‖riemannZeta₁ z‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ * (|y| + 4) ^ 4 := by
  obtain ⟨hz_re, hz1, hza⟩ := closedBall_two_add_mul_I_bounds hy hz
  have hz0 : ‖z‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 0 le_rfl (by norm_num)
  have hza1 : ‖z + 1‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 1 (by norm_num) (by norm_num)
  have hza2 : ‖z + 2‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 2 (by norm_num) (by norm_num)
  have hza3 : ‖z + 3‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 3 (by norm_num) le_rfl
  have hmellin : ‖mellin quarticKernel (-(z + 3))‖ ≤ 5 / 16 :=
    norm_mellin_quarticKernel_neg_add_three_le_five_sixteenths hz_re
  have hid := congrArg norm (twenty_four_mul_riemannZeta₁_eq_of_neg_three_lt_re
    (by linarith : -3 < z.re))
  rw [norm_mul, norm_ofNat] at hid
  have h_rhs :
      ‖2 * (z + 2) * (z + 3) -
        (z - 1) * z * (z + 1) * (z + 2) * (z + 3) * mellin quarticKernel (-(z + 3))‖ ≤
        2 * ‖z + 2‖ * ‖z + 3‖ +
          ‖z - 1‖ * ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ * ‖mellin quarticKernel (-(z + 3))‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · simp only [norm_mul, norm_ofNat, le_rfl]
    · simp only [norm_mul, le_rfl]
  let B : ℝ := (3 / 2) * (|y| + 4)
  let K : ℝ := ‖(1 : ℂ) + (y : ℂ) * I‖
  have hB_nonneg : 0 ≤ B := by positivity
  have hK_ge : 8 ≤ K := hy.trans (one_and_abs_le_norm_one_add_mul_I y).2
  have h_prod2 : ‖z + 2‖ * ‖z + 3‖ ≤ B ^ 2 := by
    rw [sq]
    exact mul_le_mul hza2 hza3 (norm_nonneg _) hB_nonneg
  have h_prod4 : ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ ≤ B ^ 4 := by
    have hp12 : ‖z‖ * ‖z + 1‖ ≤ B ^ 2 := by
      rw [sq]
      exact mul_le_mul hz0 hza1 (norm_nonneg _) hB_nonneg
    calc
      ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖
        = (‖z‖ * ‖z + 1‖) * (‖z + 2‖ * ‖z + 3‖) := by ring
      _ ≤ B ^ 2 * B ^ 2 := mul_le_mul hp12 h_prod2 (by positivity) (by positivity)
      _ = B ^ 4 := by ring
  have h_prod6 :
      ‖z - 1‖ * ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ * ‖mellin quarticKernel (-(z + 3))‖ ≤
        (8 / 5) * K * B ^ 4 * (5 / 16) := by
    have hp5 : ‖z - 1‖ * (‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖) ≤ (8 / 5) * K * B ^ 4 :=
      mul_le_mul hz1 h_prod4 (by positivity) (by positivity)
    calc
      ‖z - 1‖ * ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ * ‖mellin quarticKernel (-(z + 3))‖
        = (‖z - 1‖ * (‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖)) * ‖mellin quarticKernel (-(z + 3))‖ := by
          ring
      _ ≤ ((8 / 5) * K * B ^ 4) * (5 / 16) :=
          mul_le_mul hp5 hmellin (norm_nonneg _) (by positivity)
  have h_y4_sq : 144 ≤ (|y| + 4) ^ 2 := by nlinarith
  have h_B2_le : 2 * B ^ 2 ≤ (1 / 2) * K * (|y| + 4) ^ 4 := by
    have hB2_eq : 2 * B ^ 2 = (9 / 2) * (|y| + 4) ^ 2 := by
      dsimp only [B]
      ring
    rw [hB2_eq]
    have h1 : (9 / 2) * (|y| + 4) ^ 2 * 144 ≤ (9 / 2) * (|y| + 4) ^ 2 * (|y| + 4) ^ 2 :=
      mul_le_mul_of_nonneg_left h_y4_sq (by positivity)
    have h2 : (|y| + 4) ^ 4 ≤ (1 / 8) * K * (|y| + 4) ^ 4 := by
      have hK8 : 1 ≤ (1 / 8) * K := by linarith
      nlinarith [pow_nonneg (by positivity : 0 ≤ |y| + 4) 4]
    nlinarith
  have h_B4_eq : (8 / 5) * K * B ^ 4 * (5 / 16) = (81 / 32) * K * (|y| + 4) ^ 4 := by
    dsimp only [B]
    ring
  have h24_le : 24 * ‖riemannZeta₁ z‖ ≤ 6 * K * (|y| + 4) ^ 4 := by
    have h_K_y4 : 0 ≤ K * (|y| + 4) ^ 4 := by positivity
    linarith
  have h_zeta1_c := one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I y
  have h_y4_nonneg : 0 ≤ (|y| + 4) ^ 4 := by positivity
  have h_c_mul :
      (1 / 4 * K) * (|y| + 4) ^ 4 ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ * (|y| + 4) ^ 4 :=
    mul_le_mul_of_nonneg_right h_zeta1_c h_y4_nonneg
  linarith

/-- **Nontrivial Zeros in the Height-4 Window `[y - 2, y + 2]`**:
The `Finset ℂ` of nontrivial zeros `ρ` of `riemannZeta` with `y - 2 ≤ ρ.im ≤ y + 2`. -/
noncomputable def nontrivialZetaZerosInFourWindow (y : ℝ) : Finset ℂ :=
  (nontrivialZetaZerosUpTo (|y| + 2)).filter (fun ρ ↦ y - 2 ≤ ρ.im ∧ ρ.im ≤ y + 2)

@[simp]
theorem mem_nontrivialZetaZerosInFourWindow {y : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosInFourWindow y ↔
      IsNontrivialZetaZero ρ ∧ y - 2 ≤ ρ.im ∧ ρ.im ≤ y + 2 := by
  simp only [nontrivialZetaZerosInFourWindow, mem_filter, mem_nontrivialZetaZerosUpTo]
  refine ⟨fun ⟨⟨h1, _⟩, h3, h4⟩ ↦ ⟨h1, h3, h4⟩, fun ⟨h1, h3, h4⟩ ↦ ⟨⟨h1, ?_⟩, h3, h4⟩⟩
  rw [abs_le]
  have hy := le_abs_self y
  have hny := neg_le_abs y
  constructor <;> linarith

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ ∈ nontrivialZetaZerosInFourWindow y`
lies in `closedBall (2 + (y : ℂ) * I) |(5 / 2 : ℝ)|`. -/
theorem mem_closedBall_two_add_mul_I_five_halves_of_riemannHypothesis
    (hRH : RiemannHypothesis) (y : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZetaZerosInFourWindow y) :
    ρ ∈ closedBall (2 + (y : ℂ) * I) |(5 / 2 : ℝ)| := by
  rw [mem_nontrivialZetaZerosInFourWindow] at hρ
  obtain ⟨h_nt, h_lo, h_hi⟩ := hρ
  have hre : ρ.re = 1 / 2 := hRH ρ h_nt.1 h_nt.2.1 h_nt.2.2
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have h_re_sub : (ρ - (2 + (y : ℂ) * I)).re = -3 / 2 := by simp [hre]; ring
  have h_im_sub : (ρ - (2 + (y : ℂ) * I)).im = ρ.im - y := by simp
  rw [h_re_sub, h_im_sub]
  have him_sq : (ρ.im - y) ^ 2 ≤ 2 ^ 2 := by nlinarith
  nlinarith

/-- Explicit rational lower bound `41 / 64 ≤ Real.log (48 / 25)` proved via
`((64 / 63 : ℝ) ^ 41) ≤ 48 / 25` and `Real.one_sub_inv_le_log_of_pos`. -/
theorem forty_one_div_sixty_four_le_log_forty_eight_div_twenty_five :
    (41 / 64 : ℝ) ≤ Real.log (48 / 25) := by
  have h_step : (1 / 64 : ℝ) ≤ Real.log (64 / 63) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 64 / 63)
    norm_num at h
    exact h
  have h_pow : ((64 / 63 : ℝ) ^ 41) ≤ 48 / 25 := by norm_num
  have h_log_pow : Real.log ((64 / 63 : ℝ) ^ 41) ≤ Real.log (48 / 25) :=
    Real.log_le_log (by positivity) h_pow
  rw [Real.log_pow] at h_log_pow
  linarith

/-- Explicit rational upper bound `Real.log 2 ≤ 31 / 44` proved via
`2 ≤ (45 / 44 : ℝ) ^ 31` and `Real.log_le_sub_one_of_pos`. -/
theorem log_two_le_forty_four_div_sixty_three :
    Real.log 2 ≤ 31 / 44 := by
  have h_step : Real.log (45 / 44) ≤ 1 / 44 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 45 / 44)
    linarith
  have h_pow : (2 : ℝ) ≤ (45 / 44 : ℝ) ^ 31 := by norm_num
  have h_log_pow : Real.log 2 ≤ Real.log ((45 / 44 : ℝ) ^ 31) :=
    Real.log_le_log (by norm_num) h_pow
  rw [Real.log_pow] at h_log_pow
  linarith

/-- **Local Height-4 Window Multiplicity Bound via Jensen's Formula (`r = 5 / 2`, `R = 24 / 5`)**:
Under `RiemannHypothesis`, for every `y : ℝ` with `8 ≤ |y|`,
$$\sum_{\rho \in \text{nontrivialZetaZerosInFourWindow } y}
  \operatorname{analyticOrderNatAt}\;\zeta\;\rho \le \frac{256}{41} \log(|y| + 4).$$ -/
theorem sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 8 ≤ |y|) :
    ((∑ ρ ∈ nontrivialZetaZerosInFourWindow y, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      (256 / 41) * Real.log (|y| + 4) := by
  let c : ℂ := 2 + (y : ℂ) * I
  let M : ℝ := ‖riemannZeta₁ c‖ * (|y| + 4) ^ 4
  have hc_norm_ge : 2 ≤ ‖riemannZeta₁ c‖ := by
    have h1 := (one_and_abs_le_norm_one_add_mul_I y).2
    have h2 := one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I y
    linarith
  have hc_pos : 0 < ‖riemannZeta₁ c‖ := by linarith
  have hy4_ge : 12 ≤ |y| + 4 := by linarith
  have hy4_pos : 0 < |y| + 4 := by linarith
  have hM_ge_one : 1 ≤ M := by
    dsimp only [M]
    have hp : (1 : ℝ) ≤ (|y| + 4) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  have hf_bound : ∀ z ∈ sphere c |(24 / 5 : ℝ)|, ‖riemannZeta₁ z‖ ≤ M := by
    intro z hz
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 24 / 5)] at hz
    exact norm_riemannZeta₁_le_on_closedBall_two_add_mul_I hy (sphere_subset_closedBall hz)
  have h_div :
      ((∑ ρ ∈ nontrivialZetaZerosInFourWindow y, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |(5 / 2 : ℝ)|) u : ℤ) : ℝ) := by
    refine sum_analyticOrderNatAt_le_finsum_divisor_riemannZeta₁
      (nontrivialZetaZerosInFourWindow y) c (5 / 2) fun ρ hρ ↦ ?_
    exact ⟨mem_closedBall_two_add_mul_I_five_halves_of_riemannHypothesis hRH y hρ,
      (mem_nontrivialZetaZerosInFourWindow.mp hρ).1.2.2⟩
  have h_jensen :=
    (analyticOnNhd_riemannZeta₁ (closedBall c |(24 / 5 : ℝ)|)).sum_divisor_le
      (r := 5 / 2) (by norm_num) (by norm_num) hM_ge_one (riemannZeta₁_two_add_mul_I_ne_zero y)
      hf_bound
  refine (h_div.trans h_jensen).trans ?_
  have h_log_num : Real.log (M / ‖riemannZeta₁ c‖) = 4 * Real.log (|y| + 4) := by
    dsimp only [M]
    rw [mul_div_cancel_left₀ _ hc_pos.ne', Real.log_pow]
    ring
  have h_ratio : (24 / 5 : ℝ) / (5 / 2) = 48 / 25 := by norm_num
  rw [h_log_num, h_ratio]
  have h_log_nonneg : 0 ≤ 4 * Real.log (|y| + 4) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have h_den := forty_one_div_sixty_four_le_log_forty_eight_div_twenty_five
  have h_div_le :
      4 * Real.log (|y| + 4) / Real.log (48 / 25) ≤ 4 * Real.log (|y| + 4) / (41 / 64) :=
    div_le_div_of_nonneg_left h_log_nonneg (by norm_num) h_den
  refine h_div_le.trans_eq ?_
  ring

/-- Subadditivity of `ℕ`-valued `Finset.sum` over binary union. -/
theorem sum_union_le_nat {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (f : α → ℕ) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  omega

/-- Subadditivity of `ℕ`-valued `Finset.sum` over `Finset.biUnion` on `Finset.range n`. -/
theorem sum_biUnion_range_le_nat {α : Type*} [DecidableEq α] (n : ℕ) (g : ℕ → Finset α)
    (f : α → ℕ) :
    ∑ x ∈ (Finset.range n).biUnion g, f x ≤ ∑ k ∈ Finset.range n, ∑ x ∈ g k, f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
    have h_u := sum_union_le_nat (g n) ((Finset.range n).biUnion g) f
    omega

/-- Under `RiemannHypothesis`, for any `t : ℝ`, every `ρ ∈ nontrivialZetaZerosUpTo t` belongs to one
of the `2 * (⌊(t - 6) / 4⌋₊ + 1)` height-4 windows centered at `±(8 + 4 * k)` for
`k < ⌊(t - 6) / 4⌋₊ + 1`. -/
theorem nontrivialZetaZerosUpTo_subset_biUnion_fourWindows
    (hRH : RiemannHypothesis) (t : ℝ) :
    nontrivialZetaZerosUpTo t ⊆
      (Finset.range (⌊(t - 6) / 4⌋₊ + 1)).biUnion
        (fun k ↦ nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)) ∪
          nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ)))) := by
  intro ρ hρ
  rw [mem_nontrivialZetaZerosUpTo] at hρ
  obtain ⟨h_nt, him_le⟩ := hρ
  have him_gt : 6 < |ρ.im| := six_lt_abs_im_of_riemannHypothesis hRH h_nt
  let k : ℕ := ⌊(|ρ.im| - 6) / 4⌋₊
  have hk_nonneg : 0 ≤ (|ρ.im| - 6) / 4 := by linarith
  have hk_le_floor : k ≤ ⌊(t - 6) / 4⌋₊ :=
    Nat.floor_le_floor (by linarith)
  have hk_lt : k < ⌊(t - 6) / 4⌋₊ + 1 := Nat.lt_succ_of_le hk_le_floor
  have hk_lo : (k : ℝ) ≤ (|ρ.im| - 6) / 4 := Nat.floor_le hk_nonneg
  have hk_hi : (|ρ.im| - 6) / 4 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [Finset.mem_biUnion]
  refine ⟨k, Finset.mem_range.mpr hk_lt, ?_⟩
  rw [Finset.mem_union, mem_nontrivialZetaZerosInFourWindow, mem_nontrivialZetaZerosInFourWindow]
  rcases le_or_gt 0 ρ.im with him_nonneg | him_neg
  · left
    rw [abs_of_nonneg him_nonneg] at hk_lo hk_hi
    refine ⟨h_nt, by linarith, by linarith⟩
  · right
    rw [abs_of_neg him_neg] at hk_lo hk_hi
    refine ⟨h_nt, by linarith, by linarith⟩

end ConjectureMachines.Semantics.Riemann.VonMangoldtCount
