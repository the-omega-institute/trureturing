/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Oliver Butterley
-/
module

public import D5.S3.Analytic.Probability.BirkhoffCondexp
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Banach-valued Birkhoff pointwise convergence over finite measures

This module ports the pinned Banach approximation argument and reuses the
repository's finite-measure scalar conditional-expectation theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Probability.BirkhoffBanachCondexp

section NormedAddCommGroup

open MeasureTheory Measure MeasurableSpace Filter Topology

universe u v
variable {α : Type u} {E : Type v} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → α} {g : α → E}

/-- The set of points where the Birkhoff average is `ε`-away from the conditional expectation for
infinitely many `n`. -/
def birkhoffExceptionalSet (μ : Measure α) (f : α → α) (g : α → E) (ε : ℝ) : Set α :=
  {x | ∃ᶠ n in atTop, ε ≤ dist (birkhoffAverage ℝ f g n x) (μ[g|invariants f] x)}

lemma norm_birkhoffAverage_le (f : α → α) (e : α → E) (n : ℕ) (x : α) :
    ‖birkhoffAverage ℝ f e n x‖ ≤ birkhoffAverage ℝ f (fun y ↦ ‖e y‖) n x := by
  unfold birkhoffAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  change (n : ℝ)⁻¹ * ‖birkhoffSum f e n x‖ ≤
    (n : ℝ)⁻¹ * birkhoffSum f (fun y ↦ ‖e y‖) n x
  gcongr
  exact norm_sum_le _ _

/-- The exceptional set for a fixed `ε` has measure at most `2 * δ / ε` whenever `g` is within `L¹`
distance `δ` of a function `s` already satisfying the theorem. -/
lemma measure_limsup_birkhoffAverage_sub_condExp_le (hf : MeasurePreserving f μ μ)
    (g_integrable : Integrable g μ) {s : α → E} (s_integrable : Integrable s μ)
    (s_tendsto : ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f s · x) atTop (𝓝 (μ[s | invariants f] x)))
    {ε δ : ℝ} (hε : 0 < ε) (hs_close : ∫ y, ‖g y - s y‖ ∂μ < δ) :
    ε * μ.real (birkhoffExceptionalSet μ f g ε) ≤ 2 * δ := by
  -- Write `e` for the small difference between `g` and `s`.
  set e : α → E := g - s with e_def
  have e_int : Integrable e μ := g_integrable.sub s_integrable
  have e_close : ∫ y, ‖e y‖ ∂μ < δ := hs_close
  have e_eq_sum : g = s + e := by simp [e_def]
  have e_tendsto := (D5.S3.Analytic.Probability.BirkhoffCondexp.birkhoff_conditional_expectation μ hf e_int.norm).1
  have hsplit : μ[g | invariants f] =ᵐ[μ] μ[s | invariants f] + μ[e | invariants f] :=
    e_eq_sum ▸ condExp_add s_integrable e_int _
  have hnorm : (‖μ[e | invariants f] ·‖) ≤ᵐ[μ] μ[(‖e ·‖) | invariants f] := norm_condExp_le _
  -- The exceptional set is a.e. a subset of a set whose measure we can control.
  have hsub : birkhoffExceptionalSet μ f g ε ≤ᵐ[μ] {x | ε ≤ 2 * μ[(‖e ·‖) | invariants f] x} := by
    filter_upwards [s_tendsto, e_tendsto, hsplit, hnorm] with x hxs hxe hxsplit hxnorm hmem
    -- The dominating sequence `‖Aₙ s - 𝔼 s‖ + (Aₙ ‖e‖ + 𝔼 ‖e‖)` converges to `2 * 𝔼 ‖e‖`: the
    -- first term tends to `0` by hypothesis on `s`, the second to `𝔼 ‖e‖` by the real case.
    have hu : Tendsto (fun n ↦ ‖birkhoffAverage ℝ f s n x - μ[s|invariants f] x‖ +
        (birkhoffAverage ℝ f (‖e ·‖) n x + μ[(‖e ·‖) | invariants f] x)) atTop
        (𝓝 (2 * μ[(‖e ·‖) | invariants f] x)) := by
      simpa [two_mul] using (hxs.sub_const (μ[s|invariants f] x)).norm.add
        (hxe.add_const (μ[(‖e ·‖) | invariants f] x))
    -- So `ε ≤ dist (Aₙ g) (𝔼 g)` infinitely often forces `ε ≤ 2 * 𝔼 ‖e‖`.
    refine isClosed_Ici.mem_of_frequently_of_tendsto (hmem.mono fun n hn ↦ hn.trans ?_) hu
    rw [hxsplit]
    simp only [e_eq_sum, birkhoffAverage_add, Pi.add_apply, dist_eq_norm, add_sub_add_comm]
    grw [norm_add_le]
    gcongr
    grw [norm_sub_le, norm_birkhoffAverage_le]
    gcongr
  calc
    _ ≤ ε * μ.real {x | ε ≤ 2 * μ[(‖e ·‖) | invariants f] x} := by
        exact mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)) hε.le
    _ ≤ 2 * δ := by
        -- By Markov's inequality, `μ[‖e‖|invariants f]` has integral `∫ ‖e‖ < δ`.
        have hnn := condExp_nonneg (m := invariants f) (ae_of_all μ fun y ↦ norm_nonneg (e y))
        apply mul_meas_ge_le_integral_of_nonneg (hnn.mono fun x hx ↦ mul_nonneg zero_le_two hx)
          (by fun_prop) ε |>.trans
        rw [integral_const_mul, integral_condExp (invariants_le f)]
        grw [e_close]

/-- The set of functions satisfying the pointwise theorem is closed in `L¹`: if for every `δ > 0`,
there is an integrable `s` satisfying the theorem with `∫ ‖g - s‖ < δ`, then `g` satisfies the
theorem. -/
lemma ae_tendsTo_birkhoffAverage_condExp_of_approx (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ)
    (h : ∀ δ : ℝ, 0 < δ → ∃ s : α → E, Integrable s μ ∧
      (∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f s · x) atTop (𝓝 (μ[s|invariants f] x))) ∧
      ∫ y, ‖g y - s y‖ ∂μ < δ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  have hzero : ∀ ε : ℝ, 0 < ε → μ (birkhoffExceptionalSet μ f g ε) = 0 := by
    intro ε hε
    apply le_antisymm
    · by_contra hnot
      have hneR : μ.real (birkhoffExceptionalSet μ f g ε) ≠ 0 := by
        intro hz
        apply hnot
        exact (measureReal_eq_zero_iff (μ := μ)).mp hz |>.le
      have hposR : 0 < μ.real (birkhoffExceptionalSet μ f g ε) :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hneR)
      let δ := ε * μ.real (birkhoffExceptionalSet μ f g ε) / 4
      have hδ : 0 < δ := by positivity
      obtain ⟨s, hs_int, hs_tendsto, hs_close⟩ := h δ hδ
      have hbound := measure_limsup_birkhoffAverage_sub_condExp_le hf hg hs_int hs_tendsto hε hs_close
      dsimp [δ] at hbound
      nlinarith
    · exact bot_le
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ∀ᶠ n in atTop, dist (birkhoffAverage ℝ f g n x) (μ[g|invariants f] x) < (k + 1 : ℝ)⁻¹ := by
    refine ae_all_iff.mpr fun k : ℕ ↦ ?_
    have hk : 0 < (k + 1 : ℝ)⁻¹ := by positivity
    have hmem : ∀ᵐ x ∂μ, x ∉ birkhoffExceptionalSet μ f g (k + 1 : ℝ)⁻¹ :=
      measure_eq_zero_iff_ae_notMem.mp (hzero _ hk)
    filter_upwards [hmem] with x hx
    have hx' : ¬ ∃ᶠ n in atTop,
        (k + 1 : ℝ)⁻¹ ≤ dist (birkhoffAverage ℝ f g n x) (μ[g|invariants f] x) := by
      simpa [birkhoffExceptionalSet] using hx
    filter_upwards [not_frequently.mp hx'] with n hn
    exact lt_of_not_ge hn
  filter_upwards [hall] with x hx
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hx k)
  exact ⟨N, fun n hn ↦ (hN n hn).trans (by simpa [one_div] using hk)⟩

/-- **Pointwise Ergodic Theorem**, also known as **Birkhoff's Ergodic Theorem**.

For an integrable function `g` with values in a Banach space, the time averages converge almost
everywhere to the conditional expectation of `g` with respect to the σ-algebra of invariant
sets. -/
public theorem ae_tendsTo_birkhoffAverage_condExp (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  apply hg.induction (P := _)
  case h_ind =>
    intro c s hs _
    let g y := s.indicator (fun _ ↦ (1 : ℝ)) y
    have hcoe : (s.indicator fun _ ↦ c) = fun y ↦ g y • c := by
      simpa using Set.indicator_smul_const s (fun _ ↦ (1 : ℝ)) c
    rw [hcoe]
    have hind_int : Integrable g μ := by fun_prop
    have hcx := condExp_smul_of_aestronglyMeasurable_right (μ := μ) (m := invariants f)
      hind_int (hind_int.smul_const c)
        (stronglyMeasurable_const.aestronglyMeasurable (m := invariants f))
    have havg : ∀ n x, birkhoffAverage ℝ f (fun y ↦ g y • c) n x =
        birkhoffAverage ℝ f g n x • c := by
      intro n x
      have hsum : ∀ t : Finset ℕ,
          (∑ k ∈ t, ((n : ℝ)⁻¹ • g (f^[k] x)) • c) =
            ((n : ℝ)⁻¹ • ∑ k ∈ t, g (f^[k] x)) • c := by
        intro t
        classical
        induction t using Finset.induction_on with
        | empty => simp
        | @insert a t ha ih =>
          simp only [Finset.sum_insert ha, ih]
          rw [← add_smul]
          congr 1
          ring
      simp only [birkhoffAverage, birkhoffSum]
      rw [Finset.smul_sum]
      simpa only [smul_assoc] using hsum (Finset.range n)
    change μ[(fun y ↦ g y • c) | invariants f] =ᵐ[μ]
        (μ[g | invariants f] • fun _ ↦ c) at hcx
    filter_upwards [((D5.S3.Analytic.Probability.BirkhoffCondexp.birkhoff_conditional_expectation
      μ hf hind_int).1), hcx] with x hx hcx
    have hlim : μ[(fun y ↦ g y • c) | invariants f] x =
        μ[g | invariants f] x • c := by simpa [Pi.smul_apply] using hcx
    rw [hlim]
    simpa only [havg] using hx.smul_const c
  case h_add =>
    intro g₁ g₂ _ g₁_int g₂_int hg₁ hg₂
    have hadd := condExp_add g₁_int g₂_int (invariants f)
    filter_upwards [hg₁, hg₂, hadd] with x hx₁ hx₂ hx₃
    rw [birkhoffAverage_add, hx₃]
    exact hx₁.add hx₂
  case h_closed =>
    refine isClosed_of_closure_subset fun g hg ↦ ?_
    refine ae_tendsTo_birkhoffAverage_condExp_of_approx hf (L1.integrable_coeFn g) fun δ hδ ↦ ?_
    obtain ⟨s, hs_mem, hs_dist⟩ := Metric.mem_closure_iff.mp hg δ hδ
    refine ⟨s, L1.integrable_coeFn s, hs_mem, ?_⟩
    calc ∫ y, ‖g y - s y‖ ∂μ
        = dist g s := by
          rw [dist_eq_norm, L1.norm_eq_integral_norm]
          exact integral_congr_ae ((AEEqFun.coeFn_sub (g : α →ₘ[μ] E) s).mono (by intros; simp [*]))
      _ < δ := hs_dist
  case h_ae =>
    intro g₁ g₂ hae g₁_int hg₁
    have h₁ := ae_all_iff.mpr <|
      hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq (R := ℝ) hae
    have h₂ := condExp_congr_ae (m := invariants f) hae
    filter_upwards [h₁, h₂, hg₁] with x hx₁ hx₂ hx₃
    conv in birkhoffAverage .. => rw [← hx₁]
    rwa [← hx₂]

section Invariant

omit [IsFiniteMeasure μ] [CompleteSpace E] in
public lemma comp_eq_condExp_invariants : μ[g | invariants f] ∘ f = μ[g | invariants f] := by
  borelize E
  exact comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable

end Invariant

end NormedAddCommGroup

end D5.S3.Analytic.Probability.BirkhoffBanachCondexp
