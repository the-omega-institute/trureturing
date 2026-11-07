/- GID: D5/S3/Quantum/Analysis/DysonPhillipsPerturbation
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/DysonPhillipsPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyson–Phillips construction and continuous Volterra uniqueness on complex Banach spaces. -/

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license; see docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
Authors: Zayn Blore
Source: zblore/csd-lean4 at ca3edfd7a5576d6c4e188501f9abb7c3f38ccd7f,
CsdLean4/Mathlib/Analysis/Semigroup/BoundedPerturbation.lean.
MODIFIED: selected only the Dyson–Phillips and Volterra core, replaced the donor
semigroup framework by the native real/NNReal bundle, and added a full real-time
existence and uniqueness endpoint. The original complex maps remain in all integrals.
The donor pins Lean 4.34.0 / Mathlib 5ed2965; this source uses the repository's
Lean 4.35.0 / Mathlib 56a0058. No external package dependency is introduced.
Retire this adaptation when the actually adopted host Mathlib pin provides
equivalent strongly continuous Banach bounded-perturbation statements.
-/
import D5.S3.Quantum.Analysis.ContractionSemigroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-! # Dyson–Phillips bounded perturbation

The complex Banach construction assumes strong vector continuity only.
-/

open scoped Nat Topology
open NormedSpace MeasureTheory intervalIntegral Filter

namespace D5.S3.Quantum.Analysis.DysonPhillipsPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private abbrev Input (S : ℝ → E →L[ℂ] E) : Prop :=
  (∀ t, t ≤ 0 → S t = 1) ∧
  (∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t) ∧
  (∀ t, ‖S t‖ ≤ 1) ∧ ∀ x, Continuous fun t => S t x

omit [CompleteSpace E] in
private noncomputable def native {S : ℝ → E →L[ℂ] E} (hS : Input S) :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E where
  operator q := (S (q : ℝ)).restrictScalars ℝ
  operator_zero := by ext x; exact congrArg (fun A : E →L[ℂ] E => A x) (hS.1 0 le_rfl)
  operator_add s t := by
    ext x
    exact congrArg (fun A : E →L[ℂ] E => A x) (hS.2.1 s t s.coe_nonneg t.coe_nonneg)
  opNorm_le_one q := by rw [ContinuousLinearMap.norm_restrictScalars]; exact hS.2.2.1 q
  continuous_orbit x := (hS.2.2.2 x).comp NNReal.continuous_coe

omit [CompleteSpace E] in
private theorem native_apply {S : ℝ → E →L[ℂ] E} (hS : Input S) (t : ℝ) (x : E) :
    native hS (Real.toNNReal t) x = S t x := by
  change S (Real.toNNReal t : ℝ) x = S t x
  by_cases ht : 0 ≤ t
  · rw [Real.coe_toNNReal t ht]
  · rw [Real.toNNReal_of_nonpos (le_of_not_ge ht), NNReal.coe_zero,
      hS.1 0 le_rfl, hS.1 t (le_of_not_ge ht)]

omit [CompleteSpace E] in
private theorem norm_apply_le {S : ℝ → E →L[ℂ] E} (hS : Input S) (t : ℝ) (x : E) :
    ‖S t x‖ ≤ ‖x‖ := by
  rw [← native_apply hS t x]
  exact (native hS).norm_apply_le _ _

omit [CompleteSpace E] in
private theorem continuous_action {S : ℝ → E →L[ℂ] E} (hS : Input S) :
    Continuous fun p : ℝ × E => S p.1 p.2 := by
  have h := (native hS).continuous_operator_apply
    (continuous_real_toNNReal.comp continuous_fst) continuous_snd
  change Continuous (fun p : ℝ × E => native hS (Real.toNNReal p.1) p.2) at h
  simpa only [native_apply] using h

variable (S : ℝ → E →L[ℂ] E) (B : E →L[ℂ] E)

/-- **The Dyson terms**: `D₀(t) ψ = S t ψ`, `Dₙ₊₁(t) ψ = ∫₀ᵗ S (t − s) (B (Dₙ(s) ψ)) ds`. -/
noncomputable def dysonTerm : ℕ → ℝ → E → E
  | 0 => fun t ψ => S t ψ
  | n + 1 => fun t ψ => ∫ s in (0 : ℝ)..t, S (t - s) (B (dysonTerm n s ψ))

omit [CompleteSpace E] in
private theorem dysonTerm_zero (t : ℝ) (ψ : E) : dysonTerm S B 0 t ψ = S t ψ := rfl

omit [CompleteSpace E] in
private theorem dysonTerm_succ (n : ℕ) (t : ℝ) (ψ : E) :
    dysonTerm S B (n + 1) t ψ = ∫ s in (0 : ℝ)..t, S (t - s) (B (dysonTerm S B n s ψ)) := rfl

variable {S}

omit [CompleteSpace E] in
private theorem continuous_dysonTerm (hS : Input S) (n : ℕ) (ψ : E) :
    Continuous fun t => dysonTerm S B n t ψ := by
  induction n with
  | zero => exact hS.2.2.2 ψ
  | succ n ih =>
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun t s => S (t - s) (B (dysonTerm S B n s ψ))) ?_ continuous_id
    exact (continuous_action hS).comp
      ((continuous_fst.sub continuous_snd).prodMk (B.continuous.comp (ih.comp continuous_snd)))

omit [CompleteSpace E] in
private theorem continuous_dysonTerm_integrand (hS : Input S) (n : ℕ) (t : ℝ) (ψ : E) :
    Continuous fun s => S (t - s) (B (dysonTerm S B n s ψ)) :=
  (continuous_action hS).comp
    ((continuous_const.sub continuous_id).prodMk
      (B.continuous.comp (continuous_dysonTerm B hS n ψ)))

omit [CompleteSpace E] in
private theorem dysonTerm_add (hS : Input S) (n : ℕ) (t : ℝ) (ψ χ : E) :
    dysonTerm S B n t (ψ + χ) = dysonTerm S B n t ψ + dysonTerm S B n t χ := by
  induction n generalizing t with
  | zero => simp only [dysonTerm_zero, map_add]
  | succ n ih =>
    simp only [dysonTerm_succ, ih, map_add]
    exact intervalIntegral.integral_add
      ((continuous_dysonTerm_integrand B hS n t ψ).intervalIntegrable _ _)
      ((continuous_dysonTerm_integrand B hS n t χ).intervalIntegrable _ _)

omit [CompleteSpace E] in
private theorem dysonTerm_smul (n : ℕ) (t : ℝ) (c : ℂ) (ψ : E) :
    dysonTerm S B n t (c • ψ) = c • dysonTerm S B n t ψ := by
  induction n generalizing t with
  | zero => simp only [dysonTerm_zero, map_smul]
  | succ n ih =>
    simp only [dysonTerm_succ, ih, map_smul]
    exact intervalIntegral.integral_smul c _

omit [CompleteSpace E] in
/-- ★ `‖Dₙ(t) ψ‖ ≤ (‖B‖ t)ⁿ / n! · ‖ψ‖` for `0 ≤ t`. -/
private theorem norm_dysonTerm_le (hS : Input S) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    ‖dysonTerm S B n t ψ‖ ≤ (‖B‖ * t) ^ n / n ! * ‖ψ‖ := by
  induction n generalizing t with
  | zero =>
    rw [dysonTerm_zero]
    simpa using (norm_apply_le hS) t ψ
  | succ n ih =>
    rw [dysonTerm_succ]
    have hint : ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖S (t - s) (B (dysonTerm S B n s ψ))‖ ≤ ‖B‖ * ((‖B‖ * s) ^ n / n ! * ‖ψ‖) := by
      intro s hs
      calc ‖S (t - s) (B (dysonTerm S B n s ψ))‖
          ≤ ‖B (dysonTerm S B n s ψ)‖ := (norm_apply_le hS) _ _
        _ ≤ ‖B‖ * ‖dysonTerm S B n s ψ‖ := B.le_opNorm _
        _ ≤ ‖B‖ * ((‖B‖ * s) ^ n / n ! * ‖ψ‖) := by gcongr; exact ih hs.1
    calc ‖∫ s in (0 : ℝ)..t, S (t - s) (B (dysonTerm S B n s ψ))‖
        ≤ ∫ s in (0 : ℝ)..t, ‖S (t - s) (B (dysonTerm S B n s ψ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, ‖B‖ * ((‖B‖ * s) ^ n / n ! * ‖ψ‖) := by
          refine intervalIntegral.integral_mono_on ht
            ((continuous_dysonTerm_integrand B hS n t ψ).norm.intervalIntegrable _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _) hint
      _ = (‖B‖ * t) ^ (n + 1) / (n + 1)! * ‖ψ‖ := by
          simp_rw [mul_pow, mul_div_assoc, mul_assoc]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_pow,
            Nat.factorial_succ]
          push_cast
          field_simp
          ring

omit [CompleteSpace E] in
private theorem summable_norm_dysonTerm (hS : Input S) {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    Summable fun n => ‖dysonTerm S B n t ψ‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_dysonTerm_le B hS n ht ψ)
    ((Real.summable_pow_div_factorial (‖B‖ * t)).mul_right _)

private theorem summable_dysonTerm (hS : Input S) {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    Summable fun n => dysonTerm S B n t ψ :=
  (summable_norm_dysonTerm B hS ht ψ).of_norm

variable (S) in
/-- **The Dyson sum** `𝒮(t) ψ = ∑' n, Dₙ(t) ψ`, at time `max t 0` (the identity for `t ≤ 0`). -/
noncomputable def dysonSum (t : ℝ) (ψ : E) : E := ∑' n, dysonTerm S B n (max t 0) ψ

omit [CompleteSpace E] in
private theorem dysonSum_of_nonneg {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    dysonSum S B t ψ = ∑' n, dysonTerm S B n t ψ := by
  rw [dysonSum, max_eq_left ht]

private theorem hasSum_dysonTerm (hS : Input S) {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    HasSum (fun n => dysonTerm S B n t ψ) (dysonSum S B t ψ) := by
  rw [dysonSum_of_nonneg B ht]
  exact (summable_dysonTerm B hS ht ψ).hasSum

omit [CompleteSpace E] in
/-- ★ `‖𝒮(t) ψ‖ ≤ e^{‖B‖ t} ‖ψ‖` for `0 ≤ t`. -/
private theorem norm_dysonSum_le (hS : Input S) {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    ‖dysonSum S B t ψ‖ ≤ Real.exp (‖B‖ * t) * ‖ψ‖ := by
  rw [dysonSum_of_nonneg B ht]
  have hsum := (Real.summable_pow_div_factorial (‖B‖ * t)).mul_right ‖ψ‖
  calc ‖∑' n, dysonTerm S B n t ψ‖
      ≤ ∑' n, ‖dysonTerm S B n t ψ‖ :=
        norm_tsum_le_tsum_norm (summable_norm_dysonTerm B hS ht ψ)
    _ ≤ ∑' n, (‖B‖ * t) ^ n / n ! * ‖ψ‖ :=
        (summable_norm_dysonTerm B hS ht ψ).tsum_le_tsum
          (fun n => norm_dysonTerm_le B hS n ht ψ) hsum
    _ = Real.exp (‖B‖ * t) * ‖ψ‖ := by
        rw [tsum_mul_right, Real.exp_eq_exp_ℝ, ← (expSeries_div_hasSum_exp (‖B‖ * t)).tsum_eq]

private theorem dysonSum_add (hS : Input S) (t : ℝ) (ψ χ : E) :
    dysonSum S B t (ψ + χ) = dysonSum S B t ψ + dysonSum S B t χ := by
  simp only [dysonSum, dysonTerm_add B hS]
  exact (summable_dysonTerm B hS (le_max_right t 0) ψ).tsum_add
    (summable_dysonTerm B hS (le_max_right t 0) χ)

omit [CompleteSpace E] in
private theorem dysonSum_smul (t : ℝ) (c : ℂ) (ψ : E) :
    dysonSum S B t (c • ψ) = c • dysonSum S B t ψ := by
  simp only [dysonSum, dysonTerm_smul B]
  exact tsum_const_smul'' c

omit [CompleteSpace E] in
private theorem dysonSum_zero (hS : Input S) (ψ : E) : dysonSum S B 0 ψ = ψ := by
  rw [dysonSum_of_nonneg B le_rfl]
  have h : ∀ n, dysonTerm S B n 0 ψ = if n = 0 then ψ else 0 := by
    intro n
    cases n with
    | zero => simp [dysonTerm_zero, (hS.1 0 le_rfl)]
    | succ n => simp [dysonTerm_succ]
  simp_rw [h]
  exact tsum_ite_eq 0 (fun _ => ψ)

/-- The Dyson sum is continuous in time, by uniform convergence of the series on `[0, T]`. -/
private theorem continuousOn_dysonSum_Iic (hS : Input S) (ψ : E) (T : ℝ) :
    ContinuousOn (fun t => dysonSum S B t ψ) (Set.Iic T) := by
  simp only [dysonSum]
  refine continuousOn_tsum (u := fun n => (‖B‖ * max T 0) ^ n / n ! * ‖ψ‖)
    (fun n => ((continuous_dysonTerm B hS n ψ).comp (continuous_id.max continuous_const)).continuousOn)
    ((Real.summable_pow_div_factorial (‖B‖ * max T 0)).mul_right _) ?_
  intro n t ht
  refine le_trans (norm_dysonTerm_le B hS n (le_max_right t 0) ψ) ?_
  gcongr
  exact Set.mem_Iic.mp ht

private theorem continuous_dysonSum (hS : Input S) (ψ : E) :
    Continuous fun t => dysonSum S B t ψ := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (continuousOn_dysonSum_Iic B hS ψ (t + 1)).continuousAt (Iic_mem_nhds (by linarith))

/-! ### The Duhamel equation -/

/-- The integrand of the Duhamel equation is continuous. -/
private theorem continuous_dysonSum_integrand (hS : Input S) (t : ℝ) (ψ : E) :
    Continuous fun s => S (t - s) (B (dysonSum S B s ψ)) :=
  (continuous_action hS).comp
    ((continuous_const.sub continuous_id).prodMk (B.continuous.comp (continuous_dysonSum B hS ψ)))

/-- ★ **The Duhamel equation**: `𝒮(t) ψ = S t ψ + ∫₀ᵗ S (t − s) (B (𝒮(s) ψ)) ds` for `0 ≤ t`. -/
private theorem dysonSum_eq_add_integral (hS : Input S) {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    dysonSum S B t ψ = S t ψ + ∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s ψ)) := by
  rw [dysonSum_of_nonneg B ht, (summable_dysonTerm B hS ht ψ).tsum_eq_zero_add, dysonTerm_zero]
  congr 1
  have hsum : HasSum (fun n => ∫ s in (0 : ℝ)..t, S (t - s) (B (dysonTerm S B n s ψ)))
      (∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s ψ))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun n s => ‖B‖ * ((‖B‖ * s) ^ n / n ! * ‖ψ‖))
      (fun n => (continuous_dysonTerm_integrand B hS n t ψ).aestronglyMeasurable) ?_ ?_ ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun s hs => ?_
      rw [Set.uIoc_of_le ht] at hs
      calc ‖S (t - s) (B (dysonTerm S B n s ψ))‖
          ≤ ‖B (dysonTerm S B n s ψ)‖ := (norm_apply_le hS) _ _
        _ ≤ ‖B‖ * ‖dysonTerm S B n s ψ‖ := B.le_opNorm _
        _ ≤ ‖B‖ * ((‖B‖ * s) ^ n / n ! * ‖ψ‖) := by
            gcongr; exact norm_dysonTerm_le B hS n hs.1.le ψ
    · exact Filter.Eventually.of_forall fun s _ =>
        ((Real.summable_pow_div_factorial _).mul_right _).mul_left _
    · have : (fun s : ℝ => ∑' n, ‖B‖ * ((‖B‖ * s) ^ n / n ! * ‖ψ‖))
          = fun s => ‖B‖ * (Real.exp (‖B‖ * s) * ‖ψ‖) := by
        funext s
        rw [tsum_mul_left, tsum_mul_right, Real.exp_eq_exp_ℝ,
          ← (expSeries_div_hasSum_exp (‖B‖ * s)).tsum_eq]
      rw [this]
      exact (by fun_prop : Continuous fun s : ℝ => ‖B‖ * (Real.exp (‖B‖ * s) * ‖ψ‖))
        |>.intervalIntegrable _ _
    · refine Filter.Eventually.of_forall fun s hs => ?_
      rw [Set.uIoc_of_le ht] at hs
      exact ((S (t - s)).comp B).hasSum (hasSum_dysonTerm B hS hs.1.le ψ)
  exact hsum.tsum_eq

omit [CompleteSpace E] in
/-- The Volterra integral of the bound `(‖B‖ s)ⁿ / n!` is the next term of the exponential
series. -/
private theorem integral_norm_pow_div_factorial (n : ℕ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, ‖B‖ * ((‖B‖ * s) ^ n / n !) = (‖B‖ * t) ^ (n + 1) / (n + 1)! := by
  simp_rw [mul_pow, mul_div_assoc]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- ★ **Uniqueness for the Duhamel equation.** A continuous solution of
`X t = S t ψ + ∫₀ᵗ S (t − s) (B (X s)) ds` on `[0, T]` is the Dyson sum. -/
private theorem eq_dysonSum_of_duhamel (hS : Input S) {T : ℝ} {X : ℝ → E}
    (hX : ContinuousOn X (Set.Icc 0 T)) (ψ : E)
    (hX' : ∀ t ∈ Set.Icc (0 : ℝ) T, X t = S t ψ + ∫ s in (0 : ℝ)..t, S (t - s) (B (X s))) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, X t = dysonSum S B t ψ := by
  set Y : ℝ → E := fun t => X t - dysonSum S B t ψ with hY
  have hYc : ContinuousOn Y (Set.Icc 0 T) := hX.sub (continuous_dysonSum B hS ψ).continuousOn
  have hYint : ∀ t ∈ Set.Icc (0 : ℝ) T, ContinuousOn (fun s => S (t - s) (B (Y s))) (Set.Icc 0 t) :=
    fun t ht => (continuous_action hS).comp_continuousOn
      ((continuous_const.sub continuous_id).continuousOn.prodMk
        (B.continuous.comp_continuousOn (hYc.mono (Set.Icc_subset_Icc le_rfl ht.2))))
  have hYeq : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t = ∫ s in (0 : ℝ)..t, S (t - s) (B (Y s)) := by
    intro t ht
    have hint : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        S (t - s) (B (Y s)) = S (t - s) (B (X s)) - S (t - s) (B (dysonSum S B s ψ)) := by
      intro s _
      simp only [hY, map_sub]
    have hXint : IntervalIntegrable (fun s => S (t - s) (B (X s))) volume 0 t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le ht.1]
      exact (continuous_action hS).comp_continuousOn
        ((continuous_const.sub continuous_id).continuousOn.prodMk
          (B.continuous.comp_continuousOn (hX.mono (Set.Icc_subset_Icc le_rfl ht.2))))
    rw [hY]
    simp only
    rw [hX' t ht, dysonSum_eq_add_integral B hS ht.1 ψ, intervalIntegral.integral_congr hint,
      intervalIntegral.integral_sub hXint
        ((continuous_dysonSum_integrand B hS t ψ).intervalIntegrable _ _)]
    abel
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hYc
  have hbound : ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Y t‖ ≤ M * ((‖B‖ * t) ^ n / n !) := by
    intro n
    induction n with
    | zero => intro t ht; simpa using hM t ht
    | succ n ih =>
      intro t ht
      rw [hYeq t ht]
      calc ‖∫ s in (0 : ℝ)..t, S (t - s) (B (Y s))‖
          ≤ ∫ s in (0 : ℝ)..t, ‖S (t - s) (B (Y s))‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht.1
        _ ≤ ∫ s in (0 : ℝ)..t, M * (‖B‖ * ((‖B‖ * s) ^ n / n !)) := by
            refine intervalIntegral.integral_mono_on ht.1
              ((hYint t ht).norm.intervalIntegrable_of_Icc ht.1)
              (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
            calc ‖S (t - s) (B (Y s))‖ ≤ ‖B (Y s)‖ := (norm_apply_le hS) _ _
              _ ≤ ‖B‖ * ‖Y s‖ := B.le_opNorm _
              _ ≤ ‖B‖ * (M * ((‖B‖ * s) ^ n / n !)) := by
                  gcongr; exact ih s ⟨hs.1, le_trans hs.2 ht.2⟩
              _ = M * (‖B‖ * ((‖B‖ * s) ^ n / n !)) := by ring
        _ = M * ((‖B‖ * t) ^ (n + 1) / (n + 1)!) := by
            rw [intervalIntegral.integral_const_mul, integral_norm_pow_div_factorial]
  intro t ht
  have hlim : Tendsto (fun n : ℕ => M * ((‖B‖ * t) ^ n / n !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (‖B‖ * t)).const_mul M
  have hYt : ‖Y t‖ ≤ 0 := ge_of_tendsto' hlim fun n => hbound n t ht
  have h0 : Y t = 0 := norm_le_zero_iff.mp hYt
  rw [hY] at h0
  exact sub_eq_zero.mp h0

/-- ★★ **The semigroup law**: `𝒮(t + s) ψ = 𝒮(t) (𝒮(s) ψ)` for `s, t ≥ 0`, by uniqueness for the
Duhamel equation. -/
private theorem dysonSum_add_time (hS : Input S) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ψ : E) : dysonSum S B (t + s) ψ = dysonSum S B t (dysonSum S B s ψ) := by
  refine eq_dysonSum_of_duhamel B hS (T := t) (X := fun u => dysonSum S B (u + s) ψ)
    ((continuous_dysonSum B hS ψ).comp (continuous_add_const s)).continuousOn _ ?_ t ⟨ht, le_rfl⟩
  intro u hu
  have hu0 : 0 ≤ u + s := add_nonneg hu.1 hs
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := (0 : ℝ))
    (b := s) (c := u + s) ((continuous_dysonSum_integrand B hS (u + s) ψ).intervalIntegrable _ _)
    ((continuous_dysonSum_integrand B hS (u + s) ψ).intervalIntegrable _ _)
  have hfirst : ∫ r in (0 : ℝ)..s, S (u + s - r) (B (dysonSum S B r ψ))
      = S u (∫ r in (0 : ℝ)..s, S (s - r) (B (dysonSum S B r ψ))) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
      ((continuous_dysonSum_integrand B hS s ψ).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hs] at hr
    rw [show u + s - r = u + (s - r) by ring, hS.2.1 u (s - r) hu.1 (by linarith [hr.2]),
      mul_apply_eq_comp]
  have hsecond : ∫ r in (0 : ℝ)..u, S (u - r) (B (dysonSum S B (r + s) ψ))
      = ∫ r in s..u + s, S (u + s - r) (B (dysonSum S B r ψ)) := by
    have h := intervalIntegral.integral_comp_add_right
      (fun r => S (u + s - r) (B (dysonSum S B r ψ))) (a := 0) (b := u) s
    rw [zero_add] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun r _ => ?_
    congr 2
    ring
  show dysonSum S B (u + s) ψ
    = S u (dysonSum S B s ψ) + ∫ r in (0 : ℝ)..u, S (u - r) (B (dysonSum S B (r + s) ψ))
  rw [dysonSum_eq_add_integral B hS hu0 ψ, hS.2.1 u s hu.1 hs, ← hsplit, hfirst, hsecond,
    mul_apply_eq_comp, ← add_assoc, ← map_add, ← dysonSum_eq_add_integral B hS hs ψ]

/-! ### The perturbed semigroup as an operator -/

omit [CompleteSpace E] in
private theorem dysonSum_max (t : ℝ) (ψ : E) : dysonSum S B (max t 0) ψ = dysonSum S B t ψ := by
  rw [dysonSum, dysonSum, max_eq_left (le_max_right t 0)]

/-- ★ **The perturbed semigroup** `𝒮(t)` as a continuous linear map, `‖𝒮(t)‖ ≤ e^{‖B‖ t}`. -/
private noncomputable def perturbed (hS : Input S)
    (B : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := dysonSum S B t
      map_add' := dysonSum_add B hS t
      map_smul' := fun c ψ => by simp [dysonSum_smul] }
    (Real.exp (‖B‖ * max t 0)) fun ψ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← dysonSum_max B t ψ]
      exact norm_dysonSum_le B hS (le_max_right t 0) ψ

private theorem perturbed_apply (hS : Input S) (t : ℝ) (ψ : E) :
    perturbed hS B t ψ = dysonSum S B t ψ := rfl

private theorem norm_perturbed_le (hS : Input S) (t : ℝ) :
    ‖perturbed hS B t‖ ≤ Real.exp (‖B‖ * max t 0) :=
  LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _

/-- ★★ The perturbed semigroup is a semigroup: `𝒮(t + s) = 𝒮(t) * 𝒮(s)` for `s, t ≥ 0`. -/
private theorem perturbed_add (hS : Input S) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    perturbed hS B (t + s) = perturbed hS B t * perturbed hS B s :=
  ContinuousLinearMap.ext fun ψ => by
    rw [mul_apply_eq_comp, perturbed_apply, perturbed_apply, perturbed_apply,
      dysonSum_add_time B hS hs ht]

private theorem continuous_perturbed_apply (hS : Input S) (ψ : E) :
    Continuous fun t => perturbed hS B t ψ :=
  continuous_dysonSum B hS ψ


/-- The bounded-perturbation evolution, with uniqueness requiring only the three
Volterra conditions and with local curve uniqueness on every real horizon. -/
theorem bounded_perturbation
    (S : ℝ → E →L[ℂ] E) (B : E →L[ℂ] E)
    (h0 : ∀ t, t ≤ 0 → S t = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hnorm : ∀ t, ‖S t‖ ≤ 1)
    (hcont : ∀ x, Continuous fun t => S t x) :
    (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ x : E,
      ‖dysonTerm S B n t x‖ ≤ (‖B‖ * t) ^ n / n ! * ‖x‖) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ x : E, Summable fun n => dysonTerm S B n t x) ∧
    ∃ U : ℝ → E →L[ℂ] E,
      (∀ t, t ≤ 0 → U t = 1) ∧
      (∀ x, Continuous fun t => U t x) ∧
      (∀ t, 0 ≤ t → ∀ x, U t x = S t x +
        ∫ r in (0 : ℝ)..t, S (t - r) (B (U r x))) ∧
      (∀ V : ℝ → E →L[ℂ] E,
        ((∀ t, t ≤ 0 → V t = 1) ∧
         (∀ x, Continuous fun t => V t x) ∧
         (∀ t, 0 ≤ t → ∀ x, V t x = S t x +
           ∫ r in (0 : ℝ)..t, S (t - r) (B (V r x)))) → V = U) ∧
      (∀ t x, U t x = ∑' n, dysonTerm S B n (max t 0) x) ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → U (s + t) = (U s).comp (U t)) ∧
      (∀ t, ‖U t‖ ≤ Real.exp (‖B‖ * max t 0)) ∧
      (∀ (T : ℝ) (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, X t = S t x +
          ∫ r in (0 : ℝ)..t, S (t - r) (B (X r))) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, X t = U t x) := by
  let hS : Input S := ⟨h0, hadd, hnorm, hcont⟩
  refine ⟨fun n t ht x => norm_dysonTerm_le B hS n ht x,
    fun t ht x => summable_dysonTerm B hS ht x,
    perturbed hS B, ?_, continuous_perturbed_apply B hS,
    fun t ht x => dysonSum_eq_add_integral B hS ht x, ?_,
    fun _ _ => rfl, ?_, norm_perturbed_le B hS, ?_⟩
  · intro t ht
    ext x
    change dysonSum S B t x = x
    have he : dysonSum S B t x = dysonSum S B 0 x := by
      simp only [dysonSum, max_eq_right ht, max_self]
    rw [he, dysonSum_zero B hS]
  · intro V hV
    funext t
    ext x
    by_cases ht : 0 ≤ t
    · exact eq_dysonSum_of_duhamel B hS (T := t) (X := fun r => V r x)
        (hV.2.1 x).continuousOn x (fun r hr => hV.2.2 r hr.1 x) t ⟨ht, le_rfl⟩
    · rw [hV.1 t (le_of_not_ge ht)]
      change x = dysonSum S B t x
      have he : dysonSum S B t x = dysonSum S B 0 x := by
        simp only [dysonSum, max_eq_right (le_of_not_ge ht), max_self]
      rw [he, dysonSum_zero B hS]
  · intro s t hs ht
    exact perturbed_add B hS ht hs
  · intro T X x hX hX'
    exact eq_dysonSum_of_duhamel B hS hX x hX'

end D5.S3.Quantum.Analysis.DysonPhillipsPerturbation
