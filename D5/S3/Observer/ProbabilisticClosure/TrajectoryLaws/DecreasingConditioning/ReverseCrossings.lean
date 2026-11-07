/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/ReverseCrossings
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/ReverseCrossings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-horizon reversal bounds upcrossings of decreasing conditional expectations. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer

Copyright 2025 The Exchangeability Project contributors

Adapted from TauCetiProject/TauCeti at c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f,
with Exchangeability ancestry e0532e59ceff23edab44dda9ab0655debbc9cc22.
Applicable license texts and immutable source locators:
Library/Observer/tauceti2026levydownward.md.
-/

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

/-! Finite-horizon filtration reversal: TauCeti/Probability/Martingale/Reverse.lean. -/
section
variable {Ω : Type*} {m0 : MeasurableSpace Ω}

private def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ m0)
    (N : ℕ) : Filtration ℕ m0 where
  seq n := 𝔽 (N - n)
  mono' := Antitone.comp h_antitone antitone_const_tsub
  le' _ := h_le _

end

/-! Path reversal: TauCeti/Probability/Martingale/Crossings/TimeReversal.lean. -/

private def revProcess {Ω α : Type*} (X : ℕ → Ω → α) (N : ℕ) : ℕ → Ω → α :=
  fun n ω => X (Polynomial.revAt N n) ω

private lemma revProcess_apply_of_le {Ω α : Type*} (X : ℕ → Ω → α) {N n : ℕ} (h : n ≤ N) (ω : Ω) :
    revProcess X N n ω = X (N - n) ω := by simp [revProcess, Polynomial.revAt_le h]

private lemma upperCrossingTime_neg_revProcess_succ_le
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N m' i : ℕ) (ω : Ω)
    (hσ_lt_N : upperCrossingTime a b X N (i + 1) ω < N)
    (ih' : upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) m' ω
      ≤ N - lowerCrossingTime a b X N (i + 1) ω) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) (m' + 1) ω
      ≤ N - lowerCrossingTime a b X N i ω := by
  set Y := -(revProcess X N) with hY_def
  -- `X` reaches `≥ b` at its `(i+1)`-th upper crossing, `≤ a` at its `i`-th lower crossing, and the
  -- latter precedes the former. (Stated on explicit terms, then folded to `σ`, `τ` by `set`.)
  have hτ_lt_σ : lowerCrossingTime a b X N i ω < upperCrossingTime a b X N (i + 1) ω :=
    lowerCrossingTime_lt_upperCrossingTime hab (Nat.ne_of_lt hσ_lt_N)
  -- The `i`-th lower crossing precedes the `(i+1)`-th upper, so it too completes before `N`.
  have hτ_lt_N : lowerCrossingTime a b X N i ω < N := lt_trans hτ_lt_σ hσ_lt_N
  have hX_σ_ge_b : b ≤ X (upperCrossingTime a b X N (i + 1) ω) ω :=
    stoppedValue_upperCrossingTime (Nat.ne_of_lt hσ_lt_N)
  have hX_τ_le_a : X (lowerCrossingTime a b X N i ω) ω ≤ a :=
    stoppedValue_lowerCrossingTime (Nat.ne_of_lt hτ_lt_N)
  have h_lct_ge : upperCrossingTime a b X N (i + 1) ω ≤ lowerCrossingTime a b X N (i + 1) ω :=
    upperCrossingTime_le_lowerCrossingTime
  set σ := upperCrossingTime a b X N (i + 1) ω
  set τ := lowerCrossingTime a b X N i ω
  -- The reflected process `Y` mirrors these levels at the reflected times `N - σ` and `N - τ`.
  have hY_Nσ_le_negb : Y (N - σ) ω ≤ -b := by
    have hrev : revProcess X N (N - σ) ω = X σ ω := by
      rw [revProcess_apply_of_le X (Nat.sub_le N σ) ω, Nat.sub_sub_self (Nat.le_of_lt hσ_lt_N)]
    simp only [hY_def, Pi.neg_apply, hrev]; linarith
  have hY_Nτ_ge_nega : -a ≤ Y (N - τ) ω := by
    have hrev : revProcess X N (N - τ) ω = X τ ω := by
      rw [revProcess_apply_of_le X (Nat.sub_le N τ) ω, Nat.sub_sub_self (Nat.le_of_lt hτ_lt_N)]
    simp only [hY_def, Pi.neg_apply, hrev]; linarith
  -- Advance `Y`'s crossing count: the induction hypothesis bounds `Y`'s `m'`-th upper crossing by
  -- `N - σ`, hence its `m'`-th lower crossing too; the `(m'+1)`-th upper crossing then lands by
  -- `N - τ`, the reflection of `X`'s crossing start.
  have h_uct_le_Nσ : upperCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - σ :=
    le_trans ih' (Nat.sub_le_sub_left h_lct_ge N)
  have h_lctY_le_Nσ : lowerCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - σ := by
    simpa only [lowerCrossingTime] using
      hittingBtwn_le_of_mem h_uct_le_Nσ (Nat.le_succ_of_le (Nat.sub_le N σ)) hY_Nσ_le_negb
  have h_lctY_le_Nτ : lowerCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - τ :=
    Nat.le_of_lt (lt_of_le_of_lt h_lctY_le_Nσ (Nat.sub_lt_sub_left hτ_lt_N hτ_lt_σ))
  calc upperCrossingTime (-b) (-a) Y (N + 1) (m' + 1) ω
      = hittingBtwn Y (Set.Ici (-a)) (lowerCrossingTime (-b) (-a) Y (N + 1) m' ω) (N + 1) ω :=
        upperCrossingTime_succ_eq ω
    _ ≤ N - τ :=
        hittingBtwn_le_of_mem h_lctY_le_Nτ (Nat.le_succ_of_le (Nat.sub_le N τ)) hY_Nτ_ge_nega

private lemma upperCrossingTime_neg_revProcess_le_strong
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k m : ℕ) (ω : Ω) (hm : m ≤ k)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) m ω
      ≤ N - lowerCrossingTime a b X N (k - m) ω := by
  -- All of `X`'s upper crossings up to the `k`-th complete before `N`, and so do the lower ones.
  have h_j : ∀ j ≤ k, upperCrossingTime a b X N j ω < N := fun j hj =>
    lt_of_le_of_lt (upperCrossingTime_mono hj) h_k
  induction m with
  | zero => simp only [upperCrossingTime_zero, Nat.sub_zero]; exact Nat.zero_le _
  | succ m' ih =>
    -- `Y`'s `(m'+1)`-th crossing reflects `X`'s `(k-m')`-th; set `i = k-(m'+1)`, so `k-m' = i+1`.
    have hik : k - m' = k - (m' + 1) + 1 := by omega
    refine upperCrossingTime_neg_revProcess_succ_le X a b hab N m' (k - (m' + 1)) ω ?_ ?_
    · rw [← hik]; exact h_j (k - m') (Nat.sub_le k m')
    · rw [← hik]; exact ih (Nat.le_of_lt (Nat.lt_of_succ_le hm))

private lemma upperCrossingTime_neg_revProcess_le
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k : ℕ) (ω : Ω)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) k ω ≤ N := by
  -- The `strong` version bounds this by `N - lowerCrossingTime …` via the bijection
  -- `(τ, σ) ↦ (N - σ, N - τ)`; discard the subtraction with `Nat.sub_le`.
  have h := upperCrossingTime_neg_revProcess_le_strong X a b hab N k k ω le_rfl h_k
  exact le_trans (by simpa using h) (Nat.sub_le N _)

/-! Pathwise crossing congruence and the free N+1 boundary:
TauCeti/Probability/Martingale/Crossings/Pathwise.lean. -/

private lemma hitting_congr {Ω β ι : Type*} [Preorder ι] [InfSet ι] {u v : ι → Ω → β}
    {s : Set β} {n m : ι} {ω : Ω} (h : ∀ k, n ≤ k → k ≤ m → u k ω = v k ω) :
    hittingBtwn u s n m ω = hittingBtwn v s n m ω := by
  simp only [hittingBtwn]
  by_cases hex : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · have hex' : ∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      obtain ⟨j, hj, hj_mem⟩ := hex
      refine ⟨j, hj, ?_⟩
      rw [← h j hj.1 hj.2]
      exact hj_mem
    simp only [ite_eq_left hex, ite_eq_left hex']
    congr 1
    ext k
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [← h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
  · have hex' : ¬∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      intro ⟨j, hj, hj_mem⟩
      apply hex
      refine ⟨j, hj, ?_⟩
      rw [h j hj.1 hj.2]
      exact hj_mem
    simp only [ite_eq_right hex, ite_eq_right hex']

private lemma upperCrossingTime_congr {Ω ι : Type*} [Preorder ι] [OrderBot ι] [InfSet ι]
    {a b : ℝ} {f g : ι → Ω → ℝ} {N : ι} {ω : Ω} (h : ∀ n ≤ N, f n ω = g n ω) :
    ∀ k, upperCrossingTime a b f N k ω = upperCrossingTime a b g N k ω := by
  intro k
  induction k with
  | zero =>
    simp [upperCrossingTime_zero]
  | succ n ih =>
    simp only [upperCrossingTime_succ_eq]
    have lct_eq : lowerCrossingTime a b f N n ω = lowerCrossingTime a b g N n ω := by
      simp only [lowerCrossingTime]
      rw [ih]
      apply hitting_congr
      intros k _ hk_ub
      exact h k hk_ub
    rw [lct_eq]
    apply hitting_congr
    intros k _ hk_ub
    exact h k hk_ub

private lemma upcrossingsBefore_congr {Ω ι : Type*} [Preorder ι] [OrderBot ι] [InfSet ι]
    {a b : ℝ} {f g : ι → Ω → ℝ} {N : ι} {ω : Ω} (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp [upcrossingsBefore, upperCrossingTime_congr h]

private lemma hittingBtwn_succ_congr {Ω β : Type*} {u v : ℕ → Ω → β} {s : Set β} {n N : ℕ}
    {ω : Ω} (h : ∀ k, n ≤ k → k ≤ N → u k ω = v k ω) :
    hittingBtwn u s n (N + 1) ω = hittingBtwn v s n (N + 1) ω := by
  by_cases hex : ∃ j ∈ Set.Icc n N, u j ω ∈ s
  · have hexv : ∃ j ∈ Set.Icc n N, v j ω ∈ s := by
      obtain ⟨j, hj, hjs⟩ := hex
      exact ⟨j, hj, h j hj.1 hj.2 ▸ hjs⟩
    rw [← hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ N) hex,
        ← hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ N) hexv]
    exact hitting_congr h
  · have hexv : ¬ ∃ j ∈ Set.Icc n N, v j ω ∈ s := by
      rintro ⟨j, hj, hjs⟩
      exact hex ⟨j, hj, (h j hj.1 hj.2).symm ▸ hjs⟩
    have key : ∀ {w : ℕ → Ω → β}, (¬ ∃ j ∈ Set.Icc n N, w j ω ∈ s) →
        hittingBtwn w s n (N + 1) ω = N + 1 := by
      intro w hw
      refine le_antisymm (hittingBtwn_le ω) ?_
      by_contra hlt
      rw [not_le, hittingBtwn_lt_iff (N + 1) le_rfl] at hlt
      obtain ⟨j, hj, hjs⟩ := hlt
      rw [Set.mem_Ico] at hj
      exact hw ⟨j, Set.mem_Icc.mpr ⟨hj.1, Nat.lt_succ_iff.mp hj.2⟩, hjs⟩
    rw [key hex, key hexv]

private lemma upperCrossingTime_succ_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ}
    {ω : Ω} (h : ∀ n ≤ N, f n ω = g n ω) :
    ∀ k, upperCrossingTime a b f (N + 1) k ω = upperCrossingTime a b g (N + 1) k ω := by
  intro k
  induction k with
  | zero => simp [upperCrossingTime_zero]
  | succ n ih =>
    simp only [upperCrossingTime_succ_eq]
    have lct_eq : lowerCrossingTime a b f (N + 1) n ω = lowerCrossingTime a b g (N + 1) n ω := by
      simp only [lowerCrossingTime]
      rw [ih]
      exact hittingBtwn_succ_congr fun k _ hk_ub => h k hk_ub
    rw [lct_eq]
    exact hittingBtwn_succ_congr fun k _ hk_ub => h k hk_ub

private lemma upcrossingsBefore_succ_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f (N + 1) ω = upcrossingsBefore a b g (N + 1) ω := by
  simp [upcrossingsBefore, upperCrossingTime_succ_congr h]

private lemma upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N : ℕ) (ω : Ω) :
    upcrossingsBefore a b X N ω
      ≤ upcrossingsBefore (-b) (-a) (-(revProcess X N)) (N + 1) ω := by
  classical
  simp only [upcrossingsBefore]
  by_cases hN : N = 0
  · simp [hN]
  by_cases hemp : {n | upperCrossingTime a b X N n ω < N}.Nonempty
  · -- Mathlib's boundedness of the completed-crossing index set on the reversed side.
    have hneg : -b < -a := by linarith
    have hbdd : BddAbove
        {n | upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) n ω < N + 1} :=
      upperCrossingTime_lt_bddAbove hneg
    have hsub : {n | upperCrossingTime a b X N n ω < N} ⊆
        {n | upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) n ω < N + 1} := by
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn ⊢
      -- With horizon `N + 1` the bijection works: crossings completing at time `N` are now counted
      -- since `N < N + 1`.
      cases n with
      | zero =>
        simp only [upperCrossingTime_zero]
        exact Nat.zero_lt_succ N
      | succ k =>
        -- `hn` says `X` has `k + 1` complete crossings before time `N`; the bijection
        -- `(τ, σ) ↦ (N - σ, N - τ)` maps these to reversed crossings completing by time `N`.
        have h_bound : upperCrossingTime (-b) (-a)
            (-(revProcess X N)) (N + 1) (k + 1) ω ≤ N :=
          upperCrossingTime_neg_revProcess_le X a b hab N (k + 1) ω hn
        exact Nat.lt_succ_of_le h_bound
    exact csSup_le_csSup hbdd hemp hsub
  · rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [hemp]

/-! Positive-part CE estimate:
TauCeti/MeasureTheory/Function/ConditionalExpectation.lean. -/

private theorem lintegral_ofReal_posPart_condExp_sub_le {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} (f : Ω → ℝ) (a : ℝ) :
    ∫⁻ ω, ENNReal.ofReal ((μ[f | m] ω - a)⁺) ∂μ ≤ eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ := by
  -- Pointwise `(x - a)⁺ ≤ |x - a|`, then the triangle inequality and the L¹ contraction.
  calc ∫⁻ ω, ENNReal.ofReal ((μ[f | m] ω - a)⁺) ∂μ
      ≤ ∫⁻ ω, (‖μ[f | m] ω‖ₑ + ‖a‖ₑ) ∂μ := lintegral_mono fun ω => by
        grw [← enorm_sub_le, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (sup_le (le_abs_self _) (abs_nonneg _))
    _ = eLpNorm (μ[f | m]) 1 μ + ‖a‖ₑ * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const,
          eLpNorm_one_eq_lintegral_enorm integrable_condExp.aestronglyMeasurable]
    _ ≤ eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ := by
        grw [eLpNorm_condExp_le_eLpNorm f le_rfl]

/-! Uniform crossing integral:
TauCeti/Probability/Martingale/Crossings/Bounds.lean. -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

private lemma lintegral_upcrossings_condExp_rev_bdd [IsFiniteMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ N,
      ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 (N - n)]) ω) ∂μ ≤ C := by
  -- `C = (‖f‖₁ + |a| · μ(univ)) / (b - a)` via Doob's upcrossing inequality.
  set C := (eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ) / ENNReal.ofReal (b - a)
  have hC_finite : C < ⊤ := by
    refine ENNReal.div_lt_top ?h1 ?h2
    · -- Numerator ≠ ⊤ (finite measure keeps `μ Set.univ < ⊤`)
      refine (ENNReal.add_lt_top.2 ⟨?_, ?_⟩).ne
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
      · exact ENNReal.mul_lt_top enorm_lt_top (measure_lt_top μ Set.univ)
    · -- Denominator ≠ 0
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  refine ⟨C, hC_finite, fun N => ?_⟩
  -- Doob's upcrossing inequality for the reversed submartingale, then bound the supremum with
  -- the positive-part L¹ estimate.
  have hsub := (martingale_condExp f (revFiltration 𝔽 h_antitone h_le N) μ).submartingale
  have key := hsub.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  simp (config := { congrConsts := false }) only [show ∀ n,
    (revFiltration 𝔽 h_antitone h_le N) n = 𝔽 (N - n) from fun _ => rfl] at key
  have sup_bdd : ⨆ M, ∫⁻ ω, ENNReal.ofReal ((μ[f | 𝔽 (N - M)] ω - a)⁺) ∂μ
      ≤ eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ :=
    iSup_le fun M => lintegral_ofReal_posPart_condExp_sub_le f a
  have step1 : (∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 (N - n)]) ω ∂μ)
      * ENNReal.ofReal (b - a)
      ≤ ⨆ M, ∫⁻ ω, ENNReal.ofReal ((μ[f | 𝔽 (N - M)] ω - a)⁺) ∂μ := by
    rw [mul_comm]; exact key
  calc ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 (N - n)]) ω ∂μ
      ≤ (⨆ M, ∫⁻ ω, ENNReal.ofReal ((μ[f | 𝔽 (N - M)] ω - a)⁺) ∂μ)
          / ENNReal.ofReal (b - a) := by
        refine (ENNReal.le_div_iff_mul_le ?_ ?_).2 step1
        · left; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
        · left; exact ENNReal.ofReal_ne_top
    _ ≤ (eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ) / ENNReal.ofReal (b - a) := by
        gcongr
    _ = C := rfl

private lemma upcrossingsBefore_condExp_le_upcrossings_neg_condExp_rev
    (f : Ω → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ) (ω : Ω) :
    ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ upcrossings (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) ω := by
  -- `revProcess (μ[f|𝔽·]) N` and `n ↦ μ[f | 𝔽 (N - n)]` agree on `[0, N]` (below the horizon,
  -- `Polynomial.revAt N` is genuine subtraction). The `N + 1` reversed horizon lets crossings
  -- completing exactly at `N` count, but the extra index `N + 1` is a *free boundary*: it never
  -- affects the crossing count (`upcrossingsBefore_succ_congr`), so we may swap the two processes
  -- there even though they differ at `N + 1`.
  have h_agree : ∀ n ≤ N, (-(revProcess (fun n => μ[f | 𝔽 n]) N)) n ω
      = (-(fun n => μ[f | 𝔽 (N - n)])) n ω := by
    intro n hn
    simp only [Pi.neg_apply, revProcess_apply_of_le _ hn]
  have hle : upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω
      ≤ upcrossingsBefore (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) (N + 1) ω :=
    calc upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω
        ≤ upcrossingsBefore (-b) (-a) (-(revProcess (fun n => μ[f | 𝔽 n]) N)) (N + 1) ω :=
          upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ _ a b hab N ω
      _ = upcrossingsBefore (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) (N + 1) ω :=
          upcrossingsBefore_succ_congr h_agree
  calc ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ ↑(upcrossingsBefore (-b) (-a)
            (-(fun n => μ[f | 𝔽 (N - n)])) (N + 1) ω) := Nat.cast_le.mpr hle
    _ ≤ upcrossings (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) ω := by
        simp only [MeasureTheory.upcrossings]
        exact le_iSup (fun M => (upcrossingsBefore (-b) (-a)
          (-(fun n => μ[f | 𝔽 (N - n)])) M ω : ℝ≥0∞)) (N + 1)

private lemma lintegral_upcrossings_neg_condExp_rev_eq (f : Ω → ℝ) (a b : ℝ) (N : ℕ) :
    ∫⁻ ω, upcrossings (-b) (-a)
        (-(fun n => μ[f | 𝔽 (N - n)])) ω ∂μ
      = ∫⁻ ω, upcrossings (-b) (-a)
          (fun n => μ[(fun x => -f x) | 𝔽 (N - n)]) ω ∂μ := by
  apply lintegral_congr_ae
  -- The two processes agree a.e. at every time index (countable intersection via `ae_all_iff`).
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n,
      (-(fun m => μ[f | 𝔽 (N - m)])) n ω =
      μ[(fun x => -f x) | 𝔽 (N - n)] ω := by
    rw [ae_all_iff]
    intro n
    simp only [Pi.neg_apply]
    exact (condExp_neg f (𝔽 (N - n))).symm
  filter_upwards [h_ae_eq] with ω hω
  simp only [MeasureTheory.upcrossings]
  refine iSup_congr fun M => ?_
  rw [upcrossingsBefore_congr (fun k _ => hω k)]

private lemma lintegral_upcrossings_le_of_forall_lintegral_upcrossingsBefore_le
    {g : ℕ → Ω → ℝ} {a b : ℝ} {C : ℝ≥0∞} {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    (h_adapted : StronglyAdapted ℱ g) (hab : a < b)
    (h_N_bound : ∀ N, ∫⁻ ω, ↑(upcrossingsBefore a b g N ω) ∂μ ≤ C) :
    ∫⁻ ω, upcrossings a b g ω ∂μ ≤ C := by
  -- Set `U N ω := upcrossingsBefore` (as `ℝ≥0∞`) for the process `g`.
  set U : ℕ → Ω → ℝ≥0∞ := fun N ω => (upcrossingsBefore a b g N ω : ℝ≥0∞) with hU
  -- Monotonicity in `N` (pathwise): more time allows more completed crossings.
  have hU_mono : Monotone U := by
    intro m n hmn ω
    simp only [hU]
    exact Nat.cast_le.2 (upcrossingsBefore_mono (f := g) hab hmn ω)
  -- Measurability of each `U N` via the adaptedness hypothesis.
  have hU_meas : ∀ N, Measurable (U N) := fun _ =>
    measurable_from_top.comp (h_adapted.measurable_upcrossingsBefore hab)
  -- Monotone convergence, then bound the supremum of integrals by `C`.
  have h_iSup : ∫⁻ ω, (⨆ N, U N ω) ∂μ = ⨆ N, ∫⁻ ω, U N ω ∂μ := lintegral_iSup hU_meas hU_mono
  have hbound : (⨆ N, ∫⁻ ω, U N ω ∂μ) ≤ C := iSup_le h_N_bound
  -- Conclude via `upcrossings = ⨆ N, upcrossingsBefore N`.
  simpa [MeasureTheory.upcrossings, hU] using h_iSup.le.trans hbound

/-- On a finite measure space, the actual conditional expectations of an integrable real
input along decreasing ambient sub-sigma-algebras have a finite upcrossing integral
for every real interval with distinct ordered endpoints. -/
theorem exists_lintegral_upcrossings_condExp_le [IsFiniteMeasure μ] (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ) (hf : Integrable f μ)
    (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ ≤ C := by
  -- Downcrossings-side surrogate bound: apply the (private) reversed-process bound to `-f` on the
  -- reflected interval `[-b, -a]`. This yields the constant `C_down` used throughout.
  obtain ⟨C_down, h_C_down_finite, hC_down⟩ :=
    lintegral_upcrossings_condExp_rev_bdd (μ := μ) h_antitone h_le
      (fun ω => -f ω) hf.neg (-b) (-a) (by linarith)
  refine ⟨C_down, h_C_down_finite, ?_⟩
  -- Per-horizon `L¹` bound: compose the pathwise comparison with the negation-commutes step, then
  -- discharge with the surrogate bound `hC_down`.
  have h_N_bound : ∀ N,
      ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ ≤ C_down := fun N =>
    calc ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ
        ≤ ∫⁻ ω, upcrossings (-b) (-a)
              (-(fun n => μ[f | 𝔽 (N - n)])) ω ∂μ :=
          lintegral_mono
            (upcrossingsBefore_condExp_le_upcrossings_neg_condExp_rev f hab N)
      _ = ∫⁻ ω, upcrossings (-b) (-a)
            (fun n => μ[(fun x => -f x) | 𝔽 (N - n)]) ω ∂μ :=
          lintegral_upcrossings_neg_condExp_rev_eq f a b N
      _ ≤ C_down := hC_down N
  -- The sequence `μ[f | 𝔽 n]` is adapted to the constant ambient filtration, supplying the
  -- measurability needed for the monotone-convergence upgrade.
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    Filtration.const ℕ (inferInstance : MeasurableSpace Ω) le_rfl
  have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) :=
    fun n => stronglyMeasurable_condExp.mono (h_le n)
  -- Upgrade the per-horizon bound to the total upcrossings integral (monotone convergence in `N`).
  exact lintegral_upcrossings_le_of_forall_lintegral_upcrossingsBefore_le h_adapted hab h_N_bound

end MeasureTheory
