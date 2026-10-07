/- GID: D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian moments, independence and operator norm tails. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2
import D5.S3.Arith.Lattices.Klartag.Tail.PaddedTail

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open ProbabilityTheory
open Set
open Real
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι]

/-- The running maximum of the increments' norms. -/
noncomputable def maxNorm {E : Type*} [NormedAddCommGroup E] (ξ : ℕ → Ω → E) :
    ℕ → Ω → ℝ
  | 0, _ => 0
  | k + 1, ω => max (maxNorm ξ k ω) ‖ξ k ω‖

variable {E : Type*} [NormedAddCommGroup E] {ξ : ℕ → Ω → E}

omit [MeasurableSpace Ω] in
theorem maxNorm_nonneg (N : ℕ) (ω : Ω) : 0 ≤ maxNorm ξ N ω := by
  induction N with
  | zero => exact le_rfl
  | succ k ih => exact le_trans ih (le_max_left _ _)

omit [MeasurableSpace Ω] in
/-- **Every increment before `N` is below the maximum** — the pointwise fact the stopping-time
corollary runs on. -/
theorem le_maxNorm {j N : ℕ} (hj : j < N) (ω : Ω) : ‖ξ j ω‖ ≤ maxNorm ξ N ω := by
  induction N with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact le_trans (ih h) (le_max_left _ _)
    · subst h; exact le_max_right _ _

omit [MeasurableSpace Ω] in
/-- **The stopping-time corollary.**  For any index function `τ` with `τ ω < N`, the increment read
at `τ` is below the maximum, pointwise — so its expectation is too. -/
theorem norm_at_index_le_maxNorm {N : ℕ} (τ : Ω → ℕ) (hτ : ∀ ω, τ ω < N) (ω : Ω) :
    ‖ξ (τ ω) ω‖ ≤ maxNorm ξ N ω := le_maxNorm (hτ ω) ω

omit [MeasurableSpace Ω] in
/-- If the running maximum exceeds a non-negative level, some increment does. -/
theorem exists_le_of_lt_maxNorm {N : ℕ} {c : ℝ} (hc : 0 ≤ c) (ω : Ω)
    (h : c < maxNorm ξ N ω) : ∃ k, k < N ∧ c ≤ ‖ξ k ω‖ := by
  induction N with
  | zero => exact absurd h (by rw [show maxNorm ξ 0 ω = 0 from rfl]; exact not_lt.2 hc)
  | succ m ih =>
    have hm : maxNorm ξ (m + 1) ω = max (maxNorm ξ m ω) ‖ξ m ω‖ := rfl
    rcases max_cases (maxNorm ξ m ω) ‖ξ m ω‖ with ⟨heq, _⟩ | ⟨heq, _⟩
    · obtain ⟨k, hk, hle⟩ := ih (by rwa [hm, heq] at h)
      exact ⟨k, Nat.lt_succ_of_lt hk, hle⟩
    · refine ⟨m, Nat.lt_succ_self m, ?_⟩
      rw [hm, heq] at h; linarith

theorem measurable_maxNorm [MeasurableSpace E] [BorelSpace E]
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) : Measurable (maxNorm ξ N) := by
  induction N with
  | zero => exact measurable_const
  | succ k ih =>
    have h : Measurable fun ω => max (maxNorm ξ k ω) ‖ξ k ω‖ := ih.max (hξ k).norm
    exact h

/-- **The maximum's tail, normalised.**  With `σ² = v·d` the union bound over the `N` steps and the
`d` coordinates gives a *standard* Gaussian tail in `t`. -/
theorem maxNorm_tail {ξ : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℝ≥0} {σ : ℝ} (hσ : 0 < σ)
    (hv : 0 < (v : ℝ)) (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v) (N : ℕ) {t : ℝ}
    (ht : 0 < t) :
    P.real {ω | t < maxNorm ξ N ω / σ}
      ≤ (N : ℝ) * ((Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / 2))) := by
  classical
  have hd0 : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    by_contra h
    push Not at h
    have : (Fintype.card ι : ℝ) = 0 := le_antisymm h (by positivity)
    nlinarith [hσ2, sq_nonneg σ]
  have hsub : {ω | t < maxNorm ξ N ω / σ} ⊆ ⋃ k ∈ Finset.range N, {ω | σ * t ≤ ‖ξ k ω‖} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    rw [lt_div_iff₀ hσ] at hω
    obtain ⟨k, hk, hle⟩ := exists_le_of_lt_maxNorm (mul_pos hσ ht).le ω (by linarith)
    exact Set.mem_biUnion (Finset.mem_range.2 hk) hle
  have hexp : ∀ k, P.real {ω | σ * t ≤ ‖ξ k ω‖}
      ≤ (Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / 2)) := by
    intro k
    have h := StepInputs2.measureReal_norm_ge_le (hlaw k) (mul_pos hσ ht)
    have harg : -((σ * t) ^ 2 / (Fintype.card ι : ℝ)) / (2 * (v : ℝ)) = -t ^ 2 / 2 := by
      field_simp
      nlinarith [hσ2]
    rwa [harg] at h
  calc P.real {ω | t < maxNorm ξ N ω / σ}
      ≤ P.real (⋃ k ∈ Finset.range N, {ω | σ * t ≤ ‖ξ k ω‖}) :=
        measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ k ∈ Finset.range N, P.real {ω | σ * t ≤ ‖ξ k ω‖} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, (Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / 2)) :=
        Finset.sum_le_sum fun k _ => hexp k
    _ = (N : ℝ) * ((Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / 2))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem measure_eq_ofReal_measureReal (s : Set Ω) : P s = ENNReal.ofReal (P.real s) := by
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P s)]

/-- **The maximal inequality, in `lintegral` form.**  No integrability hypothesis. -/
theorem lintegral_maxNorm_le {ξ : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℝ≥0} {σ : ℝ}
    (hσ : 0 < σ) (hv : 0 < (v : ℝ)) (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ ω, ENNReal.ofReal (maxNorm ξ N ω) ∂P
      ≤ ENNReal.ofReal (σ * (a
          + (N : ℝ) * (Fintype.card ι : ℝ) * 2 * (Real.exp (-a ^ 2 / 2) / a))) := by
  classical
  set C : ℝ := (N : ℝ) * (Fintype.card ι : ℝ) * 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hmm : Measurable (maxNorm ξ N) := measurable_maxNorm hξ N
  set g : Ω → ℝ := fun ω => maxNorm ξ N ω / σ with hg
  have hgm : Measurable g := hmm.div_const σ
  have hgnn : 0 ≤ᵐ[P] g :=
    Filter.Eventually.of_forall fun ω => div_nonneg (maxNorm_nonneg N ω) hσ.le

  have hlc : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P = ∫⁻ t in Ioi (0 : ℝ), P {ω | t < g ω} :=
    lintegral_eq_lintegral_meas_lt P hgnn hgm.aemeasurable

  have hsmall : ∫⁻ t in Ioc (0 : ℝ) a, P {ω | t < g ω} ≤ ENNReal.ofReal a := by
    refine le_trans (setLIntegral_mono measurable_const (fun t _ => prob_le_one)) ?_
    rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]

  have hcont : Continuous fun t : ℝ => C * Real.exp (-t ^ 2 / 2) := by fun_prop
  have hintC : IntegrableOn (fun t : ℝ => C * Real.exp (-t ^ 2 / 2)) (Ioi a) :=
    (integrableOn_exp_neg_sq a).const_mul C
  have hbig : ∫⁻ t in Ioi a, P {ω | t < g ω}
      ≤ ENNReal.ofReal (C * (Real.exp (-a ^ 2 / 2) / a)) := by
    have hstep : ∫⁻ t in Ioi a, P {ω | t < g ω}
        ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (C * Real.exp (-t ^ 2 / 2)) := by
      refine setLIntegral_mono hcont.measurable.ennreal_ofReal (fun t ht => ?_)
      rw [measure_eq_ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      have h := maxNorm_tail hσ hv hσ2 hlaw N (lt_trans ha ht)
      calc P.real {ω | t < g ω} ≤ (N : ℝ) * ((Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / 2))) :=
            h
        _ = C * Real.exp (-t ^ 2 / 2) := by rw [hC]; ring
    calc ∫⁻ t in Ioi a, P {ω | t < g ω}
        ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (C * Real.exp (-t ^ 2 / 2)) := hstep
      _ = ENNReal.ofReal (∫ t in Ioi a, C * Real.exp (-t ^ 2 / 2)) :=
          (ofReal_integral_eq_lintegral_ofReal hintC
            (Filter.Eventually.of_forall fun t => by positivity)).symm
      _ ≤ ENNReal.ofReal (C * (Real.exp (-a ^ 2 / 2) / a)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [MeasureTheory.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (gaussian_tail_le ha) hC0

  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioi a) :=
    Set.disjoint_left.2 (fun t h1 h2 => absurd h2 (not_lt.2 h1.2))
  have hgle : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P
      ≤ ENNReal.ofReal (a + C * (Real.exp (-a ^ 2 / 2) / a)) := by
    rw [hlc, hsplit, lintegral_union measurableSet_Ioi hdisj,
      ENNReal.ofReal_add ha.le (by positivity)]
    exact add_le_add hsmall hbig
  have hscale : ∀ ω, ENNReal.ofReal (maxNorm ξ N ω) = ENNReal.ofReal σ * ENNReal.ofReal (g ω) := by
    intro ω
    rw [← ENNReal.ofReal_mul hσ.le, hg]
    congr 1
    field_simp
  calc ∫⁻ ω, ENNReal.ofReal (maxNorm ξ N ω) ∂P
      = ENNReal.ofReal σ * ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
        simp_rw [hscale]
        exact lintegral_const_mul _ hgm.ennreal_ofReal
    _ ≤ ENNReal.ofReal σ * ENNReal.ofReal (a + C * (Real.exp (-a ^ 2 / 2) / a)) := by
        gcongr
    _ = ENNReal.ofReal (σ * (a + C * (Real.exp (-a ^ 2 / 2) / a))) :=
        (ENNReal.ofReal_mul hσ.le).symm

/-- **The maximal inequality, in Bochner form.** -/
theorem expectation_max_norm_le {ξ : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℝ≥0} {σ : ℝ}
    (hσ : 0 < σ) (hv : 0 < (v : ℝ)) (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) {a : ℝ} (ha : 0 < a)
    (hint : Integrable (maxNorm ξ N) P) :
    ∫ ω, maxNorm ξ N ω ∂P
      ≤ σ * (a + (N : ℝ) * (Fintype.card ι : ℝ) * 2 * (Real.exp (-a ^ 2 / 2) / a)) := by
  have hbridge := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => maxNorm_nonneg N ω)
  have h := lintegral_maxNorm_le hσ hv hσ2 hlaw hξ N ha
  rw [← hbridge] at h
  refine (ENNReal.ofReal_le_ofReal_iff ?_).1 h
  have : (0 : ℝ) ≤ (N : ℝ) * (Fintype.card ι : ℝ) * 2 * (Real.exp (-a ^ 2 / 2) / a) := by
    positivity
  nlinarith [hσ.le, ha.le]

/-- **The maximal inequality with the level chosen.**  At `a = √(2·log K)` with `K = 2dN`, the
tail term is exactly `σ/a ≤ σ`, so

  `E[max_{k<N} ‖ξ_k‖] ≤ σ·(√(2·log(2dN)) + 1)`,   `σ = √(v·d)`.

The only size condition is `K ≥ e`, which holds as soon as there are two steps in dimension two. -/
theorem expectation_max_norm_le_log {ξ : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℝ≥0} {σ : ℝ}
    (hσ : 0 < σ) (hv : 0 < (v : ℝ)) (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ)
    (hK : Real.exp 1 ≤ 2 * (Fintype.card ι : ℝ) * (N : ℝ))
    (hint : Integrable (maxNorm ξ N) P) :
    ∫ ω, maxNorm ξ N ω ∂P
      ≤ σ * (Real.sqrt (2 * Real.log (2 * (Fintype.card ι : ℝ) * (N : ℝ))) + 1) := by
  set K : ℝ := 2 * (Fintype.card ι : ℝ) * (N : ℝ) with hKdef
  have hK1 : (1 : ℝ) < K := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hK
  have hK0 : 0 < K := by linarith
  have hlogK : (1 : ℝ) ≤ Real.log K := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) hK
  set a : ℝ := Real.sqrt (2 * Real.log K) with hadef
  have ha2 : a ^ 2 = 2 * Real.log K := Real.sq_sqrt (by linarith)
  have ha1 : (1 : ℝ) ≤ a := by
    nlinarith [Real.sqrt_nonneg (2 * Real.log K), ha2]
  have ha : 0 < a := by linarith
  have hexp : Real.exp (-a ^ 2 / 2) = 1 / K := by
    rw [ha2, show -(2 * Real.log K) / 2 = -Real.log K by ring, Real.exp_neg, Real.exp_log hK0,
      one_div]
  have hCK : (N : ℝ) * (Fintype.card ι : ℝ) * 2 = K := by rw [hKdef]; ring
  refine le_trans (expectation_max_norm_le hσ hv hσ2 hlaw hξ N ha hint) ?_
  rw [hCK, hexp]
  refine mul_le_mul_of_nonneg_left ?_ hσ.le
  have hstep : K * (1 / K / a) = 1 / a := by field_simp
  rw [hstep]
  have : 1 / a ≤ 1 := by
    rw [div_le_one ha]; exact ha1
  linarith

end D5.S3.Arith.Lattices.Klartag
