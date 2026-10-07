/- GID: D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian moments, independence and operator norm tails. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.LogDetMartingale

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Gaussian.GaussianFourth

open MeasureTheory
open ProbabilityTheory
open Finset
open scoped NNReal
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

/-- **`y⁴ ≤ 24(e^y + e^{-y})`.**  The `i = 4` term of the exponential series at `|y|`. -/
theorem pow_four_le_exp (y : ℝ) : y ^ 4 ≤ 24 * (Real.exp y + Real.exp (-y)) := by
  have habs : |y| ^ 4 = y ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hser := Real.sum_le_exp_of_nonneg (abs_nonneg y) 5
  have h4 : |y| ^ 4 / (Nat.factorial 4 : ℝ)
      ≤ ∑ i ∈ Finset.range 5, |y| ^ i / (Nat.factorial i : ℝ) := by
    refine Finset.single_le_sum (f := fun i => |y| ^ i / (Nat.factorial i : ℝ)) ?_ ?_
    · intro i _
      positivity
    · simp
  have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at h4
  have hterm : |y| ^ 4 / 24 ≤ Real.exp |y| := le_trans h4 hser
  have hle : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-y)]
    · rw [h]; linarith [Real.exp_pos y]
  rw [← habs]
  linarith

/-- The domination that gives both the integrability and the moment bound. -/
theorem pow_four_le_of_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    x ^ 4 ≤ 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x))) := by
  have h := pow_four_le_exp (t * x)
  have hexp : (t * x) ^ 4 = t ^ 4 * x ^ 4 := by ring
  rw [hexp] at h
  have ht4 : 0 < t ^ 4 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ht4]
  nlinarith [h]

theorem integrable_pow_four_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) := by
  refine Integrable.mono'
    (((integrable_exp_mul_gaussianReal (μ := 0) (v := v) 1).add
      (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-1))).const_mul (24 / (1 : ℝ) ^ 4))
    (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have h := pow_four_le_of_pos (t := 1) one_pos x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 4)]
  simpa using h

theorem integral_pow_four_le (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) ≤ 100 * (v : ℝ) ^ 2 := by
  rcases eq_or_lt_of_le (v.coe_nonneg) with hv | hv
  ·
    have hv0 : v = 0 := by
      ext
      simpa using hv.symm
    subst hv0
    rw [gaussianReal_zero_var]
    simp
  · set t : ℝ := Real.sqrt (2 / (v : ℝ)) with ht
    have ht0 : 0 < t := by
      rw [ht]
      exact Real.sqrt_pos.2 (by positivity)
    have ht2 : t ^ 2 = 2 / (v : ℝ) := Real.sq_sqrt (by positivity)
    have ht4 : t ^ 4 = 4 / (v : ℝ) ^ 2 := by
      have : t ^ 4 = (t ^ 2) ^ 2 := by ring
      rw [this, ht2, div_pow]
      norm_num
    have hmgf : ∀ s : ℝ, ∫ x, Real.exp (s * x) ∂(gaussianReal 0 v)
        = Real.exp ((v : ℝ) * s ^ 2 / 2) := by
      intro s
      have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) s
      simpa [mgf] using h
    have hdomint : Integrable
        (fun x : ℝ => 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x))))
        (gaussianReal 0 v) := by
      have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
      have h2 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-t)
      have h2' : Integrable (fun x : ℝ => Real.exp (-(t * x))) (gaussianReal 0 v) := by
        simpa [neg_mul] using h2
      exact (h1.add h2').const_mul _
    have hmono : ∫ x, x ^ 4 ∂(gaussianReal 0 v)
        ≤ ∫ x, 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x))) ∂(gaussianReal 0 v) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        hdomint (Filter.Eventually.of_forall fun x => pow_four_le_of_pos ht0 x)
    have hval : ∫ x, 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x)))
        ∂(gaussianReal 0 v) = 24 / t ^ 4 * (2 * Real.exp 1) := by
      rw [integral_const_mul]
      have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
      have h2 : Integrable (fun x : ℝ => Real.exp (-(t * x))) (gaussianReal 0 v) := by
        simpa [neg_mul] using integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-t)
      rw [integral_add h1 h2]
      have e1 : ∫ x, Real.exp (t * x) ∂(gaussianReal 0 v) = Real.exp 1 := by
        rw [hmgf t, ht2]
        congr 1
        field_simp
      have e2 : ∫ x, Real.exp (-(t * x)) ∂(gaussianReal 0 v) = Real.exp 1 := by
        have : (fun x : ℝ => Real.exp (-(t * x))) = fun x : ℝ => Real.exp ((-t) * x) := by
          funext x; ring_nf
        rw [this, hmgf (-t)]
        congr 1
        rw [neg_pow, ht2]
        norm_num
        field_simp
      rw [e1, e2]
      ring
    rw [hval] at hmono
    refine le_trans hmono ?_
    have hcoef : 24 / t ^ 4 = 6 * (v : ℝ) ^ 2 := by
      rw [ht4]
      field_simp
      ring
    rw [hcoef]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith [he, sq_nonneg ((v : ℝ)), Real.exp_pos 1]

section Vector

variable {n : ℕ}

theorem norm_sq_eq_sum (x : EuclideanSpace ℝ (UT n)) : ‖x‖ ^ 2 = ∑ p : UT n, (x p) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [sq]

/-- **`E[‖ξ_k‖⁴] ≤ 100·h²·d²`**, `h = c²`, `d = Fintype.card (UT n)`.  Chebyshev's sum inequality
replaces the cross terms, so no independence of the coordinates is needed. -/
theorem integral_norm_pow_four_le (c : ℝ) (k : ℕ) :
    ∫ ω, ‖ChainSetup.step c k ω‖ ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 := by
  classical
  have hcoe : ((Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ) = c ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg c)

  have hcoord : ∀ p : UT n,
      ∫ ω, (ChainSetup.step c k ω p) ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ 100 * (c ^ 2) ^ 2 := by
    intro p
    have hmeas : AEMeasurable (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ChainSetup.step c k ω p)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
      (StepInputs2.measurable_coord (ChainSetup.measurable_step c k) p).aemeasurable
    have hmap : ∫ ω, (ChainSetup.step c k ω p) ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        = ∫ x, x ^ 4 ∂(gaussianReal 0 (Real.toNNReal (c ^ 2))) := by
      rw [← ChainSetup.step_coord_law c k p]
      refine (integral_map hmeas (f := fun x : ℝ => x ^ 4) ?_).symm
      rw [ChainSetup.step_coord_law c k p]
      fun_prop
    rw [hmap]
    have h := integral_pow_four_le (Real.toNNReal (c ^ 2))
    rwa [hcoe] at h
  have hintcoord : ∀ p : UT n, Integrable
      (fun ω : ℕ → EuclideanSpace ℝ (UT n) => (ChainSetup.step c k ω p) ^ 4)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro p
    have hmeas : AEMeasurable (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ChainSetup.step c k ω p)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
      (StepInputs2.measurable_coord (ChainSetup.measurable_step c k) p).aemeasurable
    have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 4)
        (Measure.map (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ChainSetup.step c k ω p)
          (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))) := by
      rw [ChainSetup.step_coord_law c k p]
      fun_prop
    have hiff := integrable_map_measure hg hmeas
    rw [ChainSetup.step_coord_law c k p] at hiff
    exact hiff.1 (integrable_pow_four_gaussianReal _)

  have hpt : ∀ ω : ℕ → EuclideanSpace ℝ (UT n),
      ‖ChainSetup.step c k ω‖ ^ 4
        ≤ (Fintype.card (UT n) : ℝ) * ∑ p : UT n, (ChainSetup.step c k ω p) ^ 4 := by
    intro ω
    have h1 : ‖ChainSetup.step c k ω‖ ^ 4
        = (∑ p : UT n, (ChainSetup.step c k ω p) ^ 2) ^ 2 := by
      rw [← norm_sq_eq_sum]
      ring
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (UT n)))
      (f := fun p => (ChainSetup.step c k ω p) ^ 2)
    rw [h1]
    refine le_trans h2 (le_of_eq ?_)
    rw [Finset.card_univ]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    ring
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => by positivity)
    (((integrable_finsetSum _ fun p _ => hintcoord p).const_mul
      ((Fintype.card (UT n) : ℝ))))
    (Filter.Eventually.of_forall hpt)) ?_
  rw [integral_const_mul, integral_finsetSum _ fun p _ => hintcoord p]
  have hsum : ∑ _p : UT n, (100 * (c ^ 2) ^ 2) = (Fintype.card (UT n) : ℝ) * (100 * (c ^ 2) ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hle : ∑ p : UT n, ∫ ω, (ChainSetup.step c k ω p) ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (Fintype.card (UT n) : ℝ) * (100 * (c ^ 2) ^ 2) := by
    rw [← hsum]
    exact Finset.sum_le_sum fun p _ => hcoord p
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  nlinarith [hle, hd0]

end Vector

end D5.S3.Arith.Lattices.Klartag.Gaussian.GaussianFourth
