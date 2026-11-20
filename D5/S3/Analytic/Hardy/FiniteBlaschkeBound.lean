/- GID: D5/S3/Analytic/Hardy/FiniteBlaschkeBound
   generality: G
   mirror-B: D5/B/S3/Analytic/Hardy/FiniteBlaschkeBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.CanonicalDecomposition]
   utility: none
   digest: A finite set of zeros bounds a bounded holomorphic function by its Blaschke product. -/

import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.Schwarz

/-! # Finite Blaschke bounds on the disk -/

open Metric Set Filter
open scoped Topology ComplexConjugate

noncomputable section

namespace D5.S3.Analytic.Hardy.FiniteBlaschkeBound

private theorem norm_bound_closedBall {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    {R M : ℝ} {f : ℂ → ℂ} {z : ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R))
    (hM : ∀ w ∈ closedBall 0 R, ‖f w‖ ≤ M)
    (ha : ∀ k ∈ s, a k ∈ ball 0 R)
    (hzero : ∀ k ∈ s, f (a k) = 0)
    (hinj : Function.Injective a)
    (hz : z ∈ ball 0 R) (hne : ∀ k ∈ s, z ≠ a k) :
    ‖f z‖ ≤ M * ∏ k ∈ s, ‖(Complex.canonicalFactor R (a k) z)⁻¹‖ := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simpa using hM z (ball_subset_closedBall hz)
  | insert k s hk ih =>
    have hak := ha k (Finset.mem_insert_self _ _)
    have hfk := hzero k (Finset.mem_insert_self _ _)
    have hnk := hne k (Finset.mem_insert_self _ _)
    let g (w : ℂ) := (((R : ℂ) ^ 2 - conj (a k) * w) / R) * dslope f (a k) w
    have hg : DifferentiableOn ℂ g (closedBall 0 R) := by
      have hd := (Complex.differentiableOn_dslope
        (mem_of_superset (isOpen_ball.mem_nhds hak) ball_subset_closedBall)).mpr hf
      exact (by fun_prop : DifferentiableOn ℂ
        (fun w : ℂ => ((R : ℂ) ^ 2 - conj (a k) * w) / R) (closedBall 0 R)).mul hd
    have hgw {w : ℂ} (hw : w ≠ a k) : g w = Complex.canonicalFactor R (a k) w * f w := by
      dsimp only [g]
      rw [dslope_of_ne _ hw, slope_def_field, hfk, sub_zero, Complex.canonicalFactor_apply, ← div_div]
      ring
    have hgM (w : ℂ) (hw : w ∈ closedBall 0 R) : ‖g w‖ ≤ M := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (hg.diffContOnCl_ball subset_rfl) ?_ ?_
      · intro v hv
        have hvs := frontier_ball_subset_sphere hv
        have hvne : v ≠ a k := by
          intro he
          rw [mem_sphere_iff_norm] at hvs
          rw [mem_ball_iff_norm] at hak
          rw [← he, hvs] at hak
          exact (lt_irrefl R) hak
        rw [hgw hvne, norm_mul, Complex.norm_canonicalFactor_eval_circle_eq_one hak hvs, one_mul]
        exact hM v (sphere_subset_closedBall hvs)
      · rwa [closure_ball _ hR.ne']
    have hgzero (i : ι) (hi : i ∈ s) : g (a i) = 0 := by
      rw [hgw (fun he => hk ((hinj he) ▸ hi)), hzero i (Finset.mem_insert_of_mem hi), mul_zero]
    have hrec := ih hg hgM (fun i hi => ha i (Finset.mem_insert_of_mem hi)) hgzero
      (fun i hi => hne i (Finset.mem_insert_of_mem hi))
    have hfac := Complex.canonicalFactor_ne_zero hak (ball_subset_closedBall hz) hnk
    rw [hgw hnk, norm_mul] at hrec
    rw [Finset.prod_insert hk, ← mul_left_comm, norm_inv, ← div_eq_inv_mul]
    exact (le_div_iff₀ (norm_pos_iff.mpr hfac)).mpr (by simpa [mul_comm] using hrec)

/-- A bounded holomorphic function on the disk is bounded at each point by
the same constant times the product of pseudohyperbolic distances to any
finite family of its distinct zeros. -/
theorem norm_le_mul_prod {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    {M : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hM : ∀ w ∈ ball 0 1, ‖f w‖ ≤ M)
    (ha : ∀ k ∈ s, a k ∈ ball 0 1)
    (hzero : ∀ k ∈ s, f (a k) = 0)
    (hinj : Function.Injective a) (hz : z ∈ ball 0 1) :
    ‖f z‖ ≤ M * ∏ k ∈ s, ‖(z - a k) / (1 - conj (a k) * z)‖ := by
  classical
  by_cases hne : ∀ k ∈ s, z ≠ a k
  · let B (r : ℝ) := M * ∏ k ∈ s,
        ‖((r : ℂ) * (z - a k)) / ((r : ℂ)^2 - conj (a k) * z)‖
    have hcont : ContinuousAt B 1 := by
      apply continuousAt_const.mul
      have hprod : ∀ k ∈ s, ContinuousAt (fun r : ℝ =>
          ‖((r : ℂ) * (z - a k)) / ((r : ℂ)^2 - conj (a k) * z)‖) 1 := by
        intro k hk
        have hd : 1 - conj (a k) * z ≠ 0 := by
          intro he
          have hh := congrArg norm (sub_eq_zero.mp he)
          rw [norm_one, norm_mul, Complex.norm_conj] at hh
          have hk' : ‖a k‖ < 1 := mem_ball_zero_iff.mp (ha k hk)
          have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
          nlinarith [mul_nonneg (sub_nonneg.mpr hk'.le) (norm_nonneg z)]
        fun_prop (disch := simpa using hd)
      exact tendsto_finsetProd s fun k hk => (hprod k hk).tendsto
    have hb : ∀ᶠ r in 𝓝[<] (1 : ℝ), ‖f z‖ ≤ B r := by
      have hrz := Ioo_mem_nhdsLT (mem_ball_zero_iff.mp hz)
      have hra : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ k ∈ s, ‖a k‖ < r := by
        rw [Filter.eventually_all_finset]
        intro k hk
        have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo ‖a k‖ 1 :=
          Ioo_mem_nhdsLT (mem_ball_zero_iff.mp (ha k hk))
        exact hev.mono fun _ hw => hw.1
      filter_upwards [hrz, hra] with r hr hs
      have hsub := closedBall_subset_ball hr.2 (x := (0 : ℂ))
      have h := norm_bound_closedBall s a ((norm_nonneg z).trans_lt hr.1)
        (hf.mono hsub) (fun w hw => hM w (hsub hw))
        (fun k hk => mem_ball_zero_iff.mpr (hs k hk)) hzero hinj
        (mem_ball_zero_iff.mpr hr.1) hne
      simpa [B, Complex.canonicalFactor_apply, inv_div] using h
    simpa [B] using ge_of_tendsto (hcont.continuousWithinAt : ContinuousWithinAt B (Iio 1) 1) hb
  · push Not at hne
    obtain ⟨k, hk, hzk⟩ := hne
    rw [hzk, hzero k hk, norm_zero,
      Finset.prod_eq_zero hk (by simp), mul_zero]

#print axioms norm_le_mul_prod

end D5.S3.Analytic.Hardy.FiniteBlaschkeBound
