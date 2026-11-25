/- GID: D5/S3/Analytic/Laplace/LongWindowPoleExclusion
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/LongWindowPoleExclusion
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Arbitrarily late upper windows exclude simple poles of a signed Laplace transform. -/

import D5.S3.Analytic.Laplace.SignedWindowMoments
import D5.S3.Analytic.Isolation.VerticalNearestPole
import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Residues
import Mathlib.Analysis.Complex.Liouville
import D5.S3.Analytic.Laplace.LongWindowBounds

/-! # Pole exclusion from one-sided long windows

The actual signed integral and the meromorphic continuation have the same
derivatives in their common half-plane. A free real disk controls the negative
real moment, while an isolated pole gives a lower bound at a nearby center.
An isolated real pole is handled directly by its positive real residue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open D5.S3.Analytic.Laplace.PairedPoleRegularity (laplace)
open D5.S3.Analytic.Isolation.VerticalNearestPole
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes
  (removePoles removePoles_of_notMem removePoles_eventuallyEq_near_pole
    analyticAt_removePoles_of_notMem)
open D5.S3.Analytic.Laplace.LongWindowBounds (landau_window_contra)

namespace D5.S3.Analytic.Laplace.LongWindowPoleExclusion

/-- Subtracting finitely many prescribed simple principal parts leaves a single
analytic function on the entire domain, after filling in the finitely many
removable values. The local remainders need not agree away from their poles. -/
private theorem finite_principal_parts_analytic_remainder (F : ℂ → ℂ) (U : Set ℂ)
    (S : Finset ℂ) (c : ℂ → ℂ)
    (hF : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ F z)
    (hpart : ∀ r ∈ S, r ∈ U → ∃ H : ℂ → ℂ, AnalyticAt ℂ H r ∧
      F =ᶠ[𝓝[≠] r] fun z => c r / (z - r) + H z) :
    ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R U ∧
      ∀ z ∉ S, F z = (∑ r ∈ S, c r / (z - r)) + R z := by
  classical
  choose H hH hEq using hpart
  let limVal : ℂ → ℂ := fun r => if hr : r ∈ S ∧ r ∈ U then H r hr.1 hr.2 r else 0
  refine ⟨removePoles F S c limVal, ?_, ?_⟩
  · intro z hzU
    by_cases hz : z ∈ S
    · have hupdate : Function.update (fun x => F x - c z / (x - z)) z (limVal z)
          =ᶠ[𝓝 z] H z hz hzU := by
        have hlocal := eventually_nhdsWithin_iff.mp (hEq z hz hzU)
        filter_upwards [hlocal] with x hx
        by_cases hxz : x = z
        · subst x
          simp [limVal, hz, hzU]
        · rw [Function.update_of_ne hxz, hx hxz]
          ring
      have hfilled : AnalyticAt ℂ
          (Function.update (fun x => F x - c z / (x - z)) z (limVal z)) z :=
        (hH z hz hzU).congr hupdate.symm
      have hrest : AnalyticAt ℂ (fun x => ∑ r ∈ S.erase z, c r / (x - r)) z := by
        refine Finset.analyticAt_fun_sum _ fun r hr => ?_
        exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr (Finset.mem_erase.mp hr).1.symm)
      exact (hfilled.sub hrest).congr
        (removePoles_eventuallyEq_near_pole F S c limVal hz).symm
    · exact analyticAt_removePoles_of_notMem hz (hF z hzU hz)
  · intro z hz
    rw [removePoles_of_notMem F S c limVal hz]
    ring

/-- The analytic remainder after simultaneous finite pole subtraction has
uniform geometric Taylor-coefficient bounds on every closed disc in its domain. -/
private theorem finite_principal_parts_cauchy_bound (F : ℂ → ℂ) (U : Set ℂ)
    (S : Finset ℂ) (c : ℂ → ℂ)
    (hF : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ F z)
    (hpart : ∀ r ∈ S, r ∈ U → ∃ H : ℂ → ℂ, AnalyticAt ℂ H r ∧
      F =ᶠ[𝓝[≠] r] fun z => c r / (z - r) + H z)
    (z : ℂ) {e : ℝ} (he : 0 < e) (hU : Metric.closedBall z e ⊆ U) :
    ∃ R : ℂ → ℂ, ∃ M : ℝ, 0 ≤ M ∧ AnalyticOnNhd ℂ R U ∧
      (∀ x ∉ S, F x = (∑ r ∈ S, c r / (x - r)) + R x) ∧
      ∀ k : ℕ, ‖iteratedDeriv k R z‖ / (k.factorial : ℝ) ≤ M / e ^ k := by
  obtain ⟨R, hR, hEq⟩ := finite_principal_parts_analytic_remainder F U S c hF hpart
  have hcont : ContinuousOn R (Metric.sphere z e) :=
    hR.continuousOn.mono (Metric.sphere_subset_closedBall.trans hU)
  obtain ⟨M, hM⟩ := (isCompact_sphere z e).exists_bound_of_continuousOn hcont
  refine ⟨R, max M 0, le_max_right _ _, hR, hEq, ?_⟩
  intro k
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (C := max M 0) k he (hR.differentiableOn.diffContOnCl_ball hU)
    (fun x hx => (hM x hx).trans (le_max_left M 0))
  have hk : 0 < (k.factorial : ℝ) := by positivity
  apply (div_le_iff₀ hk).mpr
  convert hbound using 1
  ring

/-- The normalized derivative of a single simple principal part. -/
private theorem normalized_principal_deriv (k : ℕ) (c r z : ℂ) :
    iteratedDeriv k (fun x : ℂ => c / (x - r)) z / (k.factorial : ℂ) =
      (-1 : ℂ) ^ k * c / (z - r) ^ (k + 1) := by
  have hi : iteratedDeriv k (fun x : ℂ => (x - r)⁻¹) z =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) * (z - r) ^ (-1 - (k : ℤ)) := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul, one_pow, mul_one] using
      congrFun (iter_deriv_inv_linear_sub k (1 : ℂ) r) z
  have hp : (-1 - (k : ℤ)) = Int.negSucc k := by omega
  simp only [div_eq_mul_inv, iteratedDeriv_const_mul_field, hi, hp, zpow_negSucc]
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [hk]

/-- Every derivative coefficient of the original function is its finite pole
coefficient plus a remainder bounded geometrically by any available larger disc. -/
private theorem finite_pole_derivative_error (F : ℂ → ℂ) (U : Set ℂ)
    (S : Finset ℂ) (c : ℂ → ℂ)
    (hF : ∀ x ∈ U, x ∉ S → AnalyticAt ℂ F x)
    (hpart : ∀ r ∈ S, r ∈ U → ∃ H : ℂ → ℂ, AnalyticAt ℂ H r ∧
      F =ᶠ[𝓝[≠] r] fun x => c r / (x - r) + H x)
    (z : ℂ) (hz : z ∉ S) {e : ℝ} (he : 0 < e)
    (hU : Metric.closedBall z e ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ,
      ‖iteratedDeriv k F z / (k.factorial : ℂ) -
        ∑ r ∈ S, (-1 : ℂ) ^ k * c r / (z - r) ^ (k + 1)‖ ≤ M / e ^ k := by
  classical
  obtain ⟨R, M, hM, hR, hEq, hbound⟩ :=
    finite_principal_parts_cauchy_bound F U S c hF hpart z he hU
  let P : ℂ → ℂ := fun x => ∑ r ∈ S, c r / (x - r)
  have hP : AnalyticAt ℂ P z := by
    refine Finset.analyticAt_fun_sum _ fun r hr => ?_
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr fun h => hz (h.symm ▸ hr))
  have hRz : AnalyticAt ℂ R z := hR z (hU (Metric.mem_closedBall_self he.le))
  have hsame : F =ᶠ[𝓝 z] fun x => P x + R x := by
    have havoid : ∀ᶠ x in 𝓝 z, x ∉ S := S.isClosed.isOpen_compl.mem_nhds hz
    filter_upwards [havoid] with x hx
    exact hEq x hx
  refine ⟨M, hM, ?_⟩
  intro k
  have hPk : iteratedDeriv k P z / (k.factorial : ℂ) =
      ∑ r ∈ S, (-1 : ℂ) ^ k * c r / (z - r) ^ (k + 1) := by
    change iteratedDeriv k (fun x => ∑ r ∈ S, c r / (x - r)) z / _ = _
    rw [iteratedDeriv_fun_sum, Finset.sum_div]
    · exact Finset.sum_congr rfl fun r _ => normalized_principal_deriv k (c r) r z
    · intro r hr
      have har : AnalyticAt ℂ (fun x : ℂ => c r / (x - r)) z :=
        analyticAt_const.div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr fun h => hz (h.symm ▸ hr))
      exact har.contDiffAt
  have hk : iteratedDeriv k F z / (k.factorial : ℂ) -
      ∑ r ∈ S, (-1 : ℂ) ^ k * c r / (z - r) ^ (k + 1) =
        iteratedDeriv k R z / (k.factorial : ℂ) := by
    rw [hsame.iteratedDeriv_eq k, iteratedDeriv_fun_add hP.contDiffAt hRz.contDiffAt,
      add_div, hPk]
    ring
  rw [hk, norm_div, Complex.norm_natCast]
  exact hbound k

/-- The modulus of one isolated pole is bounded by the actual coefficient plus
the geometric Cauchy error, uniformly in every derivative order. -/
private theorem single_pole_coefficient_lower (F : ℂ → ℂ) (U : Set ℂ) (r c z : ℂ)
    (hF : ∀ x ∈ U, x ≠ r → AnalyticAt ℂ F x)
    (hpart : r ∈ U → ∃ H : ℂ → ℂ, AnalyticAt ℂ H r ∧
      F =ᶠ[𝓝[≠] r] fun x => c / (x - r) + H x)
    {e : ℝ} (he : 0 < e) (hU : Metric.closedBall z e ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ,
      (‖c‖ / ‖z - r‖) / ‖z - r‖ ^ k ≤
        ‖iteratedDeriv k F z / (k.factorial : ℂ)‖ + M / e ^ k := by
  classical
  by_cases hz : z = r
  · subst z
    exact ⟨0, le_rfl, fun k => by simp; positivity⟩
  obtain ⟨M, hM, hb⟩ := finite_pole_derivative_error F U {r} (fun _ => c)
    (by simpa only [Finset.mem_singleton] using hF)
    (by simpa only [Finset.mem_singleton, forall_eq] using hpart)
    z (by simpa only [Finset.mem_singleton] using hz) he hU
  refine ⟨M, hM, ?_⟩
  intro k
  have hb' : ‖iteratedDeriv k F z / (k.factorial : ℂ) -
      (-1 : ℂ) ^ k * c / (z - r) ^ (k + 1)‖ ≤ M / e ^ k := by
    simpa only [Finset.sum_singleton] using hb k
  have hnorm : ‖(-1 : ℂ) ^ k * c / (z - r) ^ (k + 1)‖ =
      (‖c‖ / ‖z - r‖) / ‖z - r‖ ^ k := by
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [pow_succ, div_div, mul_comm (‖z - r‖ ^ k)]
  rw [← hnorm]
  have h := norm_sub_norm_le
    ((-1 : ℂ) ^ k * c / (z - r) ^ (k + 1))
    (iteratedDeriv k F z / (k.factorial : ℂ))
  rw [norm_sub_rev] at h
  linarith

/-- At a real pole the real part of the complex residue gives a one-sided
lower bound for the real signed coefficient; no eventual-sign or subsequence
assumption is needed. -/
private theorem real_single_pole_coefficient_lower (F : ℂ → ℂ) (U : Set ℂ)
    (β σ : ℝ) (c : ℂ) (hF : ∀ x ∈ U, x ≠ (β : ℂ) → AnalyticAt ℂ F x)
    (hpart : (β : ℂ) ∈ U → ∃ H : ℂ → ℂ, AnalyticAt ℂ H β ∧
      F =ᶠ[𝓝[≠] (β : ℂ)] fun x => c / (x - β) + H x)
    (hz : σ ≠ β) {e : ℝ} (he : 0 < e)
    (hU : Metric.closedBall (σ : ℂ) e ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ,
      (c.re / (σ - β)) / (σ - β) ^ k ≤
        (((-1 : ℂ) ^ k * iteratedDeriv k F σ) / (k.factorial : ℂ)).re + M / e ^ k := by
  classical
  obtain ⟨M, hM, hb⟩ := finite_pole_derivative_error F U {(β : ℂ)} (fun _ => c)
    (by simpa only [Finset.mem_singleton] using hF)
    (by simpa only [Finset.mem_singleton, forall_eq] using hpart)
    (σ : ℂ) (by simpa only [Finset.mem_singleton, Complex.ofReal_inj] using hz) he hU
  refine ⟨M, hM, ?_⟩
  intro k
  let D : ℂ := iteratedDeriv k F σ / (k.factorial : ℂ)
  let P : ℂ := (-1 : ℂ) ^ k * c / ((σ : ℂ) - β) ^ (k + 1)
  have herr : ‖D - P‖ ≤ M / e ^ k := by
    simpa only [D, P, Finset.sum_singleton] using hb k
  have hs : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hP : ((-1 : ℂ) ^ k * P).re = (c.re / (σ - β)) / (σ - β) ^ k := by
    dsimp only [P]
    rw [← mul_div_assoc, ← mul_assoc, hs, one_mul]
    rw [show (σ : ℂ) - β = ((σ - β : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_succ, div_div]
    congr 1
    ring
  have hn : ‖(-1 : ℂ) ^ k * (P - D)‖ ≤ M / e ^ k := by
    simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_sub_rev] using herr
  have hr := (Complex.re_le_norm ((-1 : ℂ) ^ k * (P - D))).trans hn
  rw [mul_sub, Complex.sub_re, hP] at hr
  dsimp only [D] at hr
  rw [← mul_div_assoc] at hr
  linarith

private def coefficient (F : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv k F z / (k.factorial : ℂ)

private def alternating (F : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * coefficient F k z

private theorem derivative_eq {g : ℝ → ℝ} {F : ℂ → ℂ}
    (htransform : ∀ z : ℂ, 2 < z.re → laplace g z = F z)
    {z : ℂ} (hz : 2 < z.re) (k : ℕ) :
    iteratedDeriv k (laplace g) z = iteratedDeriv k F z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
    with w hw using htransform w hw

private theorem normalized_window_bound {g : ℝ → ℝ} {F : ℂ → ℂ}
    {M θ C b : ℝ} (hg : Measurable g)
    (hM : ∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (2 * u))
    (htransform : ∀ z : ℂ, 2 < z.re → laplace g z = F z)
    (hθ : 0 ≤ θ) (hb : 1 < b) :
    ∃ σ K : ℝ, 2 < σ ∧ θ < σ ∧ 0 ≤ K ∧
      ∀ U : ℝ, 1 ≤ U →
      (∀ u ∈ Icc U (b * U), g u ≤ C * Real.exp (θ * u)) →
      let k := ⌊σ * ((1 + b) / 2) * U⌋₊
      U ≤ k ∧ ∀ z : ℂ, z.re = σ →
        ‖coefficient F k z‖ + (alternating F k (σ : ℂ)).re ≤ K / (σ - θ) ^ k := by
  obtain ⟨σ, K, hσ, hθσ, hK, hbound⟩ :=
    SignedWindowMoments.long_window_moment_bound hg hM hθ hb
  refine ⟨σ, K, hσ, hθσ, hK, fun U hU hw => ?_⟩
  let k := ⌊σ * ((1 + b) / 2) * U⌋₊
  obtain ⟨hk, hmoment⟩ := hbound U hU hw
  refine ⟨hk, fun z hz => ?_⟩
  have hc : ∀ t : ℝ, 2 < t →
      IntegrableOn (fun u => g u * Real.exp (-t * u)) (Ici 0) :=
    fun t ht => SignedWindowMoments.growth_convergence hg hM ht
  have hreal := SignedMoments.alternating_derivative_real hg hc hσ k
  rw [derivative_eq htransform (by simpa using hσ) k] at hreal
  have hm := hmoment z hz
  rw [derivative_eq htransform (by simpa only [hz] using hσ) k, add_div] at hm
  change ‖coefficient F k z‖ + (alternating F k (σ : ℂ)).re ≤ K / (σ - θ) ^ k
  simp only [alternating, coefficient]
  rw [← mul_div_assoc, hreal, norm_div, Complex.norm_natCast]
  simpa only [k, div_eq_mul_inv, inv_pow] using hm

private theorem positive_re_of_mem_ball {c w : ℂ} {R : ℝ}
    (hR : R < c.re) (hw : w ∈ ball c R) : 0 < w.re := by
  have hnorm : ‖w - c‖ < R := by simpa only [dist_eq_norm] using mem_ball.mp hw
  have hre := (abs_le.mp (Complex.abs_re_le_norm (w - c))).1
  simp only [Complex.sub_re] at hre
  linarith

private theorem single_lower {F : ℂ → ℂ} {Z : Set ℂ} {residue : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → z ∉ Z → AnalyticAt ℂ F z)
    (hpole : ∀ ρ ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      F =ᶠ[𝓝[≠] ρ] fun z => residue ρ / (z - ρ) + H z)
    {c ρ : ℂ} {R e : ℝ} (hρ : ρ ∈ Z)
    (hR : R < c.re) (hisolate : ∀ w ∈ Z, w ∈ ball c R → w = ρ)
    (he : 0 < e) (heR : e < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ,
      (‖residue ρ‖ / ‖c - ρ‖) / ‖c - ρ‖ ^ k ≤
        ‖coefficient F k c‖ + M / e ^ k := by
  exact single_pole_coefficient_lower F (ball c R) ρ (residue ρ) c
    (fun w hw hn => hF w (positive_re_of_mem_ball hR hw) fun hwZ =>
      hn (hisolate w hwZ hw))
    (fun _ => hpole ρ hρ) he
    (fun w hw => mem_ball.mpr ((mem_closedBall.mp hw).trans_lt heR))

private theorem real_lower {F : ℂ → ℂ} {Z : Set ℂ} {residue : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → z ∉ Z → AnalyticAt ℂ F z)
    (hpole : ∀ ρ ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      F =ᶠ[𝓝[≠] ρ] fun z => residue ρ / (z - ρ) + H z)
    {σ β R e : ℝ} (hβ : (β : ℂ) ∈ Z) (hσβ : σ ≠ β)
    (hR : R < σ) (hisolate : ∀ w ∈ Z, w ∈ ball (σ : ℂ) R → w = (β : ℂ))
    (he : 0 < e) (heR : e < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ,
      ((residue (β : ℂ)).re / (σ - β)) / (σ - β) ^ k ≤
        (alternating F k (σ : ℂ)).re + M / e ^ k := by
  obtain ⟨M, hM, hb⟩ := real_single_pole_coefficient_lower F (ball (σ : ℂ) R)
    β σ (residue (β : ℂ))
    (fun w hw hn => hF w (positive_re_of_mem_ball (by simpa using hR) hw)
      fun hwZ => hn (hisolate w hwZ hw))
    (fun _ => hpole β hβ) hσβ he
    (fun w hw => mem_ball.mpr ((mem_closedBall.mp hw).trans_lt heR))
  exact ⟨M, hM, fun k => by
    simpa only [alternating, coefficient, ← mul_div_assoc] using hb k⟩

private theorem free_disk_bound {F : ℂ → ℂ} {Z : Set ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → z ∉ Z → AnalyticAt ℂ F z)
    {c : ℂ} {D e : ℝ} (hD : D < c.re)
    (hfree : ∀ w ∈ Z, D ≤ dist c w) (he : 0 < e) (heD : e < D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖coefficient F k c‖ ≤ M / e ^ k := by
  classical
  obtain ⟨M, hM, hbound⟩ := finite_pole_derivative_error F (ball c D) ∅ (fun _ => 0)
    (fun w hw _ => hF w (positive_re_of_mem_ball hD hw) fun hwZ =>
      not_lt_of_ge (hfree w hwZ) (by simpa only [dist_comm] using mem_ball.mp hw))
    (fun r hr => False.elim (Finset.notMem_empty r hr)) c (Finset.notMem_empty c)
    he (fun w hw => mem_ball.mpr ((mem_closedBall.mp hw).trans_lt heD))
  exact ⟨M, hM, fun k => by simpa only [coefficient, Finset.sum_empty, sub_zero] using hbound k⟩

/-- The actual derivatives, the nearest pole, and the window bounds supply
the quantitative estimate used in the long-window contradiction. -/
theorem long_window_pole_estimate {g : ℝ → ℝ} {F : ℂ → ℂ}
    {Z : Set ℂ} {residue : ℂ → ℂ} {M θ δ C : ℝ}
    (hg : Measurable g) (hM : ∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (2 * u))
    (htransform : ∀ z : ℂ, 2 < z.re → laplace g z = F z)
    (hZ : ∀ z ∈ Z, z.re ≤ 1)
    (hdiscrete : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    (hF : ∀ z : ℂ, 0 < z.re → z ∉ Z → AnalyticAt ℂ F z)
    (hpole : ∀ ρ ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      F =ᶠ[𝓝[≠] ρ] fun z => residue ρ / (z - ρ) + H z)
    (hresidue : ∀ ρ ∈ Z, residue ρ ≠ 0)
    (hreal : ∀ β : ℝ, (β : ℂ) ∈ Z → 0 < (residue (β : ℂ)).re)
    (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwindow : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u))
    (ρ : ℂ) (hρ : ρ ∈ Z) (hρright : θ < ρ.re) :
    ∃ σ c d e B K : ℝ, 2 < σ ∧ θ < σ ∧
      0 < c ∧ 0 < d ∧ d < e ∧ e < σ - θ ∧ 0 ≤ B ∧ 0 ≤ K ∧
      ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ 1 ≤ U ∧
        let k := ⌊σ * ((2 + δ) / 2) * U⌋₊
        U ≤ k ∧ c / d ^ k ≤ B / e ^ k + K / (σ - θ) ^ k := by
  obtain ⟨σ, K, hσ, hθσ, hK, hbound⟩ :=
    normalized_window_bound hg hM htransform hθ (by linarith : 1 < 1 + δ)
  have hleft : ∀ z ∈ Z, z.re < σ := fun z hz => (hZ z hz).trans_lt (by linarith)
  let ε := (θ + ρ.re) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hθε : θ < ε := by dsimp [ε]; linarith
  have hερ : ε < ρ.re := by dsimp [ε]; linarith
  have hDσ : σ - ε < σ := sub_lt_self σ hε
  rcases real_center_spectral_dichotomy hdiscrete hleft hε hρ hερ with
    ⟨D, hD, hDE, hfree, ρ₁, hρ₁, haccessible⟩ |
      ⟨β, hβ, hβright, R, hRnear, hRE, hisolate⟩
  · obtain ⟨t, _, r, hr, R, hnear, hRD, hisolate⟩ :=
      isolated_nearest_of_vertical_perturbation hdiscrete hleft
        (hDE.trans_lt hDσ) zero_lt_one hρ₁ haccessible
    let z := verticalCenter σ t
    let d := ‖z - r‖
    have hzre : z.re = σ := rfl
    have hzr : z ≠ r := by
      intro he
      have h := hleft r hr
      rw [← he, hzre] at h
      exact h.false
    have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hzr)
    have hdR : d < R := by simpa only [d, dist_eq_norm] using hnear
    let e := (d + R) / 2
    have hde : d < e := by dsimp [e]; linarith
    have heR : e < R := by dsimp [e]; linarith
    have he : 0 < e := hd.trans hde
    have heD : e < D := heR.trans_le hRD
    obtain ⟨B, hB, hlower⟩ := single_lower hF hpole hr
      (show R < z.re by rw [hzre]; linarith) hisolate he heR
    obtain ⟨A, hA, hupper⟩ := free_disk_bound hF
      (show D < (σ : ℂ).re by simpa only [Complex.ofReal_re] using hDE.trans_lt hDσ)
      hfree he heD
    have hcoefficient : 0 < ‖residue r‖ / d := div_pos
      (norm_pos_iff.mpr (hresidue r hr)) hd
    refine ⟨σ, ‖residue r‖ / d, d, e, A + B, K, hσ, hθσ,
      hcoefficient, hd, hde, ?_, add_nonneg hA hB, hK, ?_⟩
    · linarith [heD.trans_le hDE]
    intro U₀
    obtain ⟨U, hU, hw⟩ := hwindow (max U₀ 1)
    have hUone : 1 ≤ U := (le_max_right _ _).trans hU
    obtain ⟨hk, hmoment⟩ := hbound U hUone hw
    let k := ⌊σ * ((1 + (1 + δ)) / 2) * U⌋₊
    change ∃ V : ℝ, _ ∧ _ ∧
      V ≤ (⌊σ * ((2 + δ) / 2) * V⌋₊ : ℝ) ∧ _
    have hkeq : ⌊σ * ((2 + δ) / 2) * U⌋₊ = k := by
      dsimp [k]
      congr 1
      ring
    refine ⟨U, (le_max_left _ _).trans hU, hUone, ?_⟩
    rw [hkeq]
    refine ⟨hk, ?_⟩
    have hlowerk := hlower k
    have hrealbound : -(A / e ^ k) ≤ (alternating F k (σ : ℂ)).re := by
      have hre := (abs_le.mp (Complex.abs_re_le_norm (alternating F k (σ : ℂ)))).1
      have hn : ‖alternating F k (σ : ℂ)‖ = ‖coefficient F k (σ : ℂ)‖ := by
        simp [alternating, norm_pow]
      rw [hn] at hre
      linarith [hupper k]
    have hmain := hmoment z hzre
    change (‖residue r‖ / d) / d ^ k ≤ _
    change (‖residue r‖ / d) / d ^ k ≤ _ at hlowerk
    rw [add_div]
    linarith
  · let r : ℂ := β
    let d := σ - β
    have hd : 0 < d := sub_pos.mpr (by simpa only [r, Complex.ofReal_re] using hleft r hβ)
    have hdR : d < R := hRnear
    let e := (d + R) / 2
    have hde : d < e := by dsimp [e]; linarith
    have heR : e < R := by dsimp [e]; linarith
    have he : 0 < e := hd.trans hde
    have hσβ : σ ≠ β := sub_ne_zero.mp hd.ne'
    obtain ⟨B, hB, hlower⟩ := real_lower hF hpole hβ hσβ
      (hRE.trans_lt hDσ)
      hisolate he heR
    have hpositive : 0 < (residue r).re / d := div_pos (hreal β hβ) hd
    refine ⟨σ, (residue r).re / d, d, e, B, K, hσ, hθσ,
      hpositive, hd, hde, ?_, hB, hK, ?_⟩
    · linarith [heR.trans_le hRE]
    intro U₀
    obtain ⟨U, hU, hw⟩ := hwindow (max U₀ 1)
    have hUone : 1 ≤ U := (le_max_right _ _).trans hU
    obtain ⟨hk, hmoment⟩ := hbound U hUone hw
    let k := ⌊σ * ((1 + (1 + δ)) / 2) * U⌋₊
    change ∃ V : ℝ, _ ∧ _ ∧
      V ≤ (⌊σ * ((2 + δ) / 2) * V⌋₊ : ℝ) ∧ _
    have hkeq : ⌊σ * ((2 + δ) / 2) * U⌋₊ = k := by
      dsimp [k]
      congr 1
      ring
    refine ⟨U, (le_max_left _ _).trans hU, hUone, ?_⟩
    rw [hkeq]
    refine ⟨hk, ?_⟩
    have hlowerk := hlower k
    have hmain := hmoment (σ : ℂ) rfl
    change ((residue r).re / d) / d ^ k ≤ _
    change ((residue r).re / d) / d ^ k ≤ _ at hlowerk
    have hnonneg := norm_nonneg (coefficient F k (σ : ℂ))
    change _ ≤ (alternating F k (σ : ℂ)).re + _ at hlowerk
    linarith

/-- One-sided windows of arbitrary late occurrence exclude every pole to their right.
The analytic assumptions describe a continuation of the actual signed Laplace integral. -/
theorem long_window_pole_exclusion {g : ℝ → ℝ} {F : ℂ → ℂ}
    {Z : Set ℂ} {residue : ℂ → ℂ} {M θ δ C : ℝ}
    (hg : Measurable g) (hM : ∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (2 * u))
    (htransform : ∀ z : ℂ, 2 < z.re → laplace g z = F z)
    (hZ : ∀ z ∈ Z, z.re ≤ 1)
    (hdiscrete : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    (hF : ∀ z : ℂ, 0 < z.re → z ∉ Z → AnalyticAt ℂ F z)
    (hpole : ∀ ρ ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      F =ᶠ[𝓝[≠] ρ] fun z => residue ρ / (z - ρ) + H z)
    (hresidue : ∀ ρ ∈ Z, residue ρ ≠ 0)
    (hreal : ∀ β : ℝ, (β : ℂ) ∈ Z → 0 < (residue (β : ℂ)).re)
    (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwindow : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u)) :
    ∀ ρ ∈ Z, ¬ θ < ρ.re := by
  intro ρ hρ hρright
  obtain ⟨σ, c, d, e, B, K, _, _, hc, hd, hde, heE, _, hK, H⟩ :=
    long_window_pole_estimate hg hM htransform hZ hdiscrete hF hpole
      hresidue hreal hθ hδ hwindow ρ hρ hρright
  apply landau_window_contra (M := B) (C := K) hc hd hde (hde.trans heE)
  intro η hη U₀
  obtain ⟨U, hU, hUone, hk, hbound⟩ := H U₀
  let k := ⌊σ * ((2 + δ) / 2) * U⌋₊
  refine ⟨U, hU, k, hk, hbound.trans ?_⟩
  have hU0 : 0 ≤ U := by linarith
  have hE : 0 < σ - θ := (hd.trans hde).trans heE
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have hratio := div_le_div_of_nonneg_right (le_mul_of_one_le_right hK hexp)
    (pow_nonneg hE.le k)
  linarith


end D5.S3.Analytic.Laplace.LongWindowPoleExclusion
