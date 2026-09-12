/- GID: D5/S3/Analytic/Interpolation/FractionalBranchGeometry
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/FractionalBranchGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fractional row has a strict mean envelope and nested positive residual support. -/

import D5.S3.Analytic.Interpolation.QuadraticMajorantEnvelope

open Set
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.Interpolation.FractionalBranchGeometry

open TwoPointGridDominance EnvelopeKMonotone

/-- The logarithmic objective is strictly concave on the positive half-line. -/
theorem logValue_strictConcaveOn : StrictConcaveOn ℝ (Ioi 0) logValue := by
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0) hlog.1.continuousOn
  intro x hx
  have hxpos : 0 < x := interior_subset hx
  have hsecond := (hlog.2 x hxpos).2.1
  have he : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
  have hneg : -Real.exp x / (Real.exp x - 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos x)) (sq_pos_of_pos he)
  simpa only [logValue, iteratedDeriv_succ, iteratedDeriv_zero,
    Function.iterate_succ_apply, Function.iterate_zero, id_eq] using hsecond.trans_lt hneg

/-- A genuinely fractional row lies strictly below its mean vector and its variance envelope. -/
theorem fractional_mean_branch {k : ℕ} (hk : 2 ≤ k) (j : Fin k) (t : Fin k → ℝ)
    {c d θ μ V₀ : ℝ} (hc : 0 < c) (hcd : c < d) (ht : ∀ i, i ≠ j → 0 < t i)
    (hθ : θ ∈ Ioo 0 1)
    (hbudget : (1 - θ) * c + θ * d + ∑ i ∈ Finset.univ.erase j, t i = (k : ℝ) * μ)
    (hV₀ : 0 ≤ V₀)
    (hfloor : V₀ ≤ ((1 - θ) * c + θ * d - μ) ^ 2 +
      ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2) :
    let z := (1 - θ) * c + θ * d
    let y := Function.update t j z
    let V := (z - μ) ^ 2 + ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2
    (1 - θ) * logValue c + θ * logValue d +
        ∑ i ∈ Finset.univ.erase j, logValue (t i) < ∑ i, logValue (y i) ∧
      ∑ i, logValue (y i) ≤ psiK k μ V ∧ psiK k μ V ≤ psiK k μ V₀ := by
  dsimp only
  let z := (1 - θ) * c + θ * d
  let y := Function.update t j z
  have hcz : c < z := by dsimp [z]; nlinarith [hθ.1]
  have hy : ∀ i, 0 < y i := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa [y] using hc.trans hcz
    · simpa [y, hij] using ht i hij
  have hsplit (g : ℝ → ℝ) :
      ∑ i, g (y i) = g z + ∑ i ∈ Finset.univ.erase j, g (t i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp only [y, Function.update_self]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hsum : ∑ i, y i = (k : ℝ) * μ := by
    simpa only [id_eq] using (hsplit id).trans hbudget
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hmean : (∑ i, y i) / (k : ℝ) = μ := by
    rw [hsum, mul_div_cancel_left₀ _ (ne_of_gt hkpos)]
  have hμ : 0 < μ := by
    rw [← hmean]
    exact div_pos (Finset.sum_pos (fun i _ => hy i) ⟨j, Finset.mem_univ j⟩) hkpos
  have hvariance := hsplit (fun x => (x - μ) ^ 2)
  have hdomain := coordinate_variance_domain hk y hy
  dsimp only at hdomain
  rw [hmean, hvariance] at hdomain
  have hstrict := logValue_strictConcaveOn.2 hc (hc.trans hcd) hcd.ne
    (show 0 < 1 - θ by linarith [hθ.2]) hθ.1 (by ring)
  simp only [smul_eq_mul] at hstrict
  change _ < ∑ i, logValue (y i) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit logValue]
    exact add_lt_add_of_lt_of_le hstrict le_rfl
  · apply sum_logValue_le_psiK hk y hy hμ hmean.le
    · rw [hmean, hvariance]
    · exact hdomain.2
  · rcases lt_or_eq_of_le hfloor with hlt | heq
    · exact (psiK_strictAnti_variance hk hμ hV₀ hlt hdomain.2).le
    · rw [heq]

#print axioms logValue_strictConcaveOn
#print axioms fractional_mean_branch

end D5.S3.Analytic.Interpolation.FractionalBranchGeometry
