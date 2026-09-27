/- GID: D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodVarianceBound
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodVarianceBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single-peak log-likelihood variance is uniformly controlled by information. -/
import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
open Finset Set
open D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance

/-- The forward and reverse single-peak path variances are at most twice their accumulated
information, including for paths with no transitions. -/
theorem uniform_single_peak_log_likelihood_variance_bound {X : Type*} [Fintype X]
    (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1)
    (r q : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (M : ℕ) (hcard : Fintype.card X = 2 * M)
    (hplus : (univ.filter fun x => chi x = 1).card = M) (hM : 2 ≤ M)
    (hq : q = r / ((M : ℝ) - 1)) :
    let P := kernel chi z r q (Fintype.card X)
    let k := (M : ℝ) - 1
    let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
    let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
    let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
    let Prev := Function.swap P
    let Lrev : (s : ℕ) → (Fin (s + 1) → X) → ℝ :=
      fun s x ↦ logLikelihoodSum chi z r q s (fun t ↦ x t.rev)
    (∀ u, |u| < 1 → psi u ≤ 2 * phi u) ∧
    J ≤ 0 ∧
    v ≤ 2 * I ∧
    0 ≤ I ∧
    (∀ s, pathVariance P s (logLikelihoodSum chi z r q s) ≤ 2 * s * I) ∧
    ∀ s, pathVariance Prev s (Lrev s) ≤ 2 * s * I := by
  let P := kernel chi z r q (Fintype.card X)
  let k := (M : ℝ) - 1
  let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
  let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
  let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
  let Prev := Function.swap P
  let Lrev : (s : ℕ) → (Fin (s + 1) → X) → ℝ :=
    fun s x ↦ logLikelihoodSum chi z r q s (fun t ↦ x t.rev)
  change (∀ u, |u| < 1 → psi u ≤ 2 * phi u) ∧ J ≤ 0 ∧ v ≤ 2 * I ∧ 0 ≤ I ∧
    (∀ s, pathVariance P s (logLikelihoodSum chi z r q s) ≤ 2 * s * I) ∧
    ∀ s, pathVariance Prev s (Lrev s) ≤ 2 * s * I
  have hphi_even (u : ℝ) : phi (-u) = phi u := by
    simp only [phi]
    ring
  have hpsi_even (u : ℝ) : psi (-u) = psi u := by
    simp only [psi]
    ring
  have hphi_deriv (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt phi ((Real.log (1 + u) - Real.log (1 - u)) / 2) u := by
    have hp : 0 < 1 + u := by linarith [hu.1]
    have hm : 0 < 1 - u := by linarith [hu.2]
    have hap := (hasDerivAt_id u).const_add 1
    have ham := (hasDerivAt_id u).const_sub 1
    have hplus := (Real.hasDerivAt_mul_log hp.ne').comp u hap
    have hminus := (Real.hasDerivAt_mul_log hm.ne').comp u ham
    have hraw := hplus.add hminus |>.const_mul (1 / 2)
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x ↦ by
        simp only [phi, Function.comp_apply, Pi.add_apply]
        ring
    · ring
  have hpsi_deriv (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt psi
        ((Real.log (1 + u) ^ 2 + 2 * Real.log (1 + u) -
          Real.log (1 - u) ^ 2 - 2 * Real.log (1 - u)) / 2) u := by
    have hp : 0 < 1 + u := by linarith [hu.1]
    have hm : 0 < 1 - u := by linarith [hu.2]
    have hap := (hasDerivAt_id u).const_add 1
    have ham := (hasDerivAt_id u).const_sub 1
    have hlp := hap.log hp.ne'
    have hlm := ham.log hm.ne'
    have hplus := hap.mul (hlp.pow 2)
    have hminus := ham.mul (hlm.pow 2)
    have hraw := hplus.add hminus |>.const_mul (1 / 2)
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x ↦ by
        simp only [psi, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
        ring
    · simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
      field_simp [hp.ne', hm.ne']
      ring
  have hgap_deriv (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun x : ℝ ↦ 2 * phi x - psi x)
        (-((Real.log (1 + u) - Real.log (1 - u)) / 2) * Real.log (1 - u ^ 2)) u := by
    have hp : 0 < 1 + u := by linarith [hu.1]
    have hm : 0 < 1 - u := by linarith [hu.2]
    have hlog : Real.log (1 - u ^ 2) = Real.log (1 + u) + Real.log (1 - u) := by
      rw [show 1 - u ^ 2 = (1 + u) * (1 - u) by ring, Real.log_mul hp.ne' hm.ne']
    have hraw := (hphi_deriv u hu).const_mul 2 |>.sub (hpsi_deriv u hu)
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x ↦ by
        simp only [Pi.sub_apply]
    · rw [hlog]
      ring
  have hgap_deriv_nonneg (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      0 ≤ -((Real.log (1 + u) - Real.log (1 - u)) / 2) * Real.log (1 - u ^ 2) := by
    have hp : 0 < 1 + u := by linarith [hu.1]
    have hm : 0 < 1 - u := by linarith [hu.2]
    have hfirst : 0 ≤ (Real.log (1 + u) - Real.log (1 - u)) / 2 := by
      have hlogle : Real.log (1 - u) ≤ Real.log (1 + u) :=
        Real.log_le_log hm (by linarith [hu.1] : 1 - u ≤ 1 + u)
      linarith
    have hsecond : Real.log (1 - u ^ 2) ≤ 0 :=
      Real.log_nonpos (by nlinarith [hu.1, hu.2]) (by nlinarith [sq_nonneg u])
    simpa only [neg_mul] using
      (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hfirst hsecond))
  have hgap_mono : MonotoneOn (fun u : ℝ ↦ 2 * phi u - psi u) (Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro u hu
      exact (hgap_deriv u ⟨by linarith [hu.1], hu.2⟩).continuousAt.continuousWithinAt
    · rw [interior_Ico]
      intro u hu
      exact (hgap_deriv u ⟨by linarith [hu.1], hu.2⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro u hu
      rw [(hgap_deriv u ⟨by linarith [hu.1], hu.2⟩).deriv]
      exact hgap_deriv_nonneg u hu
  have hpsi_phi (u : ℝ) (hu : |u| < 1) : psi u ≤ 2 * phi u := by
    have habs : |u| ∈ Ico (0 : ℝ) 1 := ⟨abs_nonneg u, hu⟩
    have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := by norm_num
    have h := hgap_mono hzero habs (abs_nonneg u)
    change 2 * phi 0 - psi 0 ≤ 2 * phi |u| - psi |u| at h
    have hphi_abs : phi |u| = phi u := by
      by_cases h : 0 ≤ u
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h), hphi_even]
    have hpsi_abs : psi |u| = psi u := by
      by_cases h : 0 ≤ u
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h), hpsi_even]
    have hgap_zero : 2 * phi 0 - psi 0 = 0 := by norm_num [phi, psi]
    rw [hgap_zero] at h
    rw [hphi_abs, hpsi_abs] at h
    linarith
  have hxi_deriv (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt xi (1 + (Real.log (1 + u) + Real.log (1 - u)) / 2) u := by
    have hp : 0 < 1 + u := by linarith [hu.1]
    have hm : 0 < 1 - u := by linarith [hu.2]
    have hap := (hasDerivAt_id u).const_add 1
    have ham := (hasDerivAt_id u).const_sub 1
    have hplus := (Real.hasDerivAt_mul_log hp.ne').comp u hap
    have hminus := (Real.hasDerivAt_mul_log hm.ne').comp u ham
    have hraw := hplus.sub hminus |>.const_mul (1 / 2)
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x ↦ by
        simp only [xi, Function.comp_apply, Pi.sub_apply]
        ring
    · ring
  have hxi_slope_deriv (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun x : ℝ ↦ 1 + (Real.log (1 + x) + Real.log (1 - x)) / 2)
        (-u / (1 - u ^ 2)) u := by
    have hp : 0 < 1 + u := by linarith [hu.1]
    have hm : 0 < 1 - u := by linarith [hu.2]
    have hden : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
    have hap := (hasDerivAt_id u).const_add 1
    have ham := (hasDerivAt_id u).const_sub 1
    have hlp := hap.log hp.ne'
    have hlm := ham.log hm.ne'
    have hraw := (hlp.add hlm).const_mul (1 / 2) |>.const_add 1
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x ↦ by
        simp only [Pi.add_apply, id_eq]
        ring
    · simp only [id_eq]
      field_simp [hp.ne', hm.ne', hden]
      ring
  have hxi_slope_anti :
      AntitoneOn (fun u : ℝ ↦ 1 + (Real.log (1 + u) + Real.log (1 - u)) / 2)
        (Ioo (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
    · intro u hu
      exact (hxi_slope_deriv u ⟨by linarith [hu.1], hu.2⟩).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      intro u hu
      exact (hxi_slope_deriv u ⟨by linarith [hu.1], hu.2⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro u hu
      rw [(hxi_slope_deriv u ⟨by linarith [hu.1], hu.2⟩).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu.1.le)
        (by nlinarith [hu.1, hu.2])
  have hxi_deriv_anti : AntitoneOn (deriv xi) (interior (Ico (0 : ℝ) 1)) := by
    rw [interior_Ico]
    intro a ha b hb hab
    rw [(hxi_deriv a ⟨by linarith [ha.1], ha.2⟩).deriv,
      (hxi_deriv b ⟨by linarith [hb.1], hb.2⟩).deriv]
    exact hxi_slope_anti ha hb hab
  have hxi_concave : ConcaveOn ℝ (Ico (0 : ℝ) 1) xi := by
    apply hxi_deriv_anti.concaveOn_of_deriv (convex_Ico 0 1)
    · intro u hu
      exact (hxi_deriv u ⟨by linarith [hu.1], hu.2⟩).continuousAt.continuousWithinAt
    · rw [interior_Ico]
      intro u hu
      exact (hxi_deriv u ⟨by linarith [hu.1], hu.2⟩).differentiableAt.differentiableWithinAt
  have hk : 1 ≤ k := by
    have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp only [k]
    linarith
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hqpos : 0 < q := by rw [hq]; exact div_pos hr0 hkpos
  have hqone : q < 1 := by rw [hq]; exact (div_le_self hr0.le hk).trans_lt hr1
  have hqabs : |q| < 1 := abs_lt.mpr ⟨by linarith [hqpos], hqone⟩
  have hJ : J ≤ 0 := by
    have hqk : q = r / k := by simpa only [k] using hq
    have hconcave := hxi_concave.2 (⟨hr0.le, hr1⟩ : r ∈ Ico (0 : ℝ) 1)
      (⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Ico (0 : ℝ) 1)
      (show 0 ≤ (1 / k : ℝ) by positivity)
      (show 0 ≤ (1 - 1 / k : ℝ) by rw [sub_nonneg, div_le_one hkpos]; exact hk)
      (show (1 / k : ℝ) + (1 - 1 / k) = 1 by ring)
    have hscaled' : (1 / k) * xi r ≤ xi ((1 / k) * r) := by
      simpa only [one_div, smul_eq_mul, xi, Real.log_one, mul_zero, sub_zero, zero_div,
        add_zero] using hconcave
    have hscaled : (1 / k) * xi r ≤ xi q := by
      rw [hqk]
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hscaled'
    have hxi : xi r ≤ k * xi q := by
      calc
        xi r = k * ((1 / k) * xi r) := by field_simp
        _ ≤ k * xi q := mul_le_mul_of_nonneg_left hscaled hkpos.le
    dsimp only [J]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxi) (Nat.cast_nonneg _)
  have hphi_nonneg (u : ℝ) (hu : |u| < 1) : 0 ≤ phi u := by
    have hp : 0 < 1 + u := by linarith [neg_lt_of_abs_lt hu]
    have hm : 0 < 1 - u := by linarith [lt_of_abs_lt hu]
    have hlp := Real.one_sub_inv_le_log_of_pos hp
    have hlm := Real.one_sub_inv_le_log_of_pos hm
    have hlp' := mul_le_mul_of_nonneg_left hlp hp.le
    have hlm' := mul_le_mul_of_nonneg_left hlm hm.le
    have hpne : 1 + u ≠ 0 := hp.ne'
    have hmne : 1 - u ≠ 0 := hm.ne'
    rw [phi]
    field_simp at hlp' hlm'
    nlinarith
  have hNpos : 0 < (Fintype.card X : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨z⟩)
  have hI : 0 ≤ I := by
    have hnum : 0 ≤ phi r + k * phi q :=
      add_nonneg (hphi_nonneg r (abs_lt.mpr ⟨by linarith, hr1⟩))
        (mul_nonneg hkpos.le (hphi_nonneg q hqabs))
    exact div_nonneg hnum hNpos.le
  have hv : v ≤ 2 * I := by
    have hrabs : |r| < 1 := abs_lt.mpr ⟨by linarith, hr1⟩
    have hnum : psi r + k * psi q ≤ 2 * (phi r + k * phi q) := by
      have hqr := mul_le_mul_of_nonneg_left (hpsi_phi q hqabs) hkpos.le
      nlinarith [hpsi_phi r hrabs]
    have hmoment : (psi r + k * psi q) / (Fintype.card X : ℝ) ≤ 2 * I := by
      dsimp only [I]
      apply (div_le_div_of_nonneg_right hnum hNpos.le).trans_eq
      ring
    dsimp only [v]
    nlinarith [sq_nonneg I]
  have hexact : ∀ s, 1 ≤ s →
      pathVariance P s (logLikelihoodSum chi z r q s) =
        (s : ℝ) * v + 2 * ((s - 1 : ℕ) : ℝ) * I * J := by
    simpa only [P, k, I, J, v] using
      (exact_single_peak_log_likelihood_covariances chi hchi z hz r q hr0 hr1 M hcard hplus
        hM hq).2.2.2.2.2
  have hforward : ∀ s, pathVariance P s (logLikelihoodSum chi z r q s) ≤ 2 * s * I := by
    intro s
    cases s with
    | zero => simp [pathVariance, pathCovariance, pathExpectation, logLikelihoodSum]
    | succ s =>
        rw [hexact (s + 1) (Nat.succ_le_succ (Nat.zero_le s))]
        have hsv : ((s + 1 : ℕ) : ℝ) * v ≤ ((s + 1 : ℕ) : ℝ) * (2 * I) :=
          mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (s + 1))
        have hcross : 2 * ((((s + 1 : ℕ) - 1 : ℕ)) : ℝ) * I * J ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) hI) hJ
        nlinarith
  have hweight_reverse (s : ℕ) (x : Fin (s + 1) → X) :
      pathWeight Prev s x = pathWeight P s (fun t ↦ x t.rev) := by
    unfold pathWeight
    congr 1
    rw [← Equiv.prod_comp Fin.revPerm
      (fun t : Fin s ↦ P (x t.succ) (x t.castSucc))]
    apply Finset.prod_congr rfl
    intro t _
    simp only [Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ]
  have hexpectation_reverse (s : ℕ) (f : (Fin (s + 1) → X) → ℝ) :
      pathExpectation Prev s (fun x ↦ f (fun t ↦ x t.rev)) = pathExpectation P s f := by
    unfold pathExpectation
    apply Fintype.sum_equiv (Fin.revPerm.arrowCongr (Equiv.refl X))
    intro x
    rw [hweight_reverse]
    change (pathWeight P s (fun t ↦ x t.rev) * f (fun t ↦ x t.rev)) =
      pathWeight P s (fun t ↦ x t.rev) * f (fun t ↦ x t.rev)
    rfl
  have hvariance_reverse (s : ℕ) :
      pathVariance Prev s (Lrev s) =
        pathVariance P s (logLikelihoodSum chi z r q s) := by
    unfold pathVariance pathCovariance
    rw [show Lrev s = fun x ↦ logLikelihoodSum chi z r q s (fun t ↦ x t.rev) by rfl]
    rw [hexpectation_reverse s
      (fun x ↦ logLikelihoodSum chi z r q s x * logLikelihoodSum chi z r q s x),
      hexpectation_reverse s (logLikelihoodSum chi z r q s)]
  refine ⟨hpsi_phi, hJ, hv, hI, hforward, ?_⟩
  intro s
  rw [hvariance_reverse]
  exact hforward s

#print axioms uniform_single_peak_log_likelihood_variance_bound

end D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
