/- GID: D5/S3/Observer/Linear/ReflectingHeatQuantileGramian
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatQuantileGramian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian, lake/module/D5.S3.Observer.Linear.ReflectingHeatCanonicalProduct]
   utility: none
   digest: The equal-mass multiplier bounds the physical inverse Gramian diagonal. -/

import D5.S3.Observer.Linear.ReflectingHeatCanonicalProduct
import D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-! The canonical multiplier in the physical reflecting heat moment problem. -/

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

open ReflectingHeatStripBound
open EqualMassBins

/-- The quantile product gives the physical inverse-Gramian upper bound on
every positive mode. The real-axis input expresses cancellation against the
exterior Joukowski root. The imaginary-axis input sets the half-width. -/
theorem inverse_diagonal_upper_bound_of_quantiles (n : ℕ) (j : Mode n) {a β F : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {density : ℝ → ℝ} (bins : EqualMassBins β density)
    (hcap : ∀ t ∈ Ici β, density t ≤ (n : ℝ) * a / (2 * Real.pi))
    (hwidth : ∀ y ≥ 0, imaginaryPotential β density y ≤ (n : ℝ) * a / 2 * y)
    (hgreen : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      realPotential β density |ω| + (n : ℝ) * Real.log ‖ζ‖ ≤ (n : ℝ) * F) :
    let q := rate n j
    let D := (n : ℝ) * a / (2 * Real.pi)
    Real.sqrt ((physicalGramian n (a / (n : ℝ)))⁻¹ j j) ≤
      (q * weight n j) * (1 + q ^ 2 / β ^ 2) * (Real.exp 2 * (n : ℝ)) *
        Real.sqrt ((n : ℝ) ^ 2 / 4 + 2 * D ^ 2) *
        Real.exp ((n : ℝ) * F + q * ((n : ℝ) * a) / 2 - imaginaryPotential β density q) := by
  let N : ℝ := n
  let L := N * a
  let D := L / (2 * Real.pi)
  let A := Real.exp 2 * Real.exp (N * F)
  let M := bins.canonicalProduct
  let q := rate n j
  let b := weight n j
  let V := imaginaryPotential β density q
  let P := 1 + q ^ 2 / β ^ 2
  let E := N ^ 2 / 4 + 2 * D ^ 2
  have hN : 0 < N := by
    have := j.isLt
    change 0 < (n : ℝ)
    exact_mod_cast (show 0 < n by omega)
  have hL : 0 < L := mul_pos hN ha
  have hD : 0 < D := div_pos hL (mul_pos (by norm_num) Real.pi_pos)
  have hA : 0 < A := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hP : 0 < P := by dsimp [P]; positivity
  have hπ : 0 < Real.sqrt (2 * Real.pi) := by positivity [Real.pi_pos]
  have he : Differentiable ℂ M := bins.canonicalProduct_entire hβ hD hcap
  have hm (ω : ℝ) : ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + D * |ω|) / ‖ζ‖ ^ n := by
    obtain ⟨ζ, hz, hroot, hr, hg⟩ := hgreen ω
    have hpos : 0 < ‖ζ‖ := zero_lt_one.trans_le hr
    refine ⟨ζ, hz, hroot, hr, ?_⟩
    apply (le_div_iff₀ (pow_pos hpos _)).2
    have hpow : Real.exp (N * Real.log ‖ζ‖) = ‖ζ‖ ^ n := by
      rw [Real.exp_nat_mul, Real.exp_log hpos]
    calc
      _ ≤ (Real.exp 2 * (1 + D * |ω|) * Real.exp (realPotential β density |ω|)) * ‖ζ‖ ^ n :=
        mul_le_mul_of_nonneg_right (bins.canonicalProduct_real_bound hβ hD hcap ω) (by positivity)
      _ = Real.exp 2 * (1 + D * |ω|) *
          Real.exp (realPotential β density |ω| + N * Real.log ‖ζ‖) := by
        rw [Real.exp_add, hpow]; ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hg)
          (show 0 ≤ Real.exp 2 * (1 + D * |ω|) by positivity)
        convert h using 1
        dsimp [A]
        ring
  have hnode : Real.exp V / P ≤ ‖M (-(q : ℂ) * Complex.I)‖ := by
    have h := (bins.canonicalProduct_imaginary_bounds hβ hD hcap (-q)).1
    simpa only [imaginaryPotential, neg_sq, Complex.ofReal_neg, Real.exp_sub, Real.exp_log hP,
      V, P] using h
  have hMpos : 0 < ‖M (-(q : ℂ) * Complex.I)‖ :=
    (div_pos (Real.exp_pos _) hP).trans_le hnode
  have hnprime : 0 < |nodalDerivative n j| :=
    (by linarith : 0 < N / 2).trans_le (uniform_nodal_factors n j).1
  have hAj : (nodalDerivative n j : ℂ) * M (-(q : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (abs_pos.mp hnprime)) (norm_pos_iff.mp hMpos)
  obtain ⟨_, _, _, _, _, hW⟩ := inverse_diagonal_upper_bound n j M he hL hA.le
    (C := 1) (m := 0)
    (fun z => by simpa using bins.canonicalProduct_half_width hβ hD hcap hwidth z)
    hm hAj
  have hL2 := (momentInterpolant_L2_bound n j M
    (he.continuous.comp Complex.continuous_ofReal).measurable hm).2
  have hnorm : Real.sqrt (∫ ω : ℝ, ‖momentInterpolant n j M (ω : ℂ)‖ ^ 2) ≤
      N * A * Real.sqrt (2 * Real.pi) * Real.sqrt E := by
    calc
      _ ≤ Real.sqrt (2 * (N * A) ^ 2 * Real.pi * E) := Real.sqrt_le_sqrt hL2
      _ = _ := by
        rw [show 2 * (N * A) ^ 2 * Real.pi * E = (N * A) ^ 2 * (2 * Real.pi) * E by ring,
          Real.sqrt_mul (mul_nonneg (sq_nonneg _) (by positivity [Real.pi_pos])),
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hN.le hA.le)]
  have hT : L / N ^ 2 = a / N := by
    dsimp [L]
    field_simp
  have hb : 0 < b := weight_pos n j
  change Real.sqrt ((physicalGramian n (L / N ^ 2))⁻¹ j j) ≤ _ at hW
  rw [hT, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hW
  change Real.sqrt ((physicalGramian n (a / N))⁻¹ j j) ≤
    (q * b) * P * (Real.exp 2 * N) * Real.sqrt E * Real.exp (N * F + q * L / 2 - V)
  refine hW.trans ?_
  have hfac : N / (b * |nodalDerivative n j|) = q * b :=
    (endpoint_normalization n j).1
  have hpos : 0 ≤ q * b := mul_nonneg (rate_pos n j).le hb.le
  calc
    _ ≤ N * Real.exp (q * L / 2) /
          (b * (|nodalDerivative n j| * ‖M (-(q : ℂ) * Complex.I)‖) *
            Real.sqrt (2 * Real.pi)) * (N * A * Real.sqrt (2 * Real.pi) * Real.sqrt E) :=
      mul_le_mul_of_nonneg_left hnorm
        (div_nonneg (by positivity) (by positivity))
    _ = (q * b) * (Real.exp (q * L / 2) * (N * A) * Real.sqrt E) /
          ‖M (-(q : ℂ) * Complex.I)‖ := by
      rw [← hfac]
      field_simp [hb.ne', hnprime.ne', hMpos.ne', hπ.ne']
    _ ≤ (q * b) * (Real.exp (q * L / 2) * (N * A) * Real.sqrt E) / (Real.exp V / P) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos (Real.exp_pos _) hP) hnode
    _ = _ := by
      rw [Real.exp_sub, Real.exp_add]
      dsimp [A]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

open D5.S3.Analytic.Hardy.FiniteStripMomentBound (radius)

/-- The arcsine spectral average, in its regular angular coordinate. -/
def spectralAverage (f : ℝ → ℝ) : ℝ :=
  (∫ θ in 0..Real.pi, f (2 - 2 * Real.cos θ)) / Real.pi

/-- The continuum saddle exponent at mode rate `q` and saddle radius `β`. -/
def saddleRate (a β q : ℝ) : ℝ :=
  spectralAverage (fun r => Real.log (radius β q + radius β r)) - a / 2 * (radius β q - q)

private theorem rightEndpoint_average_le (n : ℕ) (hn : 0 < (n : ℝ))
    {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 Real.pi)) (hm : MonotoneOn f (Icc 0 Real.pi)) :
    (n : ℝ) * (∫ θ in 0..Real.pi, f θ) / Real.pi ≤
      ∑ k ∈ Finset.range n, f (((k + 1 : ℕ) : ℝ) * Real.pi / n) := by
  let t (k : ℕ) := (k : ℝ) * Real.pi / n
  have ht0 : t 0 = 0 := by simp [t]
  have htn : t n = Real.pi := by dsimp [t]; field_simp
  have htmono : Monotone t := by
    intro k l hkl
    dsimp [t]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) Real.pi_pos.le) hn.le
  have hsub {k : ℕ} (hk : k < n) : Icc (t k) (t (k + 1)) ⊆ Icc 0 Real.pi :=
    Icc_subset_Icc (ht0 ▸ htmono (Nat.zero_le k)) (htn ▸ htmono (Nat.succ_le_of_lt hk))
  have hi (k : ℕ) (hk : k < n) : IntervalIntegrable f volume (t k) (t (k + 1)) :=
    (hc.mono (hsub hk)).intervalIntegrable_of_Icc (htmono (Nat.le_succ k))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := t) hi
  rw [ht0, htn] at hsum
  have hb (k : ℕ) (hk : k < n) :
      (∫ x in t k..t (k + 1), f x) ≤ Real.pi / n * f (t (k + 1)) := by
    have hle := htmono (Nat.le_succ k)
    have h := intervalIntegral.integral_mono_on hle (hi k hk) intervalIntegrable_const
      (fun x hx => hm (hsub hk hx) (hsub hk (right_mem_Icc.mpr hle)) hx.2)
    rwa [intervalIntegral.integral_const, smul_eq_mul,
      show t (k + 1) - t k = Real.pi / n by dsimp [t]; push_cast; ring] at h
  have he : (∫ θ in 0..Real.pi, f θ) ≤
      (Real.pi / n) * ∑ k ∈ Finset.range n, f (t (k + 1)) := by
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hb k (Finset.mem_range.mp hk)
  apply (div_le_iff₀ Real.pi_pos).2
  calc
    _ ≤ (n : ℝ) * (Real.pi / n * ∑ k ∈ Finset.range n, f (t (k + 1))) :=
      mul_le_mul_of_nonneg_left he hn.le
    _ = _ := by
      change (n : ℝ) * (Real.pi / n * ∑ k ∈ Finset.range n, f (t (k + 1))) =
        (∑ k ∈ Finset.range n, f (t (k + 1))) * Real.pi
      field_simp

private theorem angular_product_lower (n : ℕ) (j : Mode n) {β : ℝ} (hβ : 0 < β) :
    Real.exp ((n : ℝ) * spectralAverage (fun r => Real.log (radius β (rate n j) + radius β r))) /
        (radius β (rate n j) + radius β 4) ^ 2 ≤
      ∏ k ∈ Finset.univ.erase j, (radius β (rate n j) + radius β (rate n k)) := by
  let p (θ : ℝ) := 2 - 2 * Real.cos θ
  let R (r : ℝ) := radius β (rate n j) + radius β r
  let f (θ : ℝ) := Real.log (R (p θ))
  have hR (r : ℝ) : 0 < R r := by
    unfold R radius
    positivity
  have hc : Continuous f := by
    apply Continuous.log (by dsimp [R, p, radius]; fun_prop)
    exact fun x => (hR (p x)).ne'
  have hm : MonotoneOn f (Icc 0 Real.pi) := by
    intro x hx y hy hxy
    have hcos := Real.antitoneOn_cos hx hy hxy
    have hpx : 0 ≤ p x := by dsimp [p]; linarith [Real.cos_le_one x]
    have hp : p x ≤ p y := by dsimp [p]; linarith
    apply Real.log_le_log (hR _)
    unfold R radius
    exact add_le_add_right (Real.sqrt_le_sqrt
      (add_le_add_left (pow_le_pow_left₀ hpx hp 2) _)) _
  have hnp : 0 < n := by have := j.isLt; omega
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnp
  have hstep : n - 1 + 1 = n := by omega
  have hlast : (((n - 1 + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) = Real.pi := by
    rw [hstep]
    field_simp
  have hquad := rightEndpoint_average_le n hn hc.continuousOn hm
  have he : (∑ k ∈ Finset.range n, f (((k + 1 : ℕ) : ℝ) * Real.pi / n)) =
      (∑ k : Mode n, f (angle n k)) + f Real.pi := by
    have hsplit := Finset.sum_range_succ (fun k : ℕ => f (((k + 1 : ℕ) : ℝ) * Real.pi / n)) (n - 1)
    rw [hlast, hstep] at hsplit
    change _ = (∑ k : Fin (n - 1), (fun k : ℕ => f (((k + 1 : ℕ) : ℝ) * Real.pi / n)) k) + f Real.pi
    have hfin := Fin.sum_univ_eq_sum_range
      (fun k : ℕ => f (((k + 1 : ℕ) : ℝ) * Real.pi / n)) (n - 1)
    exact hsplit.trans (congrArg (fun y => y + f Real.pi) hfin.symm)
  have hjπ : f (angle n j) ≤ f Real.pi :=
    hm ⟨(angle_mem n j).1.le, (angle_mem n j).2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ (angle_mem n j).2.le
  rw [he, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hquad
  have hRp : p Real.pi = 4 := by norm_num [p, Real.cos_pi]
  have hfπ : f Real.pi = Real.log (R 4) := by dsimp only [f]; rw [hRp]
  have hJ : (n : ℝ) * spectralAverage (fun r => Real.log (R r)) - 2 * Real.log (R 4) ≤
      ∑ k ∈ Finset.univ.erase j, Real.log (R (rate n k)) := by
    change _ ≤ ∑ k ∈ Finset.univ.erase j, f (angle n k)
    unfold spectralAverage
    change (n : ℝ) * ((∫ θ in 0..Real.pi, f θ) / Real.pi) - 2 * Real.log (R 4) ≤ _
    rw [hfπ, mul_div_assoc] at hquad
    rw [hfπ] at hjπ
    linarith
  have hex := Real.exp_le_exp.mpr hJ
  have hden : Real.exp (2 * Real.log (R 4)) = R 4 ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log (hR 4), pow_two]
  rw [Real.exp_sub, hden, Real.exp_sum] at hex
  simpa only [Real.exp_log (hR _), R] using hex

/-- The finite strip lower bound gives the continuum saddle exponent with
an explicit loss from the two removed endpoints of the monotone quadrature. -/
theorem inverse_diagonal_lower_bound_at_saddle (n : ℕ) (j : Mode n) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    (rate n j * weight n j) * Real.exp ((n : ℝ) * saddleRate a β (rate n j)) /
      ((radius β (rate n j) + radius β 4) ^ 2 * Real.sqrt ((n : ℝ) * a)) ≤
        Real.sqrt ((physicalGramian n (a / (n : ℝ)))⁻¹ j j) := by
  let q := rate n j
  let b := weight n j
  let S := (radius β q + radius β 4) ^ 2
  let L := (n : ℝ) * a
  let J := spectralAverage (fun r => Real.log (radius β q + radius β r))
  let E := Real.exp (-(n : ℝ) * a * (radius β q - q) / 2)
  have hn : 2 ≤ n := by have := j.isLt; omega
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : 0 < b := weight_pos n j
  have hnd : 0 < |nodalDerivative n j| :=
    (half_pos hn').trans_le (uniform_nodal_factors n j).1
  have hL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (mul_pos hn' ha)
  have h := inverse_diagonal_lower_bound n hn ha hβ j
  rw [Finset.prod_div_distrib, ← Finset.abs_prod, ← nodalDerivative] at h
  refine le_trans ?_ h
  have hnorm : (n : ℝ) / (b * |nodalDerivative n j|) = q * b :=
    (endpoint_normalization n j).1
  have hp := angular_product_lower n j hβ
  change q * b * Real.exp ((n : ℝ) * saddleRate a β q) / (S * Real.sqrt L) ≤
    (n : ℝ) / b *
      ((∏ k ∈ Finset.univ.erase j, (radius β q + radius β (rate n k))) /
        |nodalDerivative n j| * E / Real.sqrt L)
  rw [show Real.exp ((n : ℝ) * saddleRate a β q) = Real.exp ((n : ℝ) * J) * E by
    unfold saddleRate E J
    rw [← Real.exp_add]
    congr 1
    ring]
  calc
    _ = q * b * (Real.exp ((n : ℝ) * J) / S) * E / Real.sqrt L := by ring
    _ ≤ q * b * (∏ k ∈ Finset.univ.erase j, (radius β q + radius β (rate n k))) * E /
        Real.sqrt L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (mul_nonneg (rate_pos n j).le hb.le)) (Real.exp_pos _).le) hL.le
    _ = _ := by rw [← hnorm]; ring

set_option maxHeartbeats 500000 in
-- Expanding the two logarithmic prefactors exceeds the default limit.
/-- The two estimates give a common logarithmic loss uniform in the
positive mode and in the window parameter. The potential assumptions are the
continuum saddle identities used on the two axes. -/
theorem log_inverse_diagonal_error_of_quantiles (n : ℕ) (j : Mode n) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβupper : β ≤ 2 / a)
    (hβinv : β⁻¹ ≤ 16 * max 1 (a ^ 2))
    {density : ℝ → ℝ} (bins : EqualMassBins β density)
    (hcap : ∀ t ∈ Ici β, density t ≤ (n : ℝ) * a / (2 * Real.pi))
    (hwidth : ∀ y ≥ 0, imaginaryPotential β density y ≤ (n : ℝ) * a / 2 * y)
    (hgreen : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      realPotential β density |ω| + (n : ℝ) * Real.log ‖ζ‖ ≤ (n : ℝ) * saddleRate a β 0)
    (hvalue : imaginaryPotential β density (rate n j) =
      (n : ℝ) * (saddleRate a β 0 + a * rate n j / 2 - saddleRate a β (rate n j))) :
    |Real.log (Real.sqrt ((physicalGramian n (a / (n : ℝ)))⁻¹ j j)) -
      (n : ℝ) * saddleRate a β (rate n j)| ≤
        20 * (1 + Real.log (n : ℝ) + |Real.log a|) := by
  let N : ℝ := n
  let q := rate n j
  let b := weight n j
  let D := N * a / (2 * Real.pi)
  let W := Real.sqrt ((physicalGramian n (a / N))⁻¹ j j)
  let v := N * saddleRate a β q
  let p := max a a⁻¹
  have hN : 1 ≤ N := by
    have := j.isLt
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast (show 1 ≤ n by omega)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have ha_p : a ≤ p := le_max_left _ _
  have hai_p : a⁻¹ ≤ p := le_max_right _ _
  have hp : 1 ≤ p := by
    rcases le_total 1 a with h | h
    · exact h.trans ha_p
    · exact (one_le_inv₀ ha).2 h |>.trans hai_p
  have hpp : 0 < p := zero_lt_one.trans_le hp
  have hlp : Real.log p = |Real.log a| := by
    rcases le_total 1 a with h | h
    · have hi : a⁻¹ ≤ a := (inv_le_one_of_one_le₀ h).trans h
      change Real.log (max a a⁻¹) = _
      rw [max_eq_left hi, abs_of_nonneg (Real.log_nonneg h)]
    · have hi : a ≤ a⁻¹ := h.trans ((one_le_inv₀ ha).2 h)
      change Real.log (max a a⁻¹) = _
      rw [max_eq_right hi, Real.log_inv, abs_of_nonpos (Real.log_nonpos ha.le h)]
  have hq : 0 < q := rate_pos n j
  have hq4 : q ≤ 4 := by
    change 2 - 2 * Real.cos (angle n j) ≤ 4
    linarith [Real.neg_one_le_cos (angle n j)]
  have hb : 0 < b := weight_pos n j
  have hb2 : b ≤ 2 := by
    change Real.sqrt (2 - q / 2) ≤ 2
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hqb : q * b ≤ 8 := by
    exact (mul_le_mul hq4 hb2 hb.le (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by norm_num)
  have hp2 : 1 ≤ p ^ 2 := by simpa using pow_le_pow_left₀ zero_le_one hp 2
  have hp4 : 1 ≤ p ^ 4 := by simpa using pow_le_pow_left₀ zero_le_one hp 4
  have hi : β⁻¹ ≤ 16 * p ^ 2 :=
    hβinv.trans (mul_le_mul_of_nonneg_left
      (max_le hp2 (pow_le_pow_left₀ ha.le ha_p 2)) (by norm_num))
  have hP : 1 + q ^ 2 / β ^ 2 ≤ (8192 : ℝ) * p ^ 4 := by
    have hmul : q * β⁻¹ ≤ 64 * p ^ 2 := by
      exact (mul_le_mul hq4 hi (inv_nonneg.mpr hβ.le) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
        (by ring)
    have hs := pow_le_pow_left₀ (mul_nonneg hq.le (inv_nonneg.mpr hβ.le)) hmul 2
    rw [mul_pow, inv_pow, ← div_eq_mul_inv] at hs
    nlinarith
  have hD0 : 0 ≤ D := by dsimp [D]; positivity [Real.pi_pos]
  have hD : D ≤ N * p / 2 := by
    dsimp [D]
    calc
      _ ≤ N * a / 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hNp.le ha.le) (by norm_num)
          (by linarith [Real.pi_gt_three])
      _ ≤ _ := by gcongr
  have hE : Real.sqrt (N ^ 2 / 4 + 2 * D ^ 2) ≤ N * p := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hd := pow_le_pow_left₀ hD0 hD 2
    have hbase := mul_le_mul_of_nonneg_left hp2 (sq_nonneg N)
    nlinarith
  have hUpper := inverse_diagonal_upper_bound_of_quantiles n j ha hβ bins hcap hwidth hgreen
  dsimp only at hUpper
  rw [hvalue] at hUpper
  have hv : N * saddleRate a β 0 + q * (N * a) / 2 -
      N * (saddleRate a β 0 + a * q / 2 - saddleRate a β q) = v := by
    dsimp [v]
    ring
  have hUpper' : W ≤ (q * b) * (1 + q ^ 2 / β ^ 2) * (Real.exp 2 * N) *
      Real.sqrt (N ^ 2 / 4 + 2 * D ^ 2) * Real.exp v := by
    exact hv ▸ hUpper
  have hUpper'' : W ≤ (Real.exp 2 * (2 : ℝ) ^ 16 * N ^ 2 * p ^ 5) * Real.exp v := by
    refine hUpper'.trans ?_
    calc
      _ ≤ (8 * (8192 * p ^ 4)) * (Real.exp 2 * N) * (N * p) * Real.exp v := by
        gcongr
      _ = _ := by ring
  have hβp : β ≤ 2 * p := hβupper.trans (by rw [div_eq_mul_inv]; gcongr)
  have hS : (radius β q + radius β 4) ^ 2 ≤ 80 * p ^ 2 := by
    have hR : radius β q ≤ radius β 4 := by
      unfold radius
      exact Real.sqrt_le_sqrt (add_le_add_left (pow_le_pow_left₀ hq.le hq4 2) _)
    have hr0 : 0 ≤ radius β q := Real.sqrt_nonneg _
    have hr := pow_le_pow_left₀ (add_nonneg hr0 (Real.sqrt_nonneg _))
      (add_le_add_right hR _) 2
    have hb_sq := pow_le_pow_left₀ hβ.le hβp 2
    have hR_sq : radius β 4 ^ 2 = 16 + β ^ 2 := by
      unfold radius
      rw [Real.sq_sqrt (by positivity)]
      norm_num
    nlinarith
  have hL : Real.sqrt (N * a) ≤ N * p := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have h : 1 ≤ N * p := by simpa using mul_le_mul hN hp zero_le_one hNp.le
    nlinarith [mul_le_mul_of_nonneg_left ha_p hNp.le, sq_nonneg (N * p - 1),
      mul_nonneg (sub_nonneg.mpr h) (mul_nonneg hNp.le hpp.le)]
  have hSpos : 0 < (radius β q + radius β 4) ^ 2 := by
    unfold radius
    positivity
  have hLpos : 0 < Real.sqrt (N * a) := by positivity
  have hqlower : 4 / N ^ 2 ≤ q * b := (endpoint_normalization n j).2
  have hLower : Real.exp v / ((2 : ℝ) ^ 5 * N ^ 3 * p ^ 3) ≤ W := by
    refine le_trans ?_ (inverse_diagonal_lower_bound_at_saddle n j ha hβ)
    change _ ≤ q * b * Real.exp v / ((radius β q + radius β 4) ^ 2 * Real.sqrt (N * a))
    calc
      _ ≤ Real.exp v / (20 * N ^ 3 * p ^ 3) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (by gcongr; norm_num)
      _ = (4 / N ^ 2) * Real.exp v / ((80 * p ^ 2) * (N * p)) := by
        field_simp
        ring
      _ ≤ _ := by
        apply div_le_div₀ (by positivity) _ (mul_pos hSpos hLpos)
        · exact mul_le_mul_of_nonneg_left hL (by positivity) |>.trans
            (mul_le_mul_of_nonneg_right hS (by positivity))
        · exact mul_le_mul_of_nonneg_right hqlower (Real.exp_pos _).le
  have hW : 0 < W := (div_pos (Real.exp_pos _) (by positivity)).trans_le hLower
  have hlo := Real.log_le_log (div_pos (Real.exp_pos v)
    (show 0 < (2 : ℝ) ^ 5 * N ^ 3 * p ^ 3 by positivity)) hLower
  have hhi := Real.log_le_log hW hUpper''
  rw [Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlo
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_pow, Real.log_pow] at hhi
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    norm_num at h
    exact h
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp
  change |Real.log W - v| ≤ 20 * (1 + Real.log N + |Real.log a|)
  rw [← hlp, abs_le]
  norm_num at hlo hhi
  constructor <;> linarith

/-- The scalar function in the stationarity equation for the continuum saddle. -/
def saddleMass (β : ℝ) : ℝ := spectralAverage (fun r => (radius β r)⁻¹)

private theorem saddle_radius_bounds {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hs : saddleMass β = a / 2) :
    β ≤ 2 / a ∧ β⁻¹ ≤ 16 * max 1 (a ^ 2) := by
  let f (θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hr (r : ℝ) : β ≤ radius β r := by
    unfold radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by linarith [sq_nonneg r])
  have hf : Continuous f := by
    apply Continuous.inv₀ (by dsimp [radius]; fun_prop)
    exact fun x => (hβ.trans_le (hr _)).ne'
  have hm : (∫ θ in 0..Real.pi, f θ) / Real.pi = a / 2 := hs
  have hπ : 0 < Real.pi := Real.pi_pos
  have hle := intervalIntegral.integral_mono_on (μ := volume) hπ.le
    (hf.intervalIntegrable _ _) (intervalIntegrable_const (c := β⁻¹))
    (fun x _ => inv_anti₀ hβ (hr (2 - 2 * Real.cos x)))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
  have hc : a / 2 ≤ β⁻¹ := by
    rw [← hm, div_le_iff₀ hπ, mul_comm]
    exact hle
  constructor
  · rw [le_div_iff₀ ha]
    have := (le_div_iff₀ hβ).1 (show a / 2 ≤ 1 / β by simpa using hc)
    linarith
  · by_cases hβ1 : β ≤ 1
    · let w := Real.sqrt β
      have hw : 0 < w := Real.sqrt_pos.2 hβ
      have hw1 : w ≤ 1 := by simpa [w] using Real.sqrt_le_sqrt hβ1
      have hwπ : w ≤ Real.pi := hw1.trans (by linarith [Real.pi_gt_three])
      have hw_sq : w ^ 2 = β := Real.sq_sqrt hβ.le
      have hg (x : ℝ) (hx : x ∈ Icc 0 w) : (2 * β)⁻¹ ≤ f x := by
        have hp0 : 0 ≤ 2 - 2 * Real.cos x := by linarith [Real.cos_le_one x]
        have hpβ : 2 - 2 * Real.cos x ≤ β := by
          have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
          have hxw := pow_le_pow_left₀ hx.1 hx.2 2
          linarith
        apply inv_anti₀ (hβ.trans_le (hr _))
        unfold radius
        refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
        nlinarith [pow_le_pow_left₀ hp0 hpβ 2]
      have hpart := intervalIntegral.integral_mono_on (μ := volume) hw.le
        (intervalIntegrable_const (c := (2 * β)⁻¹)) (hf.intervalIntegrable _ _) hg
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hpart
      have htail : 0 ≤ ∫ x in w..Real.pi, f x :=
        intervalIntegral.integral_nonneg hwπ
          (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
      have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hf.intervalIntegrable (0 : ℝ) w) (hf.intervalIntegrable w Real.pi)
      have hfull : w * (2 * β)⁻¹ ≤ ∫ x in 0..Real.pi, f x := by linarith
      have heq := (div_eq_iff hπ.ne').1 hm
      have hwa : 1 ≤ Real.pi * a * w := by
        have h := (div_le_iff₀ (by positivity : 0 < 2 * β)).1
          (show w / (2 * β) ≤ a / 2 * Real.pi by rw [div_eq_mul_inv, ← heq]; exact hfull)
        have h' : w * 1 ≤ w * (Real.pi * a * w) := by
          rw [show w * (Real.pi * a * w) = a / 2 * Real.pi * (2 * β) by
            rw [← hw_sq]; ring]
          simpa using h
        exact le_of_mul_le_mul_left h' hw
      have hwi : w⁻¹ ≤ Real.pi * a := by
        rw [inv_eq_one_div]
        exact (div_le_iff₀ hw).2 hwa
      have hbi : β⁻¹ ≤ (Real.pi * a) ^ 2 := by
        rw [← hw_sq, ← inv_pow w 2]
        exact pow_le_pow_left₀ (inv_nonneg.mpr hw.le) hwi 2
      calc
        _ ≤ (Real.pi * a) ^ 2 := hbi
        _ ≤ 16 * a ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right
            (by nlinarith [Real.pi_lt_four, Real.pi_pos] : Real.pi ^ 2 ≤ 16) (sq_nonneg a)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    · exact (inv_le_one_of_one_le₀ (le_of_not_ge hβ1)).trans (by
        linarith [le_max_left (1 : ℝ) (a ^ 2)])

private theorem saddleMass_pos {β : ℝ} (hβ : 0 < β) : 0 < saddleMass β := by
  let f (θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hp (θ : ℝ) : 0 < f θ := by dsimp [f, radius]; positivity
  have hf : Continuous f := by
    apply Continuous.inv₀ (by dsimp [radius]; fun_prop)
    intro θ h
    exact (hp θ).ne' (by simp [f, h])
  unfold saddleMass spectralAverage
  exact div_pos (intervalIntegral.integral_pos Real.pi_pos hf.continuousOn
    (fun θ _ => (hp θ).le) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hp 0⟩) Real.pi_pos

private theorem saddleMass_strictAnti : StrictAntiOn saddleMass (Ioi 0) := by
  intro b hb c hc hbc
  let f (β θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hp {β : ℝ} (hβ : 0 < β) (θ : ℝ) :
      0 < radius β (2 - 2 * Real.cos θ) := by unfold radius; positivity
  have hf {β : ℝ} (hβ : 0 < β) : Continuous (f β) :=
    (by dsimp [radius]; fun_prop : Continuous fun θ => radius β (2 - 2 * Real.cos θ)).inv₀
      (fun θ => (hp hβ θ).ne')
  have hlt (θ : ℝ) : f c θ < f b θ := by
    apply inv_strictAnti₀ (hp hb θ)
    unfold radius
    exact Real.sqrt_lt_sqrt (by positivity) (add_lt_add_right
      (pow_lt_pow_left₀ hbc (le_of_lt hb) (by decide : 2 ≠ 0)) _)
  unfold saddleMass spectralAverage
  exact div_lt_div_of_pos_right
    (intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      Real.pi_pos (hf hc).continuousOn (hf hb).continuousOn
      (fun θ _ => (hlt θ).le) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hlt 0⟩) Real.pi_pos

private theorem saddleMass_continuousOn {l u : ℝ} (hl : 0 < l) :
    ContinuousOn saddleMass (Icc l u) := by
  let f (β θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hb (β : ℝ) (hβ : β ∈ Icc l u) (θ : ℝ) :
      l ≤ radius β (2 - 2 * Real.cos θ) := by
    unfold radius
    apply (Real.le_sqrt hl.le (by positivity)).2
    nlinarith [pow_le_pow_left₀ hl.le hβ.1 2, sq_nonneg (2 - 2 * Real.cos θ)]
  have hi : ContinuousOn (fun β => ∫ θ in 0..Real.pi, f β θ) (Icc l u) := by
    intro b hbi
    apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => l⁻¹)
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact ((show Continuous (fun θ => radius β (2 - 2 * Real.cos θ)) by
        dsimp [radius]; fun_prop).inv₀ (fun θ => (hl.trans_le (hb β hβ θ)).ne')).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact ae_of_all _ fun θ _ => by
        change |(radius β (2 - 2 * Real.cos θ))⁻¹| ≤ l⁻¹
        rw [abs_of_nonneg (inv_nonneg.mpr (hl.le.trans (hb β hβ θ)))]
        exact inv_anti₀ hl (hb β hβ θ)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun θ _ =>
        (ContinuousOn.inv₀ (by dsimp [radius]; fun_prop)
          (fun β hβ => (hl.trans_le (hb β hβ θ)).ne')) b hbi
  change ContinuousOn (fun β => (∫ θ in 0..Real.pi, f β θ) / Real.pi) (Icc l u)
  exact hi.div_const _

/-- Every positive window parameter has a unique positive saddle radius. -/
theorem existsUnique_saddle_radius {a : ℝ} (ha : 0 < a) :
    ∃! β : ℝ, 0 < β ∧ saddleMass β = a / 2 := by
  let l : ℝ := (32 * (1 + a) ^ 2)⁻¹
  let u : ℝ := max 1 (4 / a)
  have hl : 0 < l := by dsimp [l]; positivity
  have hpow : 1 ≤ (1 + a) ^ 2 := by
    nlinarith [sq_nonneg a]
  have hlu : l ≤ u := by
    exact (inv_le_one_of_one_le₀ (show 1 ≤ 32 * (1 + a) ^ 2 by linarith)).trans (le_max_left _ _)
  have hu : 0 < u := hl.trans_le hlu
  have hlval : a / 2 ≤ saddleMass l := by
    by_contra! h
    have hlmass := saddleMass_pos hl
    have hb := (saddle_radius_bounds hl (show 0 < 2 * saddleMass l by positivity)
      (show saddleMass l = (2 * saddleMass l) / 2 by ring)).2
    have hs : (2 * saddleMass l) ^ 2 ≤ a ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hx : max 1 ((2 * saddleMass l) ^ 2) ≤ (1 + a) ^ 2 :=
      max_le hpow (hs.trans (by linarith))
    have hh := hb.trans (mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ 16 by norm_num))
    change ((32 * (1 + a) ^ 2)⁻¹)⁻¹ ≤ 16 * (1 + a) ^ 2 at hh
    rw [inv_inv] at hh
    linarith
  have huval : saddleMass u ≤ a / 2 := by
    have humass := saddleMass_pos hu
    have hb := (saddle_radius_bounds hu (show 0 < 2 * saddleMass u by positivity)
      (show saddleMass u = (2 * saddleMass u) / 2 by ring)).1
    have hh : 4 / a ≤ 2 / (2 * saddleMass u) := (le_max_right _ _).trans hb
    have he := (div_le_div_iff₀ ha (show 0 < 2 * saddleMass u by positivity)).1 hh
    linarith
  obtain ⟨β, hβ, he⟩ := intermediate_value_Icc' hlu (saddleMass_continuousOn hl) ⟨huval, hlval⟩
  have hp := hl.trans_le hβ.1
  refine ⟨β, ⟨hp, he⟩, ?_⟩
  intro γ hγ
  exact saddleMass_strictAnti.injOn hγ.1 hp (hγ.2.trans he.symm)

/-- The positive solution of the scalar saddle equation for a physical window. -/
def saddleRadius (a : ℝ) : ℝ :=
  if ha : 0 < a then (existsUnique_saddle_radius ha).exists.choose else 0

private theorem saddleRadius_spec {a : ℝ} (ha : 0 < a) :
    0 < saddleRadius a ∧ saddleMass (saddleRadius a) = a / 2 := by
  simpa only [saddleRadius, dite_eq_left ha] using (existsUnique_saddle_radius ha).exists.choose_spec

/-- The continuous zero density, including the number of cells in the
equal-mass condition. This is the nonnegative formula at the saddle. -/
def saddleDensity (n : ℕ) (β t : ℝ) : ℝ :=
  (n : ℝ) * spectralAverage (fun r =>
    (radius β r)⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r ^ 2))) / Real.pi

private theorem saddleDensity_spec (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2) :
    ContinuousOn (saddleDensity n β) (Ici β) ∧
    (∀ t ∈ Ici β, 0 ≤ saddleDensity n β t ∧ saddleDensity n β t ≤ (n : ℝ) * a / (2 * Real.pi)) ∧
    (∀ t > β, 0 < saddleDensity n β t) ∧
    Tendsto (fun u => ∫ t in β..u, saddleDensity n β t) atTop atTop := by
  let r (θ : ℝ) := 2 - 2 * Real.cos θ
  let F (t θ : ℝ) := (radius β (r θ))⁻¹ *
    (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + (r θ) ^ 2))
  let G (θ : ℝ) := (radius β (r θ))⁻¹
  have hgpos (θ : ℝ) : 0 < G θ := by dsimp [G, radius]; positivity
  have hgcap (θ : ℝ) : G θ ≤ β⁻¹ := by
    apply inv_anti₀ hβ
    unfold radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by nlinarith [sq_nonneg (r θ)])
  have hgcont : Continuous G := by
    apply Continuous.inv₀ (by dsimp [radius, r]; fun_prop)
    intro x
    exact fun h => (hgpos x).ne' (by simp [G, h])
  have hnum (t : ℝ) (ht : β ≤ t) : Real.sqrt (t ^ 2 - β ^ 2) ≤ t :=
    (Real.sqrt_le_iff.mpr ⟨hβ.le.trans ht, by linarith [sq_nonneg β]⟩)
  have hpoint (t : ℝ) (ht : β ≤ t) (θ : ℝ) : 0 ≤ F t θ ∧ F t θ ≤ G θ := by
    have ht0 := hβ.trans_le ht
    have hr : t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r θ ^ 2) ≤ 1 :=
      (div_le_iff₀ (by positivity)).2
        (by nlinarith [mul_le_mul_of_nonneg_left (hnum t ht) ht0.le, sq_nonneg (r θ)])
    exact ⟨mul_nonneg (hgpos θ).le (div_nonneg (mul_nonneg ht0.le (Real.sqrt_nonneg _))
      (by positivity)), mul_le_of_le_one_right (hgpos θ).le hr⟩
  have hFcont (t : ℝ) (ht : β ≤ t) : Continuous (F t) := by
    apply hgcont.mul
    apply continuous_const.div (by dsimp [r]; fun_prop)
    intro x
    have ht0 := hβ.trans_le ht
    positivity
  have hFpar (θ : ℝ) : ContinuousOn (fun t => F t θ) (Ici β) := by
    apply continuousOn_const.mul
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have ht0 := hβ.trans_le ht
    positivity
  have hc : ContinuousOn (saddleDensity n β) (Ici β) := by
    have hloc : ContinuousOn (fun t => ∫ θ in 0..Real.pi, F t θ) (Ici β) := by
      intro x hx
      apply intervalIntegral.continuousWithinAt_of_dominated_interval
        (bound := fun _ => β⁻¹)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hFcont t ht).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact ae_of_all _ fun θ _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hpoint t ht θ).1]
          exact (hpoint t ht θ).2.trans (hgcap θ)
      · exact intervalIntegrable_const
      · exact ae_of_all _ fun θ _ => hFpar θ x hx
    change ContinuousOn (fun t => (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi) (Ici β)
    exact ((hloc.div_const _).const_mul _).div_const _
  have hG : (∫ θ in 0..Real.pi, G θ) / Real.pi = a / 2 := hs
  have hπ : 0 < Real.pi := Real.pi_pos
  have hbounds (t : ℝ) (ht : t ∈ Ici β) :
      0 ≤ saddleDensity n β t ∧ saddleDensity n β t ≤ (n : ℝ) * a / (2 * Real.pi) := by
    have huv := intervalIntegral.integral_mono_on (μ := volume) hπ.le
      ((hFcont t ht).intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)
      (fun θ _ => (hpoint t ht θ).2)
    have hnonneg := intervalIntegral.integral_nonneg (μ := volume) hπ.le (fun θ _ => (hpoint t ht θ).1)
    change 0 ≤ (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi ∧ _
    constructor
    · positivity
    · change (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi ≤ _
      calc
        _ ≤ (n : ℝ) * ((∫ θ in 0..Real.pi, G θ) / Real.pi) / Real.pi := by gcongr
        _ = _ := by rw [hG]; ring
  have hpos (t : ℝ) (ht : β < t) : 0 < saddleDensity n β t := by
    have ht0 := hβ.trans ht
    have hdiff : 0 < t ^ 2 - β ^ 2 := by nlinarith [mul_pos (sub_pos.mpr ht) (add_pos ht0 hβ)]
    have hfpos (θ : ℝ) : 0 < F t θ := by
      exact mul_pos (hgpos θ) (div_pos (mul_pos ht0 (Real.sqrt_pos.2 hdiff)) (by positivity))
    have hp := intervalIntegral.integral_pos hπ (hFcont t ht.le).continuousOn
      (fun θ _ => (hfpos θ).le) ⟨0, ⟨le_rfl, hπ.le⟩, hfpos 0⟩
    change 0 < (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi
    exact div_pos (mul_pos hn (div_pos hp hπ)) hπ
  refine ⟨hc, hbounds, hpos, ?_⟩
  let K := max (2 * β) 4
  have hβK : β ≤ K := by dsimp [K]; linarith [le_max_left (2 * β) (4 : ℝ)]
  let m := (n : ℝ) * a / (8 * Real.pi)
  have hm : 0 < m := by dsimp [m]; positivity
  have hflo (t : ℝ) (ht : K ≤ t) : m ≤ saddleDensity n β t := by
    have htβ : 2 * β ≤ t := (le_max_left _ _).trans ht
    have ht4 : 4 ≤ t := (le_max_right _ _).trans ht
    have ht0 : 0 < t := by positivity [hβ.trans_le (hβK.trans ht)]
    have hlo : t / 2 ≤ Real.sqrt (t ^ 2 - β ^ 2) := by
      apply (Real.le_sqrt (by positivity) (by nlinarith)).2
      nlinarith [pow_le_pow_left₀ (show 0 ≤ 2 * β by positivity) htβ 2]
    have hKern (θ : ℝ) : G θ / 4 ≤ F t θ := by
      have hr0 : 0 ≤ r θ := by dsimp [r]; linarith [Real.cos_le_one θ]
      have hr4 : r θ ≤ 4 := by dsimp [r]; linarith [Real.neg_one_le_cos θ]
      have hs := pow_le_pow_left₀ hr0 (hr4.trans ht4) 2
      have h := (le_div_iff₀ (by positivity : 0 < t ^ 2 + r θ ^ 2)).2
        (show 1 / 4 * (t ^ 2 + r θ ^ 2) ≤ t * Real.sqrt (t ^ 2 - β ^ 2) by
          nlinarith [mul_le_mul_of_nonneg_left hlo ht0.le])
      simpa only [div_eq_mul_inv, one_mul, F] using mul_le_mul_of_nonneg_left h (hgpos θ).le
    have hI := intervalIntegral.integral_mono_on (μ := volume) hπ.le ((hgcont.div_const _).intervalIntegrable _ _)
      ((hFcont t (hβK.trans ht)).intervalIntegrable _ _) (fun θ _ => hKern θ)
    have hloI : (∫ θ in 0..Real.pi, G θ) / 4 ≤ ∫ θ in 0..Real.pi, F t θ := by
      simpa only [intervalIntegral.integral_div] using hI
    change _ ≤ (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi
    calc
      _ = (n : ℝ) * (((∫ θ in 0..Real.pi, G θ) / 4) / Real.pi) / Real.pi := by
        rw [show ((∫ θ in 0..Real.pi, G θ) / 4) / Real.pi =
          ((∫ θ in 0..Real.pi, G θ) / Real.pi) / 4 by ring, hG]
        dsimp [m]
        ring
      _ ≤ _ := by gcongr
  have hb : 0 ≤ ∫ x in β..K, saddleDensity n β x :=
    intervalIntegral.integral_nonneg hβK (fun x hx => (hbounds x (mem_Ici.mpr hx.1)).1)
  apply tendsto_atTop.2
  intro R
  filter_upwards [eventually_ge_atTop (max K (K + R / m))] with t ht
  have hKt := (le_max_left _ _).trans ht
  have hconst := intervalIntegral.integral_mono_on (μ := volume) hKt
    (intervalIntegrable_const (c := m))
    ((hc.mono (show Icc K t ⊆ Ici β from fun _ hx =>
      mem_Ici.mpr (hβK.trans hx.1))).intervalIntegrable_of_Icc hKt)
    (fun x hx => hflo x hx.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hconst
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hc.mono (show Icc β K ⊆ Ici β from fun _ hx =>
      mem_Ici.mpr hx.1)).intervalIntegrable_of_Icc hβK)
    ((hc.mono (show Icc K t ⊆ Ici β from fun _ hx =>
      mem_Ici.mpr (hβK.trans hx.1))).intervalIntegrable_of_Icc hKt)
  have hR := (div_le_iff₀ hm).1 (show R / m ≤ t - K by
    linarith [(le_max_right K (K + R / m)).trans ht])
  linarith

/-- The logarithmic sum entering the real and imaginary saddle identities. -/
def saddleLogAverage (β q : ℝ) : ℝ :=
  spectralAverage (fun r => Real.log (radius β q + radius β r))

private theorem saddleLogAverage_mono {β : ℝ} (hβ : 0 < β) {u v : ℝ}
    (hu : 0 ≤ u) (h : u ≤ v) : saddleLogAverage β u ≤ saddleLogAverage β v := by
  let g (q θ : ℝ) := Real.log (radius β q + radius β (2 - 2 * Real.cos θ))
  have hp (q θ : ℝ) : 0 < radius β q + radius β (2 - 2 * Real.cos θ) := by
    unfold radius
    positivity
  have hg (q : ℝ) : Continuous (g q) := by
    apply Continuous.log (by dsimp [radius]; fun_prop)
    exact fun θ => (hp q θ).ne'
  have hR : radius β u ≤ radius β v := by
    unfold radius
    exact Real.sqrt_le_sqrt (add_le_add_left (pow_le_pow_left₀ hu h 2) _)
  unfold saddleLogAverage spectralAverage
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  exact intervalIntegral.integral_mono_on Real.pi_pos.le
    ((hg u).intervalIntegrable _ _) ((hg v).intervalIntegrable _ _)
    (fun θ _ => Real.log_le_log (hp u θ) (add_le_add_left hR _))

private theorem hasDerivAt_saddleRadiusFunction {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    HasDerivAt (radius β) (y / radius β y) y := by
  have h := ((hasDerivAt_pow 2 y).add_const (β ^ 2)).sqrt
    (show y ^ 2 + β ^ 2 ≠ 0 by positivity)
  unfold radius
  convert h using 1
  norm_num
  ring

private theorem hasDerivAt_saddleLogAverage {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    HasDerivAt (saddleLogAverage β)
      (y / radius β y * spectralAverage (fun r => (radius β y + radius β r)⁻¹)) y := by
  let r (θ : ℝ) := 2 - 2 * Real.cos θ
  let F (v θ : ℝ) := Real.log (radius β v + radius β (r θ))
  let G (v θ : ℝ) := (radius β v + radius β (r θ))⁻¹
  let F' (v θ : ℝ) := (v / radius β v) * G v θ
  let μ := volume.restrict (Ioc (0 : ℝ) Real.pi)
  have hb (v : ℝ) : β ≤ radius β v := by
    unfold radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by linarith [sq_nonneg v])
  have hp (v θ : ℝ) : 0 < radius β v + radius β (r θ) := by
    exact add_pos_of_pos_of_nonneg (hβ.trans_le (hb v)) (Real.sqrt_nonneg _)
  have hc (v : ℝ) : Continuous (F v) := by
    apply Continuous.log (by dsimp [r, radius]; fun_prop)
    exact fun θ => (hp v θ).ne'
  have hcG (v : ℝ) : Continuous (G v) := by
    apply Continuous.inv₀ (by dsimp [r, radius]; fun_prop)
    exact fun θ => (hp v θ).ne'
  have hf' (v θ : ℝ) : HasDerivAt (fun u => F u θ) (F' v θ) v := by
    simpa only [F, F', G, div_eq_mul_inv] using
      ((hasDerivAt_saddleRadiusFunction hβ v).add_const (radius β (r θ))).log (hp v θ).ne'
  have hbound (v θ : ℝ) : ‖F' v θ‖ ≤ β⁻¹ := by
    have hv : |v| ≤ radius β v := by
      unfold radius
      exact (Real.le_sqrt (abs_nonneg v) (by positivity)).2 (by nlinarith [sq_abs v])
    have hg : G v θ ≤ β⁻¹ :=
      inv_anti₀ hβ ((hb v).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    rw [Real.norm_eq_abs, show F' v θ = (v / radius β v) * G v θ from rfl,
      abs_mul, abs_div, abs_of_pos (hβ.trans_le (hb v)),
      abs_of_nonneg (inv_nonneg.mpr (hp v θ).le)]
    exact (mul_le_of_le_one_left (inv_nonneg.mpr (hp v θ).le)
      ((div_le_one (hβ.trans_le (hb v))).2 hv)).trans hg
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := univ) univ_mem
    (.of_forall fun v => (hc v).aestronglyMeasurable)
    ((hc y).intervalIntegrable (μ := volume) 0 Real.pi).1
    ((hcG y).const_mul (y / radius β y)).aestronglyMeasurable
    (ae_of_all μ fun θ v _ => hbound v θ)
    (integrable_const β⁻¹)
    (ae_of_all μ fun θ v _ => hf' v θ)).2
  have h := hd.div_const Real.pi
  change HasDerivAt (fun v => (∫ θ in 0..Real.pi, F v θ) / Real.pi) _ y
  rw [show (fun v => (∫ θ in 0..Real.pi, F v θ) / Real.pi) =
    (fun v => (∫ θ, F v θ ∂μ) / Real.pi) by
      funext v
      rw [intervalIntegral.integral_of_le Real.pi_pos.le]]
  simpa only [spectralAverage, F', G, μ, r, intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_const_mul, mul_div_assoc] using h

private theorem cauchy_half {A : ℝ} (hA : 0 < A) :
    Integrable (fun s : ℝ => (s ^ 2 + A ^ 2)⁻¹) ∧
      (∫ s in Ioi (0 : ℝ), (s ^ 2 + A ^ 2)⁻¹) = Real.pi / (2 * A) := by
  let f (s : ℝ) := (1 + s ^ 2)⁻¹
  have hA' : 0 < A⁻¹ := inv_pos.mpr hA
  have he (s : ℝ) : (s ^ 2 + A ^ 2)⁻¹ = (A ^ 2)⁻¹ * f (A⁻¹ * s) := by
    have hs : 0 < s ^ 2 + A ^ 2 := by positivity
    have hf : 0 < 1 + (A⁻¹ * s) ^ 2 := by positivity
    dsimp [f]
    field_simp [hA.ne', hs.ne', hf.ne']
    <;> ring
  simp_rw [he]
  have hi := (integrable_inv_one_add_mul_sq hA'.ne').const_mul (A ^ 2)⁻¹
  refine ⟨hi, ?_⟩
  rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 hA', mul_zero, inv_inv, smul_eq_mul]
  have h := integral_Ioi_inv_one_add_sq (i := 0)
  rw [Real.arctan_zero, sub_zero] at h
  change (A ^ 2)⁻¹ * (A * ∫ s in Ioi (0 : ℝ), f s) = _
  rw [show (∫ s in Ioi (0 : ℝ), f s) = Real.pi / 2 from h]
  field_simp

private theorem cauchy_pair_half {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    (∫ s in Ioi (0 : ℝ), s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))) =
      Real.pi / (2 * (A + R)) := by
  let C := A * R
  let g (s : ℝ) := s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))
  let h (s : ℝ) := C / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))
  have hC : 0 < C := mul_pos hA hR
  have hg (s : ℝ) : 0 ≤ g s := by dsimp [g]; positivity
  have hh (s : ℝ) : 0 ≤ h s := by dsimp [h, C]; positivity
  have hplus (s : ℝ) :
      g s + h s = (A * (s ^ 2 + A ^ 2)⁻¹ + R * (s ^ 2 + R ^ 2)⁻¹) / (A + R) := by
    dsimp [g, h, C]
    field_simp [show 0 < s ^ 2 + A ^ 2 by positivity, show 0 < s ^ 2 + R ^ 2 by positivity,
      (add_pos hA hR).ne']
    ring
  have hi : Integrable (fun s => g s + h s) := by
    simp_rw [hplus, div_eq_mul_inv]
    exact (((cauchy_half hA).1.const_mul A).add ((cauchy_half hR).1.const_mul R)).mul_const _
  have hgc : Continuous g := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro s
    positivity
  have hhc : Continuous h := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro s
    positivity
  have hgi : Integrable g := hi.mono' hgc.aestronglyMeasurable
    (.of_forall fun s => by simpa [Real.norm_eq_abs, abs_of_nonneg (hg s)] using hh s)
  have hhi : Integrable h := hi.mono' hhc.aestronglyMeasurable
    (.of_forall fun s => by simpa [Real.norm_eq_abs, abs_of_nonneg (hh s)] using hg s)
  let f (s : ℝ) := C * s⁻¹
  have hf : Set.InjOn f (Ioi 0) := by
    intro u _ v _ huv
    exact inv_injective (mul_left_cancel₀ hC.ne' huv)
  have himage : f '' Ioi 0 = Ioi 0 := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mul_pos hC (inv_pos.mpr hu)
    · intro hs
      refine ⟨C * s⁻¹, mul_pos hC (inv_pos.mpr hs), ?_⟩
      dsimp [f]
      field_simp [hC.ne', (show 0 < s from hs).ne']
  have hDeriv (s : ℝ) (hs : s ∈ Ioi 0) :
      HasDerivWithinAt f (C * (-(s ^ 2)⁻¹)) (Ioi 0) s :=
    ((hasDerivAt_inv (show 0 < s from hs).ne').const_mul C).hasDerivWithinAt
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hDeriv hf g
  rw [himage] at he
  have hsub : (∫ s in Ioi (0 : ℝ), g s) = ∫ s in Ioi (0 : ℝ), h s := by
    refine he.trans (setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_)
    have hs' : 0 < s := hs
    have hCnonneg : 0 ≤ C * (s ^ 2)⁻¹ := by positivity
    rw [mul_neg, abs_neg, abs_of_nonneg hCnonneg, smul_eq_mul]
    dsimp [f, g, h, C]
    field_simp [hs'.ne', hA.ne', hR.ne',
      show 0 < s ^ 2 + A ^ 2 by positivity, show 0 < s ^ 2 + R ^ 2 by positivity,
      show 0 < (A * R * s⁻¹) ^ 2 + A ^ 2 by positivity,
      show 0 < (A * R * s⁻¹) ^ 2 + R ^ 2 by positivity]
    <;> ring
  have hm : (∫ s in Ioi (0 : ℝ), g s + h s) = Real.pi / (A + R) := by
    simp_rw [hplus, div_eq_mul_inv]
    rw [integral_mul_const, integral_add ((cauchy_half hA).1.const_mul A).integrableOn
      ((cauchy_half hR).1.const_mul R).integrableOn,
      integral_const_mul, integral_const_mul, (cauchy_half hA).2, (cauchy_half hR).2]
    field_simp [hA.ne', hR.ne', (add_pos hA hR).ne']
    <;> ring
  rw [integral_add hgi.integrableOn hhi.integrableOn, ← hsub] at hm
  change (∫ s in Ioi (0 : ℝ), g s) = _
  apply (eq_div_iff (by positivity : 2 * (A + R) ≠ 0)).2
  apply (eq_div_iff (add_pos hA hR).ne').1 at hm
  linarith

private theorem saddle_radial_resolvent {β : ℝ} (hβ : 0 < β) (y r : ℝ) :
    (∫ t in Ioi β,
      (2 * y / (t ^ 2 + y ^ 2)) *
        ((radius β r)⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r ^ 2)))) =
      Real.pi * y / (radius β r * (radius β y + radius β r)) := by
  let A := radius β y
  let R := radius β r
  let f := radius β
  have hA : 0 < A := by dsimp [A, radius]; positivity
  have hR : 0 < R := by dsimp [R, radius]; positivity
  have hp (s : ℝ) : 0 < f s := by dsimp [f, radius]; positivity
  have hsq (s : ℝ) : f s ^ 2 = s ^ 2 + β ^ 2 :=
    Real.sq_sqrt (by positivity)
  have ha' : A ^ 2 = y ^ 2 + β ^ 2 := hsq y
  have hr' : R ^ 2 = r ^ 2 + β ^ 2 := hsq r
  have hf : Set.InjOn f (Ioi 0) := by
    intro u hu v hv h
    exact (sq_eq_sq₀ (le_of_lt hu) (le_of_lt hv)).1 (by
      linarith [hsq u, hsq v, congrArg (fun z : ℝ => z ^ 2) h])
  have himage : f '' Ioi 0 = Ioi β := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (sq_lt_sq₀ hβ.le (hp s).le).1 (by
        rw [hsq]
        linarith [sq_pos_of_pos (show 0 < s from hs)])
    · intro ht
      have ht0 : 0 < t := hβ.trans ht
      have ht2 : β ^ 2 < t ^ 2 := (sq_lt_sq₀ hβ.le ht0.le).2 ht
      refine ⟨Real.sqrt (t ^ 2 - β ^ 2), Real.sqrt_pos.mpr (sub_pos.mpr ht2), ?_⟩
      dsimp [f, radius]
      rw [Real.sq_sqrt (by linarith), sub_add_cancel, Real.sqrt_sq ht0.le]
  have hDeriv (s : ℝ) (_ : s ∈ Ioi 0) : HasDerivWithinAt f (s / f s) (Ioi 0) s :=
    (hasDerivAt_saddleRadiusFunction hβ s).hasDerivWithinAt
  let Q (t : ℝ) := (2 * y / (t ^ 2 + y ^ 2)) *
    (R⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r ^ 2)))
  have hc := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hDeriv hf Q
  rw [himage] at hc
  calc
    _ = ∫ s in Ioi (0 : ℝ), |s / f s| • Q (f s) := hc
    _ = ∫ s in Ioi (0 : ℝ), (2 * y / R) *
        (s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs' : 0 < s := hs
      change |s / f s| • Q (f s) = (2 * y / R) *
        (s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2)))
      rw [abs_of_nonneg (div_nonneg hs'.le (hp s).le), smul_eq_mul]
      have hsqrt : Real.sqrt (f s ^ 2 - β ^ 2) = s := by
        rw [hsq, add_sub_cancel_right, Real.sqrt_sq hs'.le]
      dsimp only [Q]
      rw [hsqrt, hsq, ha', hr']
      have hz : 0 < s ^ 2 + β ^ 2 + y ^ 2 := by positivity
      have hz' : 0 < s ^ 2 + β ^ 2 + r ^ 2 := by positivity
      have h₁ : s ^ 2 + (y ^ 2 + β ^ 2) = s ^ 2 + β ^ 2 + y ^ 2 := by ring
      have h₂ : s ^ 2 + (r ^ 2 + β ^ 2) = s ^ 2 + β ^ 2 + r ^ 2 := by ring
      rw [h₁, h₂]
      field_simp [(hp s).ne', hR.ne', hz.ne', hz'.ne']
    _ = _ := by
      rw [integral_const_mul, cauchy_pair_half hA hR]
      change (2 * y / R) * (Real.pi / (2 * (A + R))) = Real.pi * y / (R * (A + R))
      field_simp [hR.ne', (add_pos hA hR).ne']

private theorem saddleDensity_resolvent (n : ℕ) {a β : ℝ} (hβ : 0 < β)
    (hs : saddleMass β = a / 2) (y : ℝ) :
    (∫ t in Ioi β, (2 * y / (t ^ 2 + y ^ 2)) * saddleDensity n β t) =
      (n : ℝ) * (y / radius β y) *
        (a / 2 - spectralAverage (fun r => (radius β y + radius β r)⁻¹)) := by
  let r (θ : ℝ) := 2 - 2 * Real.cos θ
  let A := radius β y
  let R (θ : ℝ) := radius β (r θ)
  let H (t θ : ℝ) := (R θ)⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r θ ^ 2))
  let Q (t θ : ℝ) := (2 * y / (t ^ 2 + y ^ 2)) * H t θ
  let μ := volume.restrict (Ioi β)
  let ν := volume.restrict (Ioc (0 : ℝ) Real.pi)
  let N : ℝ := n
  have hA : 0 < A := by dsimp [A, radius]; positivity
  have hR (θ : ℝ) : β ≤ R θ := by
    unfold R radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by linarith [sq_nonneg (r θ)])
  have hRp (θ : ℝ) : 0 < R θ := hβ.trans_le (hR θ)
  have hcap (t θ : ℝ) (ht : β < t) : 0 ≤ H t θ ∧ H t θ ≤ β⁻¹ := by
    have ht0 := hβ.trans ht
    have hS : Real.sqrt (t ^ 2 - β ^ 2) ≤ t :=
      Real.sqrt_le_iff.mpr ⟨ht0.le, by linarith [sq_nonneg β]⟩
    have hfactor : t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r θ ^ 2) ≤ 1 := by
      exact (div_le_iff₀ (by positivity)).2
        (by nlinarith [mul_le_mul_of_nonneg_left hS ht0.le, sq_nonneg (r θ)])
    exact ⟨mul_nonneg (inv_nonneg.mpr (hRp θ).le) (by positivity),
      (mul_le_of_le_one_right (inv_nonneg.mpr (hRp θ).le) hfactor).trans (inv_anti₀ hβ (hR θ))⟩
  have hmeas : AEStronglyMeasurable (Function.uncurry Q) (μ.prod ν) := by
    apply Measurable.aestronglyMeasurable
    dsimp [Function.uncurry, Q, H, R, r, radius]
    fun_prop
  have hinv : Integrable (fun t : ℝ => 2 * |y| * β⁻¹ * (t ^ 2)⁻¹) μ := by
    exact (integrableOn_inv_sq hβ).const_mul _
  have hmajor : Integrable (fun x : ℝ × ℝ => 2 * |y| * β⁻¹ * (x.1 ^ 2)⁻¹) (μ.prod ν) := by
    exact hinv.comp_fst ν
  have hi : Integrable (Function.uncurry Q) (μ.prod ν) := by
    apply hmajor.mono' hmeas
    have ht : ∀ᵐ x : ℝ × ℝ ∂μ.prod ν, β < x.1 := by
      apply (Measure.ae_prod_iff_ae_ae (p := fun x : ℝ × ℝ => β < x.1)
        (measurable_fst measurableSet_Ioi)).2
      exact (ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β))).mono
        (fun t ht => ae_of_all ν fun _ => ht)
    filter_upwards [ht] with x hx
    have ht0 := hβ.trans hx
    have hcc := hcap x.1 x.2 hx
    change |(2 * y / (x.1 ^ 2 + y ^ 2)) * H x.1 x.2| ≤ _
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ x.1 ^ 2 + y ^ 2), abs_of_nonneg hcc.1]
    calc
      _ ≤ (2 * |y| / x.1 ^ 2) * β⁻¹ :=
        mul_le_mul (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by linarith [sq_nonneg y])) hcc.2 hcc.1 (by positivity)
      _ = _ := by ring
  have hfub := integral_integral_swap hi
  have houter :
      (∫ t, (2 * y / (t ^ 2 + y ^ 2)) * saddleDensity n β t ∂μ) =
        N / Real.pi ^ 2 * ∫ θ, (∫ t, Q t θ ∂μ) ∂ν := by
    rw [← hfub, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [saddleDensity, spectralAverage, Q, H, ν, r, R, N]
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_const_mul]
    ring
  have hintegral : (∫ θ, (∫ t, Q t θ ∂μ) ∂ν) =
      ∫ θ, Real.pi * y / (R θ * (A + R θ)) ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ fun θ => saddle_radial_resolvent hβ y (r θ)
  have hsplit (θ : ℝ) : Real.pi * y / (R θ * (A + R θ)) =
      Real.pi * (y / A) * ((R θ)⁻¹ - (A + R θ)⁻¹) := by
    field_simp [hA.ne', (hRp θ).ne', (add_pos hA (hRp θ)).ne']
    ring
  have hRc : Continuous R := by dsimp [R, r, radius]; fun_prop
  have hiR : Integrable (fun θ => (R θ)⁻¹) ν :=
    (hRc.inv₀ fun θ => (hRp θ).ne').intervalIntegrable (μ := volume) 0 Real.pi |>.1
  have hiA : Integrable (fun θ => (A + R θ)⁻¹) ν :=
    ((continuous_const.add hRc).inv₀ fun θ => (add_pos hA (hRp θ)).ne').intervalIntegrable
      (μ := volume) 0 Real.pi |>.1
  have hs' : (∫ θ, (R θ)⁻¹ ∂ν) / Real.pi = a / 2 := by
    simpa only [saddleMass, spectralAverage, intervalIntegral.integral_of_le Real.pi_pos.le, ν, R, r]
      using hs
  change (∫ t, _ ∂μ) = _
  rw [houter, hintegral]
  simp_rw [hsplit]
  rw [integral_const_mul, integral_sub hiR hiA, ← hs']
  unfold spectralAverage
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  let U := ∫ θ, (R θ)⁻¹ ∂ν
  let V := ∫ θ, (A + R θ)⁻¹ ∂ν
  change N / Real.pi ^ 2 * (Real.pi * (y / A) * (U - V)) =
    N * (y / A) * (U / Real.pi - V / Real.pi)
  field_simp [Real.pi_ne_zero, hA.ne']

private theorem imaginaryPotential_eval_of_resolvent (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2)
    (hresolvent : ∀ y ≥ 0,
      (∫ t in Ioi β, (2 * y / (t ^ 2 + y ^ 2)) * saddleDensity n β t) =
        (n : ℝ) * (y / radius β y) *
          (a / 2 - spectralAverage (fun r => (radius β y + radius β r)⁻¹))) :
    ∀ y ≥ 0, imaginaryPotential β (saddleDensity n β) y =
      (n : ℝ) * (a / 2 * (radius β y - β) -
        (saddleLogAverage β y - saddleLogAverage β 0)) := by
  obtain ⟨hc, hcap, _, _⟩ := saddleDensity_spec n hn ha hβ hs
  let F := imaginaryPotential β (saddleDensity n β)
  let G (v : ℝ) := (n : ℝ) * (a / 2 * (radius β v - β) -
        (saddleLogAverage β v - saddleLogAverage β 0))
  let D (v : ℝ) := (n : ℝ) * (v / radius β v) *
    (a / 2 - spectralAverage (fun r => (radius β v + radius β r)⁻¹))
  have hf (v : ℝ) (hv : 0 ≤ v) : HasDerivAt F (D v) v := by
    dsimp only [D, F]
    rw [← hresolvent v hv]
    exact hasDerivAt_imaginaryPotential hβ hc hcap v
  have hg (v : ℝ) : HasDerivAt G (D v) v := by
    have hR := (hasDerivAt_saddleRadiusFunction hβ v).sub_const β
    have hJ := (hasDerivAt_saddleLogAverage hβ v).sub_const (saddleLogAverage β 0)
    convert ((hR.const_mul (a / 2)).sub hJ).const_mul (n : ℝ) using 1
    dsimp [D]
    ring
  have h0 : F 0 = G 0 := by
    simp [F, G, imaginaryPotential, radius, Real.sqrt_sq hβ.le]
  intro y hy
  exact eq_of_has_deriv_right_eq (fun v hv => (hf v hv.1).hasDerivWithinAt)
    (fun v _ => (hg v).hasDerivWithinAt)
    (fun v hv => (hf v hv.1).continuousAt.continuousWithinAt)
    (fun v _ => (hg v).continuousAt.continuousWithinAt) h0 y ⟨hy, le_rfl⟩

/-- The physical-time estimate for the actual saddle density. Its remaining
analytic inputs are the imaginary-axis evaluation and real-axis cancellation
identities for that density. -/
private theorem log_inverse_diagonal_error_at_saddle_radius (n : ℕ) (j : Mode n) {T β : ℝ}
    (hT : 0 < T) (hβ : 0 < β)
    (hs : saddleMass β = ((n : ℝ) * T) / 2)
    (hImag : ∀ y ≥ 0, imaginaryPotential β (saddleDensity n β) y =
      (n : ℝ) * (((n : ℝ) * T) / 2 * (radius β y - β) -
        (saddleLogAverage β y - saddleLogAverage β 0)))
    (hReal : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      realPotential β (saddleDensity n β) |ω| + (n : ℝ) * Real.log ‖ζ‖ ≤
        (n : ℝ) * saddleRate ((n : ℝ) * T) β 0) :
    |Real.log (Real.sqrt ((physicalGramian n T)⁻¹ j j)) -
      (n : ℝ) * saddleRate ((n : ℝ) * T) β (rate n j)| ≤
        20 * (1 + Real.log (n : ℝ) + |Real.log ((n : ℝ) * T)|) := by
  let N : ℝ := n
  let a := N * T
  have hN : 0 < N := by
    have := j.isLt
    change 0 < (n : ℝ)
    exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := mul_pos hN hT
  obtain ⟨hc, hcap, hp, hu⟩ := saddleDensity_spec n hN ha hβ hs
  let bins := EqualMassBins.ofDensity hc (fun t ht => (hcap t ht).1) hp hu
  obtain ⟨hβupper, hβinv⟩ := saddle_radius_bounds hβ ha hs
  have hr : radius β 0 = β := by simp [radius, Real.sqrt_sq, hβ.le]
  have hwidth (y : ℝ) (hy : 0 ≤ y) :
      imaginaryPotential β (saddleDensity n β) y ≤ N * a / 2 * y := by
    rw [hImag y hy]
    have hlog := saddleLogAverage_mono hβ (le_refl 0) hy
    have hRy : radius β y ≤ y + β := by
      unfold radius
      exact (Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_nonneg hy hβ.le]⟩)
    have he : a / 2 * (radius β y - β) -
        (saddleLogAverage β y - saddleLogAverage β 0) ≤ a / 2 * y := by
      have hs' := mul_le_mul_of_nonneg_left (show radius β y - β ≤ y by linarith)
        (by positivity : 0 ≤ a / 2)
      linarith
    calc
      _ ≤ N * (a / 2 * y) := mul_le_mul_of_nonneg_left he hN.le
      _ = _ := by ring
  have hvalue : imaginaryPotential β (saddleDensity n β) (rate n j) =
      N * (saddleRate a β 0 + a * rate n j / 2 - saddleRate a β (rate n j)) := by
    rw [hImag _ (rate_pos n j).le]
    simp only [saddleRate, saddleLogAverage, hr, sub_zero]
    change N * (a / 2 * (radius β (rate n j) - β) - _) = _
    ring
  have H := log_inverse_diagonal_error_of_quantiles n j ha hβ hβupper hβinv bins
    (fun t ht => (hcap t ht).2) hwidth hReal hvalue
  have he : a / N = T := by dsimp [a]; field_simp
  change |Real.log (Real.sqrt ((physicalGramian n (a / N))⁻¹ j j)) -
      N * saddleRate a β (rate n j)| ≤ 20 * (1 + Real.log N + |Real.log a|) at H
  rwa [he] at H

private theorem exists_outer_root (c : ℂ) : ∃ z : ℂ, z ≠ 0 ∧ z + z⁻¹ = c ∧ 1 ≤ ‖z‖ := by
  obtain ⟨w, hw⟩ := Complex.cos_surjective (c / 2)
  let z := Complex.exp (w * Complex.I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have he : z + z⁻¹ = c := by
    simp only [Complex.cos, neg_mul, Complex.exp_neg] at hw
    have h := congrArg (fun x : ℂ => x * 2) hw
    simpa only [z, div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using h
  by_cases hn : 1 ≤ ‖z‖
  · exact ⟨z, hz, he, hn⟩
  · exact ⟨z⁻¹, inv_ne_zero hz, by simpa only [inv_inv, add_comm] using he, by
      rw [norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.2 hz)).2 (le_of_not_ge hn)⟩

open Polynomial in
private theorem angularGreen_eq_log_outer_radius (ω : ℝ) {z : ℂ} (hz : z ≠ 0)
    (hroot : z + z⁻¹ = (ω : ℂ) * Complex.I - 2) (hz₁ : 1 ≤ ‖z‖) :
    spectralAverage (fun r => Real.log ‖(r : ℂ) - (ω : ℂ) * Complex.I‖) = Real.log ‖z‖ ∧
      IntervalIntegrable (fun θ => Real.log ‖Complex.ofReal (2 - 2 * Real.cos θ) -
        (ω : ℂ) * Complex.I‖) volume 0 Real.pi := by
  let p : ℂ[X] := (X - C z) * (X - C z⁻¹)
  let f (θ : ℝ) := Real.log ‖(Complex.ofReal (2 - 2 * Real.cos θ)) - (ω : ℂ) * Complex.I‖
  have hp : p ≠ 0 := by
    apply mul_ne_zero <;> exact X_sub_C_ne_zero _
  have hn : Real.posLog ‖z⁻¹‖ = 0 := by
    apply (Real.posLog_eq_zero_iff _).2
    rw [abs_of_nonneg (norm_nonneg _), norm_inv]
    exact inv_le_one_of_one_le₀ hz₁
  have hmah : p.logMahlerMeasure = Real.log ‖z‖ := by
    rw [show p = (X - C z) * (X - C z⁻¹) from rfl,
      logMahlerMeasure_mul_eq_add_logMahlerMeasure hp, logMahlerMeasure_X_sub_C,
      logMahlerMeasure_X_sub_C, hn, add_zero, Real.posLog_eq_log]
    rwa [abs_of_nonneg (norm_nonneg _)]
  have hval (θ : ℝ) : Real.log ‖p.eval (circleMap 0 (-1) θ)‖ = f θ := by
    let w := circleMap 0 (-1) θ
    have hw : ‖w‖ = 1 := by simp [w]
    have hwn : w ≠ 0 := by
      apply norm_ne_zero_iff.mp
      simp [hw]
    have hsum : w + w⁻¹ = -2 * (Real.cos θ : ℂ) := by
      simp only [w, circleMap_zero, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
        inv_neg, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
      ring
    have he : p.eval w = w * (w + w⁻¹ - ((ω : ℂ) * Complex.I - 2)) := by
      simp only [p, eval_mul, eval_sub, eval_X, eval_C]
      rw [← hroot]
      field_simp [hz, hwn]
      ring
    change Real.log ‖p.eval w‖ = _
    rw [he, norm_mul, hw, one_mul, hsum]
    congr 2
    push_cast
    ring
  have hI : IntervalIntegrable f volume 0 (2 * Real.pi) := by
    have hi := p.intervalIntegrable_mahlerMeasure
    have hneg : IntervalIntegrable (fun θ => Real.log ‖p.eval (circleMap 0 (-1) θ)‖)
        volume 0 (2 * Real.pi) := by
      let g (v : ℂ) := Real.log ‖p.eval v‖
      have hi' : CircleIntegrable g 0 1 := hi
      have hn' : CircleIntegrable g 0 (-1) := by simpa only [circleIntegrable_neg_radius] using hi'
      exact hn'
    simpa only [hval] using hneg
  have hsymm (θ : ℝ) : f (2 * Real.pi - θ) = f θ := by
    dsimp only [f]
    rw [Real.cos_two_pi_sub]
  have hmid : Real.pi ∈ uIcc 0 (2 * Real.pi) := by
    rw [uIcc_of_le (by positivity)]
    constructor <;> linarith [Real.pi_pos]
  have h₁ : IntervalIntegrable f volume 0 Real.pi :=
    hI.mono_set (uIcc_subset_uIcc_left hmid)
  have h₂ : IntervalIntegrable f volume Real.pi (2 * Real.pi) :=
    hI.mono_set (uIcc_subset_uIcc_right hmid)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have hreflect : (∫ θ in Real.pi..2 * Real.pi, f θ) = ∫ θ in 0..Real.pi, f θ := by
    have he := intervalIntegral.integral_comp_sub_left f (a := 0) (b := Real.pi) (2 * Real.pi)
    rw [sub_zero, show 2 * Real.pi - Real.pi = Real.pi by ring] at he
    simp only [hsymm] at he
    exact he.symm
  have havg : p.logMahlerMeasure = (∫ θ in 0..Real.pi, f θ) / Real.pi := by
    rw [logMahlerMeasure_def, ← Real.circleAverage_neg_radius, Real.circleAverage_def]
    simp only [hval, smul_eq_mul]
    rw [← hsplit, hreflect]
    ring
  exact ⟨havg.symm.trans hmah, h₁⟩

/-- The value of the saddle square root on the real boundary. -/
def realSaddleRoot (β x : ℝ) : ℂ :=
  if x ≤ β then Complex.ofReal (Real.sqrt (β ^ 2 - x ^ 2))
  else Complex.ofReal (Real.sqrt (x ^ 2 - β ^ 2)) * Complex.I

private theorem norm_axis_difference_sq (r x : ℝ) :
    ‖(r : ℂ) - (x : ℂ) * Complex.I‖ ^ 2 = r ^ 2 + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, ← sq]

private theorem log_axis_comparison {R s r x : ℝ} (hR : 0 < R) (hs : 0 ≤ s)
    (hRs : s < R) (hsq : R ^ 2 - s ^ 2 = r ^ 2 + x ^ 2) :
    Real.log ‖(r : ℂ) - (x : ℂ) * Complex.I‖ + s / R ≤ Real.log (R + s) := by
  let d := ‖(r : ℂ) - (x : ℂ) * Complex.I‖
  have hd2 : d ^ 2 = (R + s) * (R - s) := by
    rw [show d ^ 2 = r ^ 2 + x ^ 2 from norm_axis_difference_sq r x, ← hsq]
    ring
  have hd : 0 < d := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro h
    change 0 = d at h
    rw [← h, zero_pow (by decide : 2 ≠ 0)] at hd2
    exact (mul_pos (add_pos_of_pos_of_nonneg hR hs) (sub_pos.mpr hRs)).ne' hd2.symm
  have hp : 0 < R + s := add_pos_of_pos_of_nonneg hR hs
  have hm : 0 < R - s := sub_pos.mpr hRs
  have hl := congrArg Real.log hd2
  rw [Real.log_pow, Real.log_mul hp.ne' hm.ne'] at hl
  norm_num at hl
  have hv : 0 ≤ 2 * s / (R - s) := by positivity
  have hb := Real.le_log_one_add_of_nonneg hv
  have he : 1 + 2 * s / (R - s) = (R + s) / (R - s) := by
    field_simp [hm.ne']
    ring
  have he' : 2 * (2 * s / (R - s)) / (2 * s / (R - s) + 2) = 2 * (s / R) := by
    field_simp [hm.ne', hR.ne', show 0 < 2 * s / (R - s) + 2 by linarith]
    <;> ring
  rw [he, he', Real.log_div hp.ne' hm.ne'] at hb
  change Real.log d + s / R ≤ _
  linarith

private theorem saddle_real_cancellation (n : ℕ) {a β : ℝ} (hβ : 0 < β)
    (hs : saddleMass β = a / 2)
    (hreal : ∀ x ≥ 0, realPotential β (saddleDensity n β) x =
      (n : ℝ) * (a / 2 * ((realSaddleRoot β x).re - β) -
        spectralAverage (fun r => Real.log ‖realSaddleRoot β x + (radius β r : ℂ)‖) +
        saddleLogAverage β 0)) (ω : ℝ) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧ ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      realPotential β (saddleDensity n β) |ω| + (n : ℝ) * Real.log ‖ζ‖ ≤
        (n : ℝ) * saddleRate a β 0 := by
  obtain ⟨ζ, hz, hroot, hn⟩ := exists_outer_root ((ω : ℂ) * Complex.I - 2)
  obtain ⟨hgreen, hiG⟩ := angularGreen_eq_log_outer_radius ω hz hroot hn
  refine ⟨ζ, hz, hroot, hn, ?_⟩
  let x := |ω|
  let S := realSaddleRoot β x
  let Gamma := spectralAverage (fun r => Real.log ‖(r : ℂ) - (ω : ℂ) * Complex.I‖)
  let J := spectralAverage (fun r => Real.log ‖S + (radius β r : ℂ)‖)
  have hx : 0 ≤ x := abs_nonneg ω
  have hx2 : x ^ 2 = ω ^ 2 := sq_abs ω
  have hβ0 : radius β 0 = β := by simp [radius, Real.sqrt_sq hβ.le]
  suffices hh : a / 2 * S.re + Gamma ≤ J by
    rw [hreal x hx, ← hgreen]
    change (n : ℝ) * (a / 2 * (S.re - β) - J + saddleLogAverage β 0) + (n : ℝ) * Gamma ≤ _
    have he : saddleRate a β 0 = saddleLogAverage β 0 - a / 2 * β := by
      simp [saddleRate, saddleLogAverage, hβ0]
    rw [he]
    have h := mul_le_mul_of_nonneg_left hh (show 0 ≤ (n : ℝ) by positivity)
    linarith
  by_cases hsx : x ≤ β
  · let s := Real.sqrt (β ^ 2 - x ^ 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = β ^ 2 - x ^ 2 := by
      exact Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hx hsx 2))
    have hS : S = (s : ℂ) := by simp [S, s, realSaddleRoot, hsx]
    have hJ : J = spectralAverage (fun r => Real.log (radius β r + s)) := by
      unfold J
      simp_rw [hS, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
      apply congrArg (fun f => spectralAverage f)
      funext r
      rw [abs_of_nonneg (add_nonneg hs0
        (show 0 ≤ radius β r from Real.sqrt_nonneg _)), add_comm]
    rw [hS, Complex.ofReal_re, hJ]
    let p (θ : ℝ) := 2 - 2 * Real.cos θ
    let g (θ : ℝ) := Real.log ‖(p θ : ℂ) - (ω : ℂ) * Complex.I‖
    let G (θ : ℝ) := (radius β (p θ))⁻¹
    let H (θ : ℝ) := Real.log (radius β (p θ) + s)
    have hP (θ : ℝ) : 0 < radius β (p θ) := by unfold radius; positivity
    have hcG : Continuous G := by
      apply Continuous.inv₀ (by dsimp [radius, p]; fun_prop)
      exact fun θ => (hP θ).ne'
    have hcH : Continuous H := by
      apply Continuous.log (by dsimp [radius, p]; fun_prop)
      exact fun θ => (add_pos_of_pos_of_nonneg (hP θ) hs0).ne'
    have hb (θ : ℝ) (ht : θ ∈ Ioo 0 Real.pi) : s * G θ + g θ ≤ H θ := by
      have hcos := Real.strictAntiOn_cos
        (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
        ⟨ht.1.le, ht.2.le⟩ ht.1
      have hp : 0 < p θ := by dsimp [p]; rw [Real.cos_zero] at hcos; linarith
      have hR2 : radius β (p θ) ^ 2 = (p θ) ^ 2 + β ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hRs : s < radius β (p θ) :=
        (sq_lt_sq₀ hs0 (hP θ).le).1 (by rw [hR2, hs2]; nlinarith [sq_pos_of_pos hp])
      have h := log_axis_comparison (hP θ) hs0 hRs (show
        radius β (p θ) ^ 2 - s ^ 2 = (p θ) ^ 2 + ω ^ 2 by rw [hR2, hs2, hx2]; ring)
      simpa only [H, g, G, div_eq_mul_inv, add_comm] using h
    have hiG' : IntervalIntegrable g volume 0 Real.pi := hiG
    have h := intervalIntegral.integral_mono_on_of_le_Ioo Real.pi_pos.le
      (((hcG.intervalIntegrable (μ := volume) 0 Real.pi).const_mul s).add hiG')
      (hcH.intervalIntegrable _ _) hb
    rw [intervalIntegral.integral_add
      ((hcG.intervalIntegrable (μ := volume) 0 Real.pi).const_mul s) hiG',
      intervalIntegral.integral_const_mul] at h
    have hm : (∫ θ in 0..Real.pi, G θ) / Real.pi = a / 2 := hs
    have hmul := div_le_div_of_nonneg_right h Real.pi_pos.le
    rw [add_div, mul_div_assoc, hm, mul_comm s (a / 2)] at hmul
    exact hmul
  · have hxβ : β < x := lt_of_not_ge hsx
    let c := Real.sqrt (x ^ 2 - β ^ 2)
    have hc : c ^ 2 = x ^ 2 - β ^ 2 :=
      Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hβ.le hxβ.le 2))
    have hS : S = (c : ℂ) * Complex.I := by simp [S, c, realSaddleRoot, hsx]
    have hre : S.re = 0 := by rw [hS]; simp [Complex.mul_re]
    have hnrm (r : ℝ) : ‖S + (radius β r : ℂ)‖ = ‖(r : ℂ) - (ω : ℂ) * Complex.I‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
      rw [norm_axis_difference_sq, hS, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        mul_one, add_zero, sub_zero, zero_add, zero_pow (by decide : 2 ≠ 0), ← sq]
      rw [hc, show radius β r ^ 2 = r ^ 2 + β ^ 2 from Real.sq_sqrt (by positivity), hx2]
      ring
    rw [hre, mul_zero, zero_add]
    simp only [J, Gamma, hnrm, le_refl]

/-- The estimate at the unique positive saddle for the physical window.
The imaginary potential is evaluated by the weighted resolvent. The remaining
hypothesis is the real boundary value of the same potential. -/
theorem physical_log_inverse_diagonal_error (n : ℕ) (j : Mode n) {T : ℝ} (hT : 0 < T)
    (hReal : let a := (n : ℝ) * T; let β := saddleRadius a
      ∀ x ≥ 0, realPotential β (saddleDensity n β) x =
        (n : ℝ) * (a / 2 * ((realSaddleRoot β x).re - β) -
          spectralAverage (fun r => Real.log ‖realSaddleRoot β x + (radius β r : ℂ)‖) +
          saddleLogAverage β 0)) :
    let a := (n : ℝ) * T
    |Real.log (Real.sqrt ((physicalGramian n T)⁻¹ j j)) -
      (n : ℝ) * saddleRate a (saddleRadius a) (rate n j)| ≤
        20 * (1 + Real.log (n : ℝ) + |Real.log a|) := by
  have hn : 0 < (n : ℝ) := by
    have := j.isLt
    exact_mod_cast (show 0 < n by omega)
  obtain ⟨hβ, hs⟩ := saddleRadius_spec (mul_pos hn hT)
  have hImag := imaginaryPotential_eval_of_resolvent n hn (mul_pos hn hT) hβ hs
    (fun y _ => saddleDensity_resolvent n hβ hs y)
  exact log_inverse_diagonal_error_at_saddle_radius n j hT hβ hs hImag
    (saddle_real_cancellation n hβ hs hReal)

#print axioms physical_log_inverse_diagonal_error
#print axioms inverse_diagonal_lower_bound_at_saddle
#print axioms inverse_diagonal_upper_bound_of_quantiles

end D5.S3.Observer.Linear.ReflectingHeatInterpolation
