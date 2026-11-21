/- GID: D5/S3/Observer/Linear/ReflectingHeatQuantileGramian
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatQuantileGramian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian, lake/module/D5.S3.Observer.Linear.ReflectingHeatSaddleBoundary]
   utility: none
   digest: The equal-mass multiplier bounds the physical inverse Gramian diagonal. -/

import D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian
import D5.S3.Observer.Linear.ReflectingHeatSaddleBoundary

/-! The canonical multiplier in the physical reflecting heat moment problem. -/

open Filter MeasureTheory Set
open scoped BigOperators Topology

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

/-- The two-sided logarithmic estimate on the actual positive modes of the
reflecting heat Gramian at the unique saddle for the physical window. -/
theorem physical_log_inverse_diagonal_error (n : ℕ) (j : Mode n) {T : ℝ} (hT : 0 < T) :
    let a := (n : ℝ) * T
    |Real.log (Real.sqrt ((physicalGramian n T)⁻¹ j j)) -
      (n : ℝ) * saddleRate a (saddleRadius a) (rate n j)| ≤
        20 * (1 + Real.log (n : ℝ) + |Real.log a|) := by
  have hn : 0 < (n : ℝ) := by
    have := j.isLt
    exact_mod_cast (show 0 < n by omega)
  obtain ⟨hβ, hs⟩ := saddleRadius_spec (mul_pos hn hT)
  have hImag := imaginaryPotential_eval_at_saddle n hn (mul_pos hn hT) hβ hs
  exact log_inverse_diagonal_error_at_saddle_radius n j hT hβ hs hImag
    (saddle_real_cancellation n hn (mul_pos hn hT) hβ hs)

private theorem radius_between {β y : ℝ} (hβ : 0 ≤ β) (hy : 0 ≤ y) :
    y ≤ radius β y ∧ radius β y ≤ y + β := by
  unfold radius
  exact ⟨(Real.le_sqrt hy (by positivity)).2 (by linarith [sq_nonneg β]),
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_nonneg hβ hy]⟩⟩

private theorem saddleLogAverage_le_log_linear {β y : ℝ} (hβ : 0 < β) (hy : 1 ≤ y) :
    saddleLogAverage β y ≤ Real.log ((5 + 2 * β) * y) := by
  let r (θ : ℝ) := 2 - 2 * Real.cos θ
  let f (θ : ℝ) := Real.log (radius β y + radius β (r θ))
  have hp (θ : ℝ) : 0 < radius β y + radius β (r θ) := by unfold radius; positivity
  have hc : Continuous f :=
    Continuous.log (by unfold r radius; fun_prop) (fun θ => (hp θ).ne')
  have hbound (θ : ℝ) : f θ ≤ Real.log ((5 + 2 * β) * y) := by
    apply Real.log_le_log (hp θ)
    have hr0 : 0 ≤ r θ := by dsimp [r]; linarith [Real.cos_le_one θ]
    have hr4 : r θ ≤ 4 := by dsimp [r]; linarith [Real.neg_one_le_cos θ]
    have h₁ := (radius_between hβ.le (by linarith : 0 ≤ y)).2
    have h₂ := (radius_between hβ.le hr0).2
    nlinarith [mul_nonneg (show 0 ≤ y - 1 by linarith)
      (show 0 ≤ 4 + 2 * β by positivity)]
  have hi := intervalIntegral.integral_mono_on Real.pi_pos.le
    (hc.intervalIntegrable (μ := volume) 0 Real.pi) intervalIntegrable_const
    (fun θ _ => hbound θ)
  unfold saddleLogAverage spectralAverage
  change (∫ θ in 0..Real.pi, f θ) / Real.pi ≤ _
  apply (div_le_iff₀ Real.pi_pos).2
  simpa [intervalIntegral.integral_const, mul_comm] using hi

/-- The imaginary-axis growth attains half the rescaled physical time, which
is also a global exponential type bound for the normalized canonical product. -/
theorem canonicalProduct_type_at_saddle (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2)
    (bins : EqualMassBins β (saddleDensity n β)) :
    (∀ z : ℂ, ‖bins.canonicalProduct z‖ ≤ Real.exp ((n : ℝ) * a / 2 * ‖z‖)) ∧
      Tendsto (fun y : ℝ => Real.log ‖bins.canonicalProduct ((y : ℂ) * Complex.I)‖ / y)
        atTop (𝓝 ((n : ℝ) * a / 2)) := by
  obtain ⟨_, hd, _, _⟩ := saddleDensity_spec n hn ha hβ hs
  let D := (n : ℝ) * a / (2 * Real.pi)
  have hD : 0 < D := by dsimp [D]; positivity
  let P y := imaginaryPotential β (saddleDensity n β) y
  let A := (n : ℝ) * a / 2
  have hImag := imaginaryPotential_eval_at_saddle n hn ha hβ hs
  have hwidth (y : ℝ) (hy : 0 ≤ y) : P y ≤ A * y := by
    have hlog := saddleLogAverage_mono hβ (le_refl 0) hy
    have hrad := (radius_between hβ.le hy).2
    rw [show P y = imaginaryPotential β (saddleDensity n β) y from rfl, hImag y hy]
    calc
      _ ≤ (n : ℝ) * (a / 2 * y) := by
        apply mul_le_mul_of_nonneg_left _ hn.le
        have h := mul_le_mul_of_nonneg_left
          (show radius β y - β ≤ y by linarith) (by positivity : 0 ≤ a / 2)
        linarith
      _ = A * y := by dsimp [A]; ring
  refine ⟨bins.canonicalProduct_half_width hβ hD (fun t ht => (hd t ht).2) hwidth, ?_⟩
  let B := A * β + (n : ℝ) * (Real.log (5 + 2 * β) - saddleLogAverage β 0) +
    Real.log (1 + (β ^ 2)⁻¹)
  let F y := Real.log ‖bins.canonicalProduct ((y : ℂ) * Complex.I)‖
  have hlog : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hB : Tendsto (fun y : ℝ => B / y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.const_mul B)
  have hlim : Tendsto (fun y : ℝ => A - (B / y + ((n : ℝ) + 2) * (Real.log y / y)))
      atTop (𝓝 A) := by
    simpa using (tendsto_const_nhds (x := A)).sub (hB.add (hlog.const_mul ((n : ℝ) + 2)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    obtain ⟨hlo, _⟩ := bins.canonicalProduct_imaginary_bounds hβ hD (fun t ht => (hd t ht).2) y
    have hlo' := Real.log_le_log (Real.exp_pos _) hlo
    rw [Real.log_exp] at hlo'
    have hJ := saddleLogAverage_le_log_linear hβ hy
    rw [Real.log_mul (by positivity : 5 + 2 * β ≠ 0) hy0.ne'] at hJ
    have he : 1 + y ^ 2 / β ^ 2 ≤ (1 + (β ^ 2)⁻¹) * y ^ 2 := by
      rw [div_eq_mul_inv, add_mul, one_mul, mul_comm (β ^ 2)⁻¹]
      linarith [pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hy 2]
    have he' := Real.log_le_log (show 0 < 1 + y ^ 2 / β ^ 2 by positivity) he
    rw [Real.log_mul (by positivity : 1 + (β ^ 2)⁻¹ ≠ 0) (sq_pos_of_pos hy0).ne',
      Real.log_pow] at he'
    have hR := (radius_between hβ.le hy0.le).1
    have hh : A * y - (B + ((n : ℝ) + 2) * Real.log y) ≤ F y := by
      change _ ≤ Real.log ‖bins.canonicalProduct ((y : ℂ) * Complex.I)‖
      rw [hImag y hy0.le] at hlo'
      dsimp [A, B]
      nlinarith [mul_nonneg (mul_nonneg hn.le ha.le) (sub_nonneg.mpr hR),
        mul_nonneg hn.le (sub_nonneg.mpr hJ)]
    change A - (B / y + ((n : ℝ) + 2) * (Real.log y / y)) ≤ F y / y
    calc
      _ = (A * y - (B + ((n : ℝ) + 2) * Real.log y)) / y := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hh hy0.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    obtain ⟨hlo, hhi⟩ := bins.canonicalProduct_imaginary_bounds hβ hD (fun t ht => (hd t ht).2) y
    have h := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hhi
    rw [Real.log_exp] at h
    exact (div_le_iff₀ hy0).2 (h.trans (hwidth y hy0.le))

#print axioms canonicalProduct_type_at_saddle
#print axioms physical_log_inverse_diagonal_error
#print axioms inverse_diagonal_lower_bound_at_saddle
#print axioms inverse_diagonal_upper_bound_of_quantiles

end D5.S3.Observer.Linear.ReflectingHeatInterpolation
