import D5.S3.Analytic.Interpolation.SchurConjugateSlope
import D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

noncomputable section
open Set Metric Complex Polynomial
open D5.S3.Analytic.Interpolation.SchurConjugateSlope
open D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
open D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation (h Q)

namespace SchurQuarticExactCheck
private def eps (d : ℝ) : ℝ := d ^ 2 / 6
private def scale (d : ℝ) : ℝ := Real.sqrt (1 + 4 * eps d ^ 2)
private def poly (d : ℝ) : Polynomial ℝ :=
  C (1 / (6 * scale d)) * X ^ 3 +
  C (eps d / (2 * scale d)) * X ^ 2 -
  C (eps d / (12 * scale d)) * X ^ 4
private def quartic (d : ℝ) (z : ℂ) : ℂ :=
  (z ^ 3 / 6 + (eps d : ℂ) * (z ^ 2 / 2 - z ^ 4 / 12)) / (scale d : ℂ)
private def node (d : ℝ) : ℂ := (1 - (d : ℂ)) + (Real.sqrt 3 * d : ℝ) * I
private def other (d : ℝ) : ℂ := (1 - (d : ℂ)) - (Real.sqrt 3 * d : ℝ) * I
private def error (d : ℝ) (g : ℂ → ℂ) : ℂ :=
  deriv g 1 - (g (node d) - g (other d)) / (node d - other d)
private def monomial (t : ℤ) (z : ℂ) : ℂ := z ^ t.toNat / ((t : ℂ) * ((t : ℂ) - 1))
private def values (d : ℝ) : Set ℝ :=
  {r | ∃ t : ℤ, 2 ≤ t ∧ r = ‖error d (monomial t)‖}

example (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1 / 2) :
    (∀ z : ℂ, (poly d).eval₂ (algebraMap ℝ ℂ) z = quartic d z) ∧
    (poly d).natDegree = 4 ∧
    node d ≠ other d ∧ node d ∈ closedBall (0 : ℂ) 1 ∧
    other d = conj (node d) ∧
    (∀ g : ℂ → ℂ, error d g = deriv g 1 -
      deriv (interpolant g (1 - d) (Real.sqrt 3 * d)) 1) ∧
    quartic d ∈ entireClass ∧ diskNorm (quartic d) = 1 ∧
    error d (quartic d) = ((d * Real.sqrt (1 + d ^ 4 / 9) : ℝ) : ℂ) ∧
    d < d * Real.sqrt (1 + d ^ 4 / 9) ∧
    (∀ t : ℤ, 2 ≤ t →
      error d (monomial t) / (d : ℂ) =
        Q t.toNat 2 1 (negConjPair (1 - d) (Real.sqrt 3 * d) + 1)) ∧
    (values d).Nonempty ∧ BddAbove (values d) ∧ sSup (values d) = d ∧
    error d (monomial 2) = (d : ℂ) ∧ error d (monomial 3) = (d : ℂ) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have he : 0 < eps d := by unfold eps; positivity
  have he0 : eps d ≠ 0 := ne_of_gt he
  have hs : 0 < scale d := by unfold scale; positivity
  have hs0 : scale d ≠ 0 := ne_of_gt hs
  have hsC : (scale d : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hs2 : scale d ^ 2 = 1 + 4 * eps d ^ 2 := Real.sq_sqrt (by positivity)
  have hb : 0 < Real.sqrt 3 * d := by positivity
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hab : (1 - d) ^ 2 + (Real.sqrt 3 * d) ^ 2 ≤ 1 := by
    rw [mul_pow, h3]
    nlinarith
  have hw : ((1 - d : ℝ) : ℂ) + ((Real.sqrt 3 * d : ℝ) : ℂ) * I ≠ 1 := by
    intro H
    have H' := congrArg Complex.im H
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
      mul_zero, add_zero, zero_add, one_im] at H'
    linarith
  have hnv : node d - other d = 2 * ((Real.sqrt 3 * d : ℝ) : ℂ) * I := by
    unfold node other
    ring
  have hnv0 : node d - other d ≠ 0 := by
    rw [hnv]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt hb)) I_ne_zero
  have hnodes : node d ≠ other d := sub_ne_zero.mp hnv0
  have hconj : other d = conj (node d) := by
    simp [other, node, map_add, map_mul]
  have hnodeball : node d ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_le_one_iff]
    simpa [node, Complex.normSq_apply, pow_two] using hab
  have hinterp (g : ℂ → ℂ) : error d g = deriv g 1 -
      deriv (interpolant g (1 - d) (Real.sqrt 3 * d)) 1 := by
    rw [interpolant_deriv]
    simp only [error, slope, node, other, ofReal_sub, ofReal_one, hnv]
  have hpoly (z : ℂ) : (poly d).eval₂ (algebraMap ℝ ℂ) z = quartic d z := by
    simp [poly, quartic, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow]
    ring
  have hdeg : (poly d).natDegree = 4 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · unfold poly
      compute_degree!
    · simp [poly, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow]
      exact div_ne_zero he0 (mul_ne_zero (by norm_num) hs0)
  let first : ℂ → ℂ := fun z =>
    (z ^ 2 / 2 + (eps d : ℂ) * (z - z ^ 3 / 3)) / (scale d : ℂ)
  let second : ℂ → ℂ := fun z =>
    (z + (eps d : ℂ) * (1 - z ^ 2)) / (scale d : ℂ)
  have hg1 (z : ℂ) : HasDerivAt (quartic d) (first z) z := by
    convert ((((hasDerivAt_id z).pow 3).div_const 6).add
      ((hasDerivAt_const z (eps d : ℂ)).mul
        ((((hasDerivAt_id z).pow 2).div_const 2).sub
          (((hasDerivAt_id z).pow 4).div_const 12)))).div_const (scale d : ℂ) using 1 <;>
      dsimp [quartic, first] <;> ring
  have hg2 (z : ℂ) : HasDerivAt first (second z) z := by
    convert ((((hasDerivAt_id z).pow 2).div_const 2).add
      ((hasDerivAt_const z (eps d : ℂ)).mul
        ((hasDerivAt_id z).sub (((hasDerivAt_id z).pow 3).div_const 3)))).div_const
          (scale d : ℂ) using 1 <;> dsimp [first, second] <;> ring
  have hg : Differentiable ℂ (quartic d) := fun z => (hg1 z).differentiableAt
  have hderiv : deriv (quartic d) = first := funext fun z => (hg1 z).deriv
  have hsecond : deriv (deriv (quartic d)) = second := by
    rw [hderiv]
    exact funext fun z => (hg2 z).deriv
  let f : ℂ → ℂ := fun z => z + (eps d : ℂ) * (1 - z ^ 2)
  have hf : Differentiable ℂ f := by dsimp [f]; fun_prop
  have hcircle (z : ℂ) (hz : ‖z‖ = 1) : ‖f z‖ ≤ scale d := by
    have hxy : z.re ^ 2 + z.im ^ 2 = 1 := by
      have H := congrArg (fun r : ℝ => r ^ 2) hz
      simpa [Complex.sq_norm, Complex.normSq_apply, pow_two] using H
    have hfact : f z = z * (1 - 2 * (eps d : ℂ) * (z.im : ℂ) * I) := by
      apply Complex.ext <;>
        simp [f, pow_two, Complex.mul_re, Complex.mul_im] <;>
        nlinarith [hxy]
    rw [hfact, norm_mul, hz, one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) hs.le).mp
    rw [Complex.sq_norm, hs2]
    simp only [Complex.normSq_apply, sub_re, one_re, mul_re, ofReal_re, ofReal_im,
      ofNat_re, ofNat_im, I_re, I_im, mul_im, one_im, sub_im]
    have hnon := mul_nonneg (sq_nonneg (eps d)) (show 0 ≤ 1 - z.im ^ 2 by
      nlinarith [sq_nonneg z.re])
    nlinarith
  have hbound (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : ‖f z‖ ≤ scale d := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := ball (0 : ℂ) 1) isBounded_ball hf.diffContOnCl
    · intro w hw
      rw [frontier_ball (by norm_num : (1 : ℝ) ≠ 0)] at hw
      apply hcircle
      simpa only [mem_sphere, dist_zero_right] using hw
    · rwa [closure_ball (by norm_num : (0 : ℝ) < 1)]
  have hsecond_bound (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) :
      ‖deriv (deriv (quartic d)) z‖ ≤ 1 := by
    rw [hsecond]
    change ‖f z / (scale d : ℂ)‖ ≤ 1
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hs, div_le_one hs]
    exact hbound z hz
  have hunit : ‖deriv (deriv (quartic d)) I‖ = 1 := by
    rw [hsecond]
    change ‖f I / (scale d : ℂ)‖ = 1
    have hI : ‖f I‖ = scale d := by
      apply (sq_eq_sq₀ (norm_nonneg _) hs.le).mp
      rw [Complex.sq_norm, hs2]
      simp [f, Complex.normSq_apply, I_sq, pow_two]
      ring
    rw [norm_div, hI, norm_real, Real.norm_eq_abs, abs_of_pos hs, div_self hs0]
  have hbdd : BddAbove ((fun z => ‖deriv (deriv (quartic d)) z‖) ''
      closedBall (0 : ℂ) 1) := ⟨1, by rintro r ⟨z, hz, rfl⟩; exact hsecond_bound z hz⟩
  have hnorm : diskNorm (quartic d) = 1 := by
    apply le_antisymm
    · exact csSup_le ⟨_, ⟨0, by simp, rfl⟩⟩
        (by rintro r ⟨z, hz, rfl⟩; exact hsecond_bound z hz)
    · rw [← hunit]
      exact le_csSup hbdd ⟨I, by simp, rfl⟩
  have hmember : quartic d ∈ entireClass := ⟨hg, by rw [hnorm]⟩
  have hsformula : scale d = Real.sqrt (1 + d ^ 4 / 9) := by
    congr 1
    unfold eps
    ring
  have herror : error d (quartic d) = (d : ℂ) * (scale d : ℂ) := by
    unfold error
    rw [hderiv]
    dsimp [quartic, node, other, first]
    have h3C : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast h3
    have hs2C : (scale d : ℂ) ^ 2 = 1 + 4 * (eps d : ℂ) ^ 2 := by
      exact_mod_cast hs2
    have heC : (eps d : ℂ) = (d : ℂ) ^ 2 / 6 := by simp [eps]
    field_simp [hsC, hnv0]
    simp only [ofReal_mul, ofReal_sub, ofReal_one] at *
    ring_nf
    simp only [I_sq, h3C] at *
    linear_combination (d : ℂ) * hs2C
  have hstrict : d < d * Real.sqrt (1 + d ^ 4 / 9) := by
    have H : 1 < Real.sqrt (1 + d ^ 4 / 9) := by
      rw [Real.one_lt_sqrt (by positivity)]
      positivity
    nlinarith
  let m : ℕ → ℂ → ℂ := fun n z => z ^ n / ((n : ℂ) * ((n : ℂ) - 1))
  have hmon (n : ℕ) (hn : 2 ≤ n) :
      error d (m n) = (d : ℂ) * Q n 2 1 (negConjPair (1 - d) (Real.sqrt 3 * d) + 1) := by
    have hpow : (node d - other d) * h (n - 1)
        (conjPair (1 - d) (Real.sqrt 3 * d)) = (node d) ^ n - (other d) ^ n := by
      rw [h_eq_twoH]
      simpa [conjPair, node, other, ofReal_sub, ofReal_one,
        Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        twoH_sub_mul (n - 1) (node d) (other d)
    have hdiv : ((node d) ^ n - (other d) ^ n) / (node d - other d) =
        h (n - 1) (conjPair (1 - d) (Real.sqrt 3 * d)) := by
      exact (div_eq_iff hnv0).mpr (by rw [mul_comm]; exact hpow.symm)
    have hdmon : deriv (m n) 1 = (n : ℂ) / ((n : ℂ) * ((n : ℂ) - 1)) := by
      simpa [m] using (((hasDerivAt_id (1 : ℂ)).pow n).div_const
        ((n : ℂ) * ((n : ℂ) - 1))).deriv
    rw [(Q_two_node_closed_form n (1 - d) (Real.sqrt 3 * d) hn hab hw).1]
    unfold error
    rw [hdmon]
    dsimp [m]
    rw [← sub_div, div_div_comm, hdiv]
    simp only [ofReal_sub, ofReal_one]
    field_simp
    ring
  have hinter (t : ℤ) (ht : 2 ≤ t) : monomial t = m t.toNat := by
    have H : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
    have HC : (t.toNat : ℂ) = (t : ℂ) := by exact_mod_cast H
    simp only [monomial, m, HC]
  have hcorr (t : ℤ) (ht : 2 ≤ t) :
      error d (monomial t) / (d : ℂ) =
      Q t.toNat 2 1 (negConjPair (1 - d) (Real.sqrt 3 * d) + 1) := by
    rw [hinter t ht, hmon _ (by omega)]
    exact mul_div_cancel_left₀ _ hdC
  have hmonbound (t : ℤ) (ht : 2 ≤ t) : ‖error d (monomial t)‖ ≤ d := by
    have hq : ‖Q t.toNat 2 1 (negConjPair (1 - d) (Real.sqrt 3 * d) + 1)‖ ≤ 1 :=
      (first_inequality_region (1 - d) (Real.sqrt 3 * d) hab hw).2.1.mpr
        ((first_inequality_region (1 - d) (Real.sqrt 3 * d) hab hw).2.2.1.mpr
          (by rw [mul_pow, h3]; ring_nf; exact le_rfl)) _ (by omega)
    rw [hinter t ht, hmon _ (by omega), norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hd]
    nlinarith
  have htwo : error d (monomial 2) = (d : ℂ) := by
    rw [hinter 2 (by norm_num), hmon 2 (by norm_num),
      (Q_two_node_closed_form 2 (1 - d) (Real.sqrt 3 * d) (by norm_num) hab hw).2,
      mul_one]
  have hthree : error d (monomial 3) = (d : ℂ) := by
    unfold error
    have HM : deriv (monomial 3) 1 = (1 / 2 : ℂ) := by
      simpa [monomial] using (((hasDerivAt_id (1 : ℂ)).pow 3).div_const (6 : ℂ)).deriv
    rw [HM]
    dsimp [monomial, node, other]
    have h3C : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast h3
    field_simp [hnv0]
    simp only [ofReal_mul]
    ring_nf
    simp only [I_sq, h3C]
    ring
  have hnonempty : (values d).Nonempty := ⟨d, 2, by norm_num, by
    rw [htwo, norm_real, Real.norm_eq_abs, abs_of_pos hd]⟩
  have hbounded : BddAbove (values d) := ⟨d, by
    rintro r ⟨t, ht, rfl⟩
    exact hmonbound t ht⟩
  have hsup : sSup (values d) = d := by
    apply le_antisymm (csSup_le hnonempty (by
      rintro r ⟨t, ht, rfl⟩; exact hmonbound t ht))
    exact le_csSup hbounded ⟨2, by norm_num, by
      rw [htwo, norm_real, Real.norm_eq_abs, abs_of_pos hd]⟩
  refine ⟨hpoly, hdeg, hnodes, hnodeball, hconj, hinterp, hmember, hnorm, ?_,
    hstrict, hcorr, hnonempty, hbounded, hsup, htwo, hthree⟩
  simpa only [ofReal_mul, hsformula] using herror

end SchurQuarticExactCheck
