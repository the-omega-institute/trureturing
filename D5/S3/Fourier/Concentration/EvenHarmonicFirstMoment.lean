/- GID: D5/S3/Fourier/Concentration/EvenHarmonicFirstMoment
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/EvenHarmonicFirstMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consecutive vanishing even harmonics give an attained bound on the first harmonic. -/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset MeasureTheory Polynomial

namespace D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment

universe u

/-- The sharp first harmonic magnitude when the first N−1 even harmonics vanish. -/
noncomputable def firstHarmonicBound (N : ℕ) : ℝ :=
  1 / ((N : ℝ) * Real.sin (Real.pi / (2 * N)))

private theorem resolvent_polynomial {n : ℕ} (R : ℝ[X]) (hR : R.natDegree ≤ n + 1)
    (s : ℝ) (hs : 0 < s) (hr : 0 < R.eval (-s)) :
    ∃ p : ℝ[X], p.natDegree ≤ n ∧
      ∀ y : ℝ, 0 ≤ y →
        p.eval y = y / (y + s) + s * R.eval y / ((y + s) * R.eval (-s)) := by
  let q := X + C (s / R.eval (-s)) * R
  have hroot : IsRoot q (-s) := by
    simp only [IsRoot.def, q, eval_add, eval_X, eval_C_mul]
    rw [div_mul_cancel₀ _ hr.ne', neg_add_cancel]
  obtain ⟨p, hp⟩ := dvd_iff_isRoot.mpr hroot
  have hdegree : q.natDegree ≤ n + 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact (natDegree_C_mul_le _ R).trans hR
  refine ⟨p, ?_, ?_⟩
  · by_cases hp0 : p = 0
    · simp [hp0]
    have hpdeg := (monic_X_sub_C (-s)).natDegree_mul' hp0
    rw [← hp, natDegree_X_sub_C] at hpdeg
    omega
  intro y hy
  have hs' : 0 < y + s := add_pos_of_nonneg_of_pos hy hs
  have heval := congrArg (Polynomial.eval y) hp
  simp only [q, eval_add, eval_X, eval_mul, eval_sub, eval_C] at heval
  rw [sub_neg_eq_add] at heval
  field_simp [hs'.ne', hr.ne'] at heval ⊢
  linear_combination -heval

/-- Divisibility at the negative pole gives a polynomial majorant that is exact at the nodes. -/
private theorem resolvent_moment_comparison {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (v : J → ℝ) (x : I → ℝ) (y : J → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j)
    (n : ℕ) (R : ℝ[X]) (hR : R.natDegree ≤ n + 1)
    (hpos : ∀ i, 0 ≤ R.eval (x i)) (hzero : ∀ j, R.eval (y j) = 0)
    (hmatch : ∀ p : ℝ[X], p.natDegree ≤ n →
      ∑ i, w i * p.eval (x i) = ∑ j, v j * p.eval (y j))
    (s : ℝ) (hs : 0 < s) (hneg : 0 < R.eval (-s)) :
    ∑ i, w i * (x i / (x i + s)) ≤ ∑ j, v j * (y j / (y j + s)) := by
  obtain ⟨p, hp, hpe⟩ := resolvent_polynomial R hR s hs hneg
  calc
    _ ≤ ∑ i, w i * p.eval (x i) := by
      apply sum_le_sum
      intro i _
      rw [hpe _ (hx i)]
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (div_nonneg (mul_nonneg hs.le (hpos i))
          (mul_nonneg (add_nonneg (hx i) hs.le) hneg.le))) (hw i)
    _ = ∑ j, v j * p.eval (y j) := hmatch p hp
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [hpe _ (hy j), hzero j, mul_zero, zero_div, add_zero]

private theorem integral_resolvent {y : ℝ} (hy : 0 ≤ y) :
    Integrable (fun t : ℝ => y / (y + t ^ 2)) ∧
      (∫ t : ℝ, y / (y + t ^ 2)) = Real.pi * Real.sqrt y := by
  by_cases h0 : y = 0
  · simp [h0]
  have hr : 0 < Real.sqrt y := Real.sqrt_pos.2 (lt_of_le_of_ne hy (Ne.symm h0))
  have hr2 := Real.sq_sqrt hy
  have hc : (fun t : ℝ => y / (y + t ^ 2)) =
      fun t => (1 + ((Real.sqrt y)⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    nth_rw 1 [← hr2]
    field_simp [hr.ne']
    rw [hr2]
  rw [hc]
  refine ⟨integrable_inv_one_add_mul_sq (inv_ne_zero hr.ne'), ?_⟩
  rw [integral_univ_inv_one_add_mul_sq, abs_of_nonneg (by positivity), div_inv_eq_mul]

/-- Integrate the resolvent comparison to obtain the order of the square-root means. -/
private theorem sqrt_moment_comparison {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (v : J → ℝ) (x : I → ℝ) (y : J → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j)
    (n : ℕ) (R : ℝ[X]) (hR : R.natDegree ≤ n + 1)
    (hpos : ∀ i, 0 ≤ R.eval (x i)) (hzero : ∀ j, R.eval (y j) = 0)
    (hmatch : ∀ p : ℝ[X], p.natDegree ≤ n →
      ∑ i, w i * p.eval (x i) = ∑ j, v j * p.eval (y j))
    (hneg : ∀ s : ℝ, 0 < s → 0 < R.eval (-s)) :
    ∑ i, w i * Real.sqrt (x i) ≤ ∑ j, v j * Real.sqrt (y j) := by
  have hi (i : I) : Integrable (fun t : ℝ => w i * (x i / (x i + t ^ 2))) :=
    (integral_resolvent (hx i)).1.const_mul _
  have hj (j : J) : Integrable (fun t : ℝ => v j * (y j / (y j + t ^ 2))) :=
    (integral_resolvent (hy j)).1.const_mul _
  have hcompare (t : ℝ) (ht : t ≠ 0) :
      ∑ i, w i * (x i / (x i + t ^ 2)) ≤ ∑ j, v j * (y j / (y j + t ^ 2)) := by
    have hp : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    exact resolvent_moment_comparison w v x y hw hx hy n R hR hpos hzero hmatch
      _ hp (hneg _ hp)
  have hmeasure : ∀ᵐ t : ℝ, t ≠ 0 :=
    ae_iff.2 (by simp)
  have h := integral_mono_ae (integrable_finsetSum _ (fun i _ => hi i))
    (integrable_finsetSum _ (fun j _ => hj j)) (hmeasure.mono hcompare)
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun j _ => hj j)] at h
  simp_rw [integral_const_mul, (integral_resolvent (hx _)).2,
    (integral_resolvent (hy _)).2, mul_left_comm _ Real.pi, ← mul_sum] at h
  exact le_of_mul_le_mul_left h Real.pi_pos

open Polynomial.Chebyshev

/-- A single Chebyshev polynomial gives nonnegative nodal factors for both parities. -/
private noncomputable def arcNodePolynomial (N : ℕ) : ℝ[X] :=
  1 + C ((-1 : ℝ) ^ N) * (T ℝ (N : ℤ)).comp (C 2 * X - 1)

private theorem arcNodePolynomial_eval (N : ℕ) (y : ℝ) :
    (arcNodePolynomial N).eval y = 1 + (-1 : ℝ) ^ N * (T ℝ (N : ℤ)).eval (2 * y - 1) := by
  simp [arcNodePolynomial, eval_comp]

private theorem arcNodePolynomial_degree (N : ℕ) : (arcNodePolynomial N).natDegree ≤ N := by
  unfold arcNodePolynomial
  apply natDegree_add_le_of_degree_le
  · simp
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_comp, natDegree_T]
  have hg : (C (2 : ℝ) * X - 1).natDegree = 1 := by
    rw [show (1 : ℝ[X]) = C 1 by simp, natDegree_sub_C, natDegree_C_mul_X _ (by norm_num)]
  simp [hg]

private theorem arcNodePolynomial_nonneg (N : ℕ) {y : ℝ} (h₀ : 0 ≤ y) (h₁ : y ≤ 1) :
    0 ≤ (arcNodePolynomial N).eval y := by
  rw [arcNodePolynomial_eval]
  have ht := abs_eval_T_real_le_one (N : ℤ)
    (show |2 * y - 1| ≤ 1 by rw [abs_le]; constructor <;> linarith)
  have hsign : |(-1 : ℝ) ^ N| = 1 := by rw [abs_pow]; norm_num
  have hm : |(-1 : ℝ) ^ N * (T ℝ (N : ℤ)).eval (2 * y - 1)| ≤ 1 := by
    rwa [abs_mul, hsign, one_mul]
  linarith only [(abs_le.mp hm).1]

private theorem arcNodePolynomial_positive_at_negative (N : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < (arcNodePolynomial N).eval (-s) := by
  rw [arcNodePolynomial_eval,
    show 2 * (-s) - 1 = -(1 + 2 * s) by ring, T_eval_neg]
  rw [Int.cast_negOnePow_natCast ℝ N, ← mul_assoc, ← mul_pow]
  norm_num
  have ht := one_le_eval_T_real (N : ℤ) (show 1 ≤ 1 + 2 * s by linarith)
  linarith only [ht]

private theorem arcNodePolynomial_zero_on_arc (N : ℕ) (hN : 0 < N) (j : ℕ) :
    (arcNodePolynomial N).eval
      ((Real.cos (Real.pi * ((j : ℝ) - ((N : ℝ) - 1) / 2) / N)) ^ 2) = 0 := by
  rw [arcNodePolynomial_eval, ← Real.cos_two_mul, T_real_cos]
  push_cast
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hangle :
      (N : ℝ) * (2 * (Real.pi * ((j : ℝ) - ((N : ℝ) - 1) / 2) / N)) =
        2 * Real.pi * j - Real.pi * ((N : ℝ) - 1) := by
    field_simp
  rw [hangle, Real.cos_sub]
  have hcos : Real.cos (2 * Real.pi * j) = 1 := by
    rw [show 2 * Real.pi * (j : ℝ) = j * (2 * Real.pi) by ring,
      Real.cos_nat_mul_two_pi]
  have hsin : Real.sin (2 * Real.pi * j) = 0 := by
    rw [show 2 * Real.pi * (j : ℝ) = 0 + j * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_zero]
  rw [hcos, hsin, zero_mul, add_zero, one_mul,
    show Real.pi * ((N : ℝ) - 1) = (N : ℝ) * Real.pi - Real.pi by ring,
    Real.cos_sub_pi, Real.cos_nat_mul_pi, mul_neg, ← mul_pow]
  norm_num

private noncomputable def chebSequence : Polynomial.Sequence ℝ where
  elems' j := T ℝ (j : ℤ)
  degree_eq' j := by simp [degree_T]

private theorem polynomial_means_eq_of_cheb {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (v : J → ℝ) (x : I → ℝ) (y : J → ℝ) (N : ℕ)
    (h : ∀ k : ℕ, k < N →
      ∑ i, w i * (T ℝ (k : ℤ)).eval (x i) = ∑ j, v j * (T ℝ (k : ℤ)).eval (y j))
    (p : ℝ[X]) (hp : p.natDegree < N) :
    ∑ i, w i * p.eval (x i) = ∑ j, v j * p.eval (y j) := by
  let left : ℝ[X] →ₗ[ℝ] ℝ := ∑ i, w i • leval (x i)
  let right : ℝ[X] →ₗ[ℝ] ℝ := ∑ j, v j • leval (y j)
  have hleft (q : ℝ[X]) : left q = ∑ i, w i * q.eval (x i) := by
    simp [left, LinearMap.sum_apply, smul_eq_mul]
  have hright (q : ℝ[X]) : right q = ∑ j, v j * q.eval (y j) := by
    simp [right, LinearMap.sum_apply, smul_eq_mul]
  have hspan : Submodule.span ℝ (chebSequence '' Set.Iio N) ≤ LinearMap.ker (left - right) := by
    rw [Submodule.span_le]
    rintro q ⟨k, hk, rfl⟩
    simp only [Set.mem_Iio] at hk
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, hleft, hright, sub_eq_zero]
    exact h k hk
  rw [chebSequence.span_degreeLT (fun k _ => isUnit_iff_ne_zero.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr (chebSequence.ne_zero k)))] at hspan
  have hm : p ∈ Polynomial.degreeLT ℝ N := by
    rw [Polynomial.mem_degreeLT]
    exact p.degree_le_natDegree.trans_lt (by exact_mod_cast hp)
  have he := LinearMap.mem_ker.mp (hspan hm)
  simpa only [LinearMap.sub_apply, hleft, hright, sub_eq_zero] using he

private noncomputable def arcAngle (N j : ℕ) : ℝ := Real.pi * ((j : ℝ) - ((N : ℝ) - 1) / 2) / N
private noncomputable def arcPhase (N j : ℕ) : ℂ := Complex.exp ((arcAngle N j : ℂ) * Complex.I)

private theorem arc_phase_norm (N j : ℕ) : ‖arcPhase N j‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem arc_even_sum_zero {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    ∑ j ∈ range N, arcPhase N j ^ (2 * k) = 0 := by
  have hN : N ≠ 0 := by omega
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  let angle : ℂ := 2 * Real.pi * Complex.I * k / N
  let q := Complex.exp angle
  let offset : ℂ := -(angle * ((N : ℂ) - 1) / 2)
  have hq : q ≠ 1 := by
    intro h
    have hd := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hN).1 h
    exact (not_le_of_gt hkN) (Nat.le_of_dvd hk hd)
  have hqN : q ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have heq : (N : ℂ) * angle = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      dsimp [angle]
      field_simp
    rw [heq, Complex.exp_eq_one_iff]
    exact ⟨k, by simp⟩
  have hpoint (j : ℕ) :
      arcPhase N j ^ (2 * k) = Complex.exp offset * q ^ j := by
    rw [arcPhase, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [arcAngle, angle, offset, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simp_rw [hpoint, ← mul_sum]
  rw [geom_sum_eq hq, hqN, sub_self, zero_div, mul_zero]

private theorem arc_cos_sum {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ range N, Real.cos (arcAngle N j) = 1 / Real.sin (Real.pi / (2 * N)) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  let d := Real.pi / (2 * N)
  let s (j : ℕ) := Real.sin (Real.pi * ((j : ℝ) / N - 1 / 2))
  have hstep (j : ℕ) :
      2 * Real.sin d * Real.cos (arcAngle N j) = s (j + 1) - s j := by
    have ha : Real.pi * (((j + 1 : ℕ) : ℝ) / N - 1 / 2) = arcAngle N j + d := by
      push_cast
      dsimp [arcAngle, d]
      field_simp
      ring
    have hb : Real.pi * ((j : ℝ) / N - 1 / 2) = arcAngle N j - d := by
      dsimp [arcAngle, d]
      field_simp
      ring
    dsimp [s]
    rw [ha, hb, Real.sin_add, Real.sin_sub]
    ring
  have hsum : 2 * Real.sin d * (∑ j ∈ range N, Real.cos (arcAngle N j)) = 2 := by
    rw [mul_sum]
    simp_rw [hstep]
    rw [sum_range_sub]
    dsimp [s]
    rw [div_self hN', show Real.pi * (1 - 1 / 2) = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
    norm_num [show Real.pi * (- (1 / 2)) = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
  have hd : 0 < d := by dsimp [d]; positivity
  have hlt : d < Real.pi := by
    have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [hN₁, Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hd hlt
  exact (eq_div_iff hs.ne').2 (by nlinarith only [hsum])

private theorem cheb_re_power (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    (T ℝ (k : ℤ)).eval z.re = (z ^ k).re := by
  have he : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
    simpa [hz] using Complex.norm_mul_exp_arg_mul_I z
  nth_rw 1 [← he]
  rw [Complex.exp_ofReal_mul_I_re, T_real_cos]
  nth_rw 2 [← he]
  rw [← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
  push_cast
  congr 2
  ring

private theorem unit_square_projection (z : ℂ) (hz : ‖z‖ = 1) :
    (z ^ 2).re = 2 * z.re ^ 2 - 1 := by
  have h := Complex.normSq_eq_norm_sq z
  rw [hz, one_pow, Complex.normSq_apply] at h
  simp only [pow_two, Complex.mul_re]
  linarith only [h]

private theorem arc_projection_nonneg {N : ℕ} (hN : 0 < N) (j : Fin N) :
    0 ≤ Real.cos (arcAngle N j) := by
  apply Real.cos_nonneg_of_mem_Icc
  have hN' : (0 : ℝ) < N := by positivity
  have hj : (j : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j := by positivity
  constructor
  · apply (le_div_iff₀ hN').2
    nlinarith only [mul_nonneg Real.pi_pos.le hj0, Real.pi_pos]
  · apply (div_le_iff₀ hN').2
    nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hj), Real.pi_pos]

/-- The even moments fix polynomial means of the squared real projections. -/
private theorem square_projection_upper {I : Type*} [Fintype I]
    (w : I → ℝ) (z : I → ℂ) (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hz : ∀ i, ‖z i‖ = 1) (N : ℕ) (hN : 0 < N)
    (hm : ∀ k : ℕ, 0 < k → k < N → ∑ i, (w i : ℂ) * z i ^ (2 * k) = 0) :
    ∑ i, w i * (z i).re ≤ 1 / ((N : ℝ) * Real.sin (Real.pi / (2 * N))) := by
  let v (_ : Fin N) : ℝ := (N : ℝ)⁻¹
  let y (j : Fin N) : ℝ := Real.cos (arcAngle N j) ^ 2
  let x (i : I) : ℝ := (z i).re ^ 2
  have hx₀ (i : I) : 0 ≤ x i := sq_nonneg _
  have hx₁ (i : I) : x i ≤ 1 := by
    have h := (Complex.abs_re_le_norm (z i)).trans_eq (hz i)
    change (z i).re ^ 2 ≤ 1
    simpa using (sq_le_sq.mpr (by simpa using h : |(z i).re| ≤ |(1 : ℝ)|))
  have hy₀ (j : Fin N) : 0 ≤ y j := sq_nonneg _
  have hv : ∑ j, v j = 1 := by
    have hN' : (N : ℝ) ≠ 0 := by positivity
    simp [v, nsmul_eq_mul, hN']
  have hphase₂ (j : Fin N) : (arcPhase N j ^ 2).re = 2 * y j - 1 := by
    rw [unit_square_projection _ (arc_phase_norm _ _)]
    rw [arcPhase, Complex.exp_ofReal_mul_I_re]
  have hphaseNorm₂ (j : Fin N) : ‖arcPhase N j ^ 2‖ = 1 := by
    rw [norm_pow, arc_phase_norm, one_pow]
  have hcheb (k : ℕ) (hkN : k < N) :
      ∑ i, w i * (T ℝ (k : ℤ)).eval (2 * x i - 1) =
        ∑ j, v j * (T ℝ (k : ℤ)).eval (2 * y j - 1) := by
    by_cases hk : k = 0
    · subst k
      simpa using hw₁.trans hv.symm
    have hz₂ (i : I) : ‖z i ^ 2‖ = 1 := by rw [norm_pow, hz i, one_pow]
    have hL (i : I) : (T ℝ (k : ℤ)).eval (2 * x i - 1) = (z i ^ (2 * k)).re := by
      rw [← unit_square_projection _ (hz i), cheb_re_power _ (hz₂ i), pow_mul]
    have hR (j : Fin N) : (T ℝ (k : ℤ)).eval (2 * y j - 1) =
        (arcPhase N j ^ (2 * k)).re := by
      rw [← hphase₂, cheb_re_power _ (hphaseNorm₂ j), pow_mul]
    simp_rw [hL, hR]
    have hl := congrArg Complex.re (hm k (by omega) hkN)
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.zero_re] at hl
    rw [hl]
    have hr : ∑ j : Fin N, arcPhase N j ^ (2 * k) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun j => arcPhase N j ^ (2 * k))]
      exact arc_even_sum_zero (by omega) hkN
    have hr' := congrArg Complex.re hr
    simp only [Complex.re_sum, Complex.zero_re] at hr'
    simp only [v, ← mul_sum, hr', mul_zero]
  have hmatch (p : ℝ[X]) (hp : p.natDegree ≤ N - 1) :
      ∑ i, w i * p.eval (x i) = ∑ j, v j * p.eval (y j) := by
    let affine : ℝ[X] := C (1 / 2 : ℝ) * X + C (1 / 2 : ℝ)
    have hd : affine.natDegree ≤ 1 := by
      dsimp [affine]
      apply natDegree_add_le_of_degree_le
      · exact (natDegree_C_mul_le _ _).trans (by simp)
      · simp
    have hp' : (p.comp affine).natDegree < N := by
      apply natDegree_comp_le.trans_lt
      have h := Nat.mul_le_mul_left p.natDegree hd
      simp only [mul_one] at h
      omega
    have hr := polynomial_means_eq_of_cheb w v (fun i => 2 * x i - 1)
      (fun j => 2 * y j - 1) N hcheb (p.comp affine) hp'
    have he (a : ℝ) : (p.comp affine).eval (2 * a - 1) = p.eval a := by
      rw [eval_comp]
      congr 1
      simp [affine]
      ring
    simpa only [he] using hr
  have hbound := sqrt_moment_comparison w v x y hw hx₀ hy₀ (N - 1) (arcNodePolynomial N)
    ((arcNodePolynomial_degree N).trans (by omega))
    (fun i => arcNodePolynomial_nonneg N (hx₀ i) (hx₁ i))
    (fun j => arcNodePolynomial_zero_on_arc N hN j.val) hmatch
    (arcNodePolynomial_positive_at_negative N)
  calc
    _ ≤ ∑ i, w i * Real.sqrt (x i) := sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (by
        dsimp [x]
        rw [Real.sqrt_sq_eq_abs]
        exact le_abs_self _) (hw i)
    _ ≤ ∑ j, v j * Real.sqrt (y j) := hbound
    _ = _ := by
      simp only [v, y, Real.sqrt_sq_eq_abs, abs_of_nonneg (arc_projection_nonneg hN _),
        ← mul_sum]
      rw [Fin.sum_univ_eq_sum_range (fun j => Real.cos (arcAngle N j)), arc_cos_sum hN]
      simp only [one_div, mul_inv]

private theorem even_block_first_upper {I : Type*} [Fintype I]
    (w : I → ℝ) (z : I → ℂ) (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hz : ∀ i, ‖z i‖ = 1) (N : ℕ) (hN : 0 < N)
    (hm : ∀ k : ℕ, 0 < k → k < N → ∑ i, (w i : ℂ) * z i ^ (2 * k) = 0) :
    ‖∑ i, (w i : ℂ) * z i‖ ≤ 1 / ((N : ℝ) * Real.sin (Real.pi / (2 * N))) := by
  let m := ∑ i, (w i : ℂ) * z i
  let u := Complex.exp ((m.arg : ℂ) * (-Complex.I))
  have hu : ‖u‖ = 1 := by
    have h : u = Complex.exp (((-m.arg : ℝ) : ℂ) * Complex.I) := by
      simp [u]
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hrot (i : I) : ‖u * z i‖ = 1 := by rw [norm_mul, hu, hz i, mul_one]
  have hrot_even (k : ℕ) (hk : 0 < k) (hkN : k < N) :
      ∑ i, (w i : ℂ) * (u * z i) ^ (2 * k) = 0 := by
    simp_rw [mul_pow, mul_left_comm (↑(w _) : ℂ), ← mul_sum, hm k hk hkN, mul_zero]
  have h := square_projection_upper w (fun i => u * z i) hw hw₁ hrot N hN hrot_even
  have hsum : (∑ i, (w i : ℂ) * (u * z i)) = u * m := by
    simp_rw [mul_left_comm (↑(w _) : ℂ), ← mul_sum]
    rfl
  have hreal : (∑ i, w i * (u * z i).re) = (u * m).re := by
    rw [← hsum]
    simp [Complex.re_sum, Complex.mul_re]
  have hum : u * m = (‖m‖ : ℂ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I m]
    unfold u
    rw [mul_left_comm, ← Complex.exp_add,
      show (m.arg : ℂ) * (-Complex.I) + (m.arg : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero, mul_one]
  rw [hreal, hum, Complex.ofReal_re] at h
  exact h

private theorem even_block_first_attained (N : ℕ) (hN : 0 < N) :
    ∃ (w : Fin N → ℝ) (z : Fin N → ℂ), (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∀ i, ‖z i‖ = 1) ∧
      (∀ k : ℕ, 0 < k → k < N → ∑ i, (w i : ℂ) * z i ^ (2 * k) = 0) ∧
      ‖∑ i, (w i : ℂ) * z i‖ = 1 / ((N : ℝ) * Real.sin (Real.pi / (2 * N))) := by
  let w (_ : Fin N) : ℝ := (N : ℝ)⁻¹
  let z (i : Fin N) : ℂ := arcPhase N i
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hw (i : Fin N) : 0 ≤ w i := by dsimp [w]; positivity
  have hw₁ : ∑ i, w i = 1 := by simp [w, nsmul_eq_mul, hN']
  have hz (i : Fin N) : ‖z i‖ = 1 := arc_phase_norm N i
  have hm (k : ℕ) (hk : 0 < k) (hkN : k < N) :
      ∑ i, (w i : ℂ) * z i ^ (2 * k) = 0 := by
    simp only [w, z, Complex.ofReal_inv, Complex.ofReal_natCast, ← mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun j => arcPhase N j ^ (2 * k)), arc_even_sum_zero hk hkN,
      mul_zero]
  refine ⟨w, z, hw, hw₁, hz, hm, le_antisymm (even_block_first_upper w z hw hw₁ hz N hN hm) ?_⟩
  have hre : (∑ i, (w i : ℂ) * z i).re =
      1 / ((N : ℝ) * Real.sin (Real.pi / (2 * N))) := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, w, z, arcPhase, Complex.exp_ofReal_mul_I_re, ← mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun j => Real.cos (arcAngle N j)), arc_cos_sum hN]
    simp only [one_div, mul_inv]
  rw [← hre]
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

/-- The bound for N−1 vanishing even harmonics is attained using N phases. -/
theorem sharp_first_harmonic_even_block (N : ℕ) (hN : 0 < N) :
    let bound := firstHarmonicBound N
    (∀ {J : Type u} [Fintype J] (w : J → ℝ) (z : J → ℂ),
      (∀ j, 0 ≤ w j) → (∑ j, w j = 1) → (∀ j, ‖z j‖ = 1) →
        (∀ k : ℕ, 0 < k → k < N → ∑ j, (w j : ℂ) * z j ^ (2 * k) = 0) →
          ‖∑ j, (w j : ℂ) * z j‖ ≤ bound) ∧
    (∃ (w : Fin N → ℝ) (z : Fin N → ℂ), (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, ‖z j‖ = 1) ∧
      (∀ k : ℕ, 0 < k → k < N → ∑ j, (w j : ℂ) * z j ^ (2 * k) = 0) ∧
        ‖∑ j, (w j : ℂ) * z j‖ = bound) :=
  ⟨fun w z hw hw₁ hz hm => even_block_first_upper w z hw hw₁ hz N hN hm,
    even_block_first_attained N hN⟩

#print axioms sharp_first_harmonic_even_block

end D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment
