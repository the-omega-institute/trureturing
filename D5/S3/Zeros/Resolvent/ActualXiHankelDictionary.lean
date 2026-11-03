/- GID: D5/S3/Zeros/Resolvent/ActualXiHankelDictionary
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiHankelDictionary
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: Finite real-polynomial Hankel forms of actual xi derivatives equal folded complex squares. -/

import D5.S3.Zeros.Resolvent.ActualXiTaylorBounds
import Mathlib.Tactic

/-!
The coefficients on the left are derivatives of the original xi expression.
The right side uses a complex square, never a modulus square. Nonnegativity
requires the explicitly stated Riemann hypothesis. Spectral powers do not
assert any physical-space moment condition. Distinct off-line conjugate pairs,
not analytic multiplicities, are the folded negative-index counting objects;
no negative-index theorem is asserted here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Resolvent.ActualXiHankelDictionary
open Complex Finset
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary

/-- Real Taylor coefficients of the independently defined actual xi function. -/
def xiCoefficient (j : ℕ) : ℝ :=
  (iteratedDeriv (2 * j + 1) xiOdd 0 / ((2 * j + 1).factorial : ℂ)).re

private theorem xiCoefficient_eq (j : ℕ) : xiCoefficient j = (moment j).re := by
  rw [xiCoefficient, actual_xi_taylor_moment]

private theorem finite_square (N m : ℕ) (u : Fin (N + 1) → ℝ) (n : PositiveZero) :
    weight n * (node n ^ m * ∑ a : Fin (N + 1), (u a : ℂ) * node n ^ (a : ℕ)) ^ 2 =
      ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        ((u a : ℂ) * (u b : ℂ)) * (weight n * node n ^ (2 * m + (a : ℕ) + (b : ℕ))) := by
  rw [pow_two]
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  simp only [pow_add, pow_mul]
  ring

private theorem hankel_hasSum (N m : ℕ) (u : Fin (N + 1) → ℝ) :
    HasSum (fun n : PositiveZero => weight n *
      (node n ^ m * ∑ a : Fin (N + 1), (u a : ℂ) * node n ^ (a : ℕ)) ^ 2)
      (∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        ((u a : ℂ) * (u b : ℂ)) * moment (2 * m + (a : ℕ) + (b : ℕ))) := by
  have h := hasSum_sum (s := (univ : Finset (Fin (N + 1)))) (fun a _ =>
    hasSum_sum (s := (univ : Finset (Fin (N + 1)))) (fun b _ =>
      ((moment_summable (2 * m + (a : ℕ) + (b : ℕ))).hasSum).mul_left
        ((u a : ℂ) * (u b : ℂ))))
  exact h.congr_fun (finite_square N m u)

/-- The full finite real-polynomial dictionary, with its essential complex square. -/
theorem actual_xi_hankel_identity (N m : ℕ) (u : Fin (N + 1) → ℝ) :
    (∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      u a * u b * xiCoefficient (2 * m + (a : ℕ) + (b : ℕ))) =
    (∑' n : PositiveZero, weight n *
      (node n ^ m * ∑ a : Fin (N + 1), (u a : ℂ) * node n ^ (a : ℕ)) ^ 2).re := by
  rw [(hankel_hasSum N m u).tsum_eq]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, xiCoefficient_eq]

/-- Under RH only, the same actual derivative Hankel form is nonnegative. -/
theorem actual_xi_hankel_nonnegative_of_rh (hRH : RiemannHypothesis)
    (N m : ℕ) (u : Fin (N + 1) → ℝ) :
    0 ≤ ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      u a * u b * xiCoefficient (2 * m + (a : ℕ) + (b : ℕ)) := by
  rw [actual_xi_hankel_identity]
  rw [Complex.re_tsum (hankel_hasSum N m u).summable]
  apply tsum_nonneg
  intro n
  have hz := actualData.zero_isNontrivial n
  have hx : (actualData.zero n).re = 1 / 2 := by
    apply hRH _ hz.1
    · rintro ⟨k, hk⟩
      have hr := congrArg Complex.re hk
      norm_num at hr
      have hp := hz.2.1
      linarith
    · intro h
      have h1 := congrArg Complex.re h
      norm_num at h1
      linarith [hz.2.2]
  have hn := (node_real_iff n).mpr hx
  have hp := node_real_positive n hn
  have he : node n = ((node n).re : ℂ) := by
    apply Complex.ext <;> simp [hn]
  have hw : weight n = ((weight n).re : ℂ) := by
    apply Complex.ext <;> simp [hp.2.2]
  rw [he, hw]
  have hpoly : (∑ a : Fin (N + 1), (u a : ℂ) * ((node n).re : ℂ) ^ (a : ℕ)) =
      ((∑ a : Fin (N + 1), u a * (node n).re ^ (a : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hpoly]
  norm_cast
  exact mul_nonneg hp.2.1.le (sq_nonneg _)

end D5.S3.Zeros.Resolvent.ActualXiHankelDictionary
