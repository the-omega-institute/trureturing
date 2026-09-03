/- GID: D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Right half-strip zero-freeness implies RH by the zeta functional equation. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Right Half-Strip Riemann Reduction

The zeta functional equation reflects a zero strictly left of the critical
line and inside the critical strip to a zero in the open right half-strip.
Zeros with nonpositive real part are forced to be Mathlib's trivial zeros.
Thus excluding zeros in the open right half-strip suffices for Mathlib's
formulation of the Riemann hypothesis.

Library-search audit trail (2026-09-03):

* Exact D5 searches for the declaration name and its `hRight` binder missed.
  Shape searches found other zeta-zero and Riemann-hypothesis criteria, but no
  theorem with this right-half-strip hypothesis and conclusion.
* Pinned Mathlib defines `RiemannHypothesis` and supplies
  `riemannZeta_one_sub` and `riemannZeta_ne_zero_of_one_le_re`, but contains no
  declaration with the complete reduction statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

private lemma zeta_zero_trivial_of_re_nonpos {rho : Complex}
    (hzero : riemannZeta rho = 0) (hnonpos : rho.re <= 0) :
    exists n : Nat, rho = -2 * (n + 1) := by
  have hrhoZero : rho ≠ 0 := by
    intro hrho
    subst rho
    norm_num [riemannZeta_zero] at hzero
  let t : Complex := 1 - rho
  have htPos : 0 < t.re := by
    dsimp [t]
    linarith
  have htOne : 1 <= t.re := by
    dsimp [t]
    linarith
  have htNotNegNat : forall n : Nat, t ≠ -n := by
    intro n ht
    rw [ht] at htPos
    simp only [Complex.neg_re, Complex.natCast_re] at htPos
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) htPos
  have htNeOne : t ≠ 1 := by
    intro ht
    apply hrhoZero
    dsimp [t] at ht
    linear_combination -ht
  have htwoPi : (2 * (Real.pi : Complex)) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : (2 * (Real.pi : Complex)) ^ (-t) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero htwoPi]
    exact Complex.exp_ne_zero _
  have hgamma : Complex.Gamma t ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos htPos
  have hzetaT : riemannZeta t ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re htOne
  have hfunctional := riemannZeta_one_sub htNotNegNat htNeOne
  have hfactorZero :
      2 * (2 * (Real.pi : Complex)) ^ (-t) * Complex.Gamma t *
        Complex.cos ((Real.pi : Complex) * t / 2) * riemannZeta t = 0 := by
    rw [← hfunctional]
    simpa [t] using hzero
  have hprefactorZero :
      2 * (2 * (Real.pi : Complex)) ^ (-t) * Complex.Gamma t *
        Complex.cos ((Real.pi : Complex) * t / 2) = 0 :=
    (mul_eq_zero.mp hfactorZero).resolve_right hzetaT
  have hcos : Complex.cos ((Real.pi : Complex) * t / 2) = 0 := by
    rcases mul_eq_zero.mp hprefactorZero with hpre | hcos
    · exact False.elim <| (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hgamma) hpre
    · exact hcos
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hpi : (Real.pi : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcancel : (Real.pi : Complex) * t =
      (Real.pi : Complex) * (2 * (k : Complex) + 1) := by
    linear_combination (2 : Complex) * hk
  have htInteger : t = ((2 * k + 1 : Int) : Complex) := by
    have h := mul_left_cancel₀ hpi hcancel
    rw [h]
    push_cast
    ring
  have hkNonnegative : 0 <= k := by
    rw [htInteger, Complex.intCast_re] at htOne
    have hkBound : (1 : Int) <= 2 * k + 1 := by
      exact_mod_cast htOne
    omega
  have hrhoInteger : rho = -2 * (k : Complex) := by
    dsimp [t] at htInteger
    push_cast at htInteger
    linear_combination -htInteger
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hkNonnegative
  cases m with
  | zero =>
      have hkZero : k = 0 := by simpa using hm
      apply False.elim
      apply hrhoZero
      rw [hrhoInteger, hkZero]
      norm_num
  | succ n =>
      refine ⟨n, ?_⟩
      rw [hrhoInteger, hm]
      push_cast
      ring

/-- Mathlib's Riemann hypothesis supplies a compatible witness for the
right-half-strip premise. This is a satisfiability check, not an RH proof. -/
example (hRH : RiemannHypothesis) :
    forall rho : Complex, riemannZeta rho = 0 ->
      (1 : Real) / 2 < rho.re -> rho.re < 1 -> False := by
  intro rho hzero hhalf hlt
  have hnotTrivial : ¬(∃ n : Nat, rho = -2 * (n + 1)) := by
    rintro ⟨n, hn⟩
    rw [hn] at hhalf
    norm_num at hhalf
    have hnnonneg : (0 : Real) ≤ n := Nat.cast_nonneg n
    linarith
  have hneOne : rho ≠ 1 := by
    intro hrho
    rw [hrho] at hlt
    norm_num at hlt
  have hline := hRH rho hzero hnotTrivial hneOne
  linarith

/-- The complex numbers, which form the quantified domain, are inhabited. -/
example : Complex := 0

/-- If the Riemann zeta function has no zero in the open strip
`1 / 2 < re rho < 1`, then every Mathlib-nontrivial zero lies on the critical
line. -/
theorem golden_right_half_strip_implies_rh
    (hRight : forall rho : Complex, riemannZeta rho = 0 ->
      (1 : Real) / 2 < rho.re -> rho.re < 1 -> False) :
    RiemannHypothesis := by
  intro rho hzero hnotTrivial hneOne
  by_cases hline : rho.re = (1 : Real) / 2
  · exact hline
  by_cases hone : 1 <= rho.re
  · exact False.elim <| (riemannZeta_ne_zero_of_one_le_re hone) hzero
  have hltOne : rho.re < 1 := lt_of_not_ge hone
  by_cases hpositive : 0 < rho.re
  · by_cases hright : (1 : Real) / 2 < rho.re
    · apply False.elim
      apply hRight rho hzero
      · linarith
      · exact hltOne
    · have hltHalf : rho.re < (1 : Real) / 2 :=
        lt_of_le_of_ne (le_of_not_gt hright) hline
      have hnotNegNat : forall n : Nat, rho ≠ -n := by
        intro n hrho
        rw [hrho] at hpositive
        simp only [Complex.neg_re, Complex.natCast_re] at hpositive
        exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hpositive
      have hreflectedZero : riemannZeta (1 - rho) = 0 := by
        rw [riemannZeta_one_sub hnotNegNat hneOne, hzero]
        ring
      have hreflectedRight : (1 : Real) / 2 < (1 - rho).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have hreflectedLtOne : (1 - rho).re < 1 := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      exact False.elim <|
        hRight (1 - rho) hreflectedZero hreflectedRight hreflectedLtOne
  · apply False.elim
    apply hnotTrivial
    exact zeta_zero_trivial_of_re_nonpos hzero (le_of_not_gt hpositive)

#print axioms golden_right_half_strip_implies_rh

end D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
