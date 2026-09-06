/- GID: D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier
   mirror-E: none(waiver:analytic-obstruction-without-numerical-evidence)
   anchors: []
   digest: Transfer symmetric translations through the actual Weil correlation and bound the residual required by a candidate gap. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A boundary-sensitive obstruction to an interior near-ground-state candidate

The carrier is the existing, unrestricted `Zeta23.EF.weilTest`; no even-only
replacement of the full Weil form is introduced. Put
`B f(x) = f(x-t) + f(x+t) - c f(x)`, with `t,c` real.
The analytic content is the exact identity
`weilTest (B f) (B f) = weilTest f (B (B f))`.
It transfers the prime samples, both pole evaluations, and the Gamma integral
at once, before taking their difference. A compactly supported nonzero function
cannot satisfy `B f = 0` when `t > 0`.

Consequently, a coercive lower bound tested on `B f` forces a directional Weil
residual on `B^2 f`. The squared residual estimate below is a necessary condition,
not a proof of arithmetic coercivity or of RH. To use it for an operator on
`[-a,a]`, both shifted tests must remain in its form/operator test domain. In
particular, a margin `2t` in the original support suffices. Sharp boundary
truncations do not have that margin and are not excluded by this theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.WeilGroundModeShiftBarrier

open MeasureTheory Set
open Zeta23.EF
open scoped ComplexConjugate Convolution

noncomputable section

/-- The real self-adjoint symmetric translation filter used to probe an explicit
candidate. This is not a definition of a ground state or of the Weil operator. -/
def symmetricShiftDefect (t c : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f (x - t) + f (x + t) - (c : ℂ) * f x

private theorem continuous_defect {f : ℝ → ℂ} (hf : Continuous f) (t c : ℝ) :
    Continuous (symmetricShiftDefect t c f) :=
  ((hf.comp (continuous_id.sub continuous_const)).add
    (hf.comp (continuous_id.add continuous_const))).sub (continuous_const.mul hf)

private theorem compact_shift {f : ℝ → ℂ} (hfs : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun x => f (x - t)) := by
  simpa [Function.comp_def, sub_eq_add_neg] using
    hfs.comp_homeomorph (Homeomorph.addRight (-t))

private theorem compact_defect {f : ℝ → ℂ} (hfs : HasCompactSupport f) (t c : ℝ) :
    HasCompactSupport (symmetricShiftDefect t c f) := by
  have hp : HasCompactSupport (fun x => f (x + t)) := by
    simpa only [sub_neg_eq_add] using compact_shift hfs (-t)
  exact ((compact_shift hfs t).add hp).sub hfs.mul_left

private theorem cross_integrable {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfs : HasCompactSupport f) (x : ℝ) :
    Integrable (fun y => f y * conj (g (y - x))) :=
  (hf.mul (Complex.continuous_conj.comp
    (hg.comp (continuous_id.sub continuous_const)))).integrable_of_hasCompactSupport
      hfs.mul_right

private theorem weilTest_apply (f g : ℝ → ℂ) (x : ℝ) :
    weilTest f g x = ∫ y : ℝ, f y * conj (g (y - x)) := by
  simp only [weilTest, convolution_def, ContinuousLinearMap.mul_apply', tilde, neg_sub]

private theorem shifted_cross (f g : ℝ → ℂ) (t x : ℝ) :
    (∫ y : ℝ, f (y - t) * conj (g (y - x))) = weilTest f g (x - t) := by
  rw [weilTest_apply]
  calc
    _ = ∫ y : ℝ, (fun v => f v * conj (g (v - (x - t)))) (y - t) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [show y - t - (x - t) = y - x by ring]
    _ = _ := integral_sub_right_eq_self _ t

private theorem transfer_left {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfs : HasCompactSupport f)
    (t c x : ℝ) :
    weilTest (symmetricShiftDefect t c f) g x =
      weilTest f g (x - t) + weilTest f g (x + t) -
        (c : ℂ) * weilTest f g x := by
  have hm := cross_integrable (hf.comp (continuous_id.sub continuous_const)) hg
    (compact_shift hfs t) x
  have hp := cross_integrable (hf.comp (continuous_id.add continuous_const)) hg
    (by simpa only [sub_neg_eq_add] using compact_shift hfs (-t)) x
  have h0 := cross_integrable hf hg hfs x
  rw [weilTest_apply]
  have hexpand :
      (fun y => symmetricShiftDefect t c f y * conj (g (y - x))) =
      fun y => (f (y - t) * conj (g (y - x)) +
        f (y + t) * conj (g (y - x))) -
        (c : ℂ) * (f y * conj (g (y - x))) := by
    funext y
    dsimp [symmetricShiftDefect]
    ring
  rw [hexpand, integral_sub (hm.add hp) (h0.const_mul (c : ℂ)),
    integral_add hm hp, cintegral_const_mul, shifted_cross]
  have hp' := shifted_cross f g (-t) x
  simp only [sub_neg_eq_add] at hp'
  rw [hp', ← weilTest_apply]

private theorem transfer_right {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfs : HasCompactSupport f)
    (t c x : ℝ) :
    weilTest f (symmetricShiftDefect t c g) x =
      weilTest f g (x - t) + weilTest f g (x + t) -
        (c : ℂ) * weilTest f g x := by
  have hm := cross_integrable hf hg hfs (x - t)
  have hp := cross_integrable hf hg hfs (x + t)
  have h0 := cross_integrable hf hg hfs x
  rw [weilTest_apply]
  have hexpand :
      (fun y => f y * conj (symmetricShiftDefect t c g (y - x))) =
      fun y => (f y * conj (g (y - (x - t))) +
        f y * conj (g (y - (x + t)))) -
        (c : ℂ) * (f y * conj (g (y - x))) := by
    funext y
    dsimp [symmetricShiftDefect]
    rw [show y - x - t = y - (x + t) by ring,
      show y - x + t = y - (x - t) by ring]
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal]
    ring
  rw [hexpand, integral_sub (hm.add hp) (h0.const_mul (c : ℂ)),
    integral_add hm hp, cintegral_const_mul]
  rw [← weilTest_apply, ← weilTest_apply, ← weilTest_apply]

/-- The symmetric filter transfers through the genuine Weil correlation.
Applying `literatureRHS` preserves the finite prime terms, both poles, and the
Gamma term simultaneously. No zero-side formula or RH hypothesis is used. -/
theorem weil_symmetric_shift_transfer {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfs : HasCompactSupport f)
    (t c : ℝ) :
    weilTest (symmetricShiftDefect t c f) g =
      weilTest f (symmetricShiftDefect t c g) := by
  funext x
  rw [transfer_left hf hg hfs, transfer_right hf hg hfs]

private theorem backward_recurrence (u : ℕ → ℂ) (c : ℂ)
    (hrec : ∀ n, u n + u (n + 2) = c * u (n + 1)) :
    ∀ N, u N = 0 → u (N + 1) = 0 → u 0 = 0 := by
  intro N
  induction N with
  | zero => intro h _; exact h
  | succ N ih =>
      intro hN hN1
      have hN0 : u N = 0 := by
        have h := hrec N
        have hz1 : u (N + 1) = 0 := hN
        have hz2 : u (N + 2) = 0 := by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hN1
        simpa only [hz1, hz2, mul_zero, add_zero] using h
      exact ih hN0 hN

/-- A nonzero compactly supported function is never an eigenfunction of a
nontrivial symmetric translation. This makes the residual probe non-vacuous. -/
theorem symmetric_shift_defect_ne_zero {f : ℝ → ℂ}
    (hfs : HasCompactSupport f) (hf : f ≠ 0) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    symmetricShiftDefect t c f ≠ 0 := by
  intro hB
  apply hf
  funext x
  obtain ⟨C, hC⟩ := hfs.isCompact.isBounded.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt ((C - x) / t)
  have hNx : C < x + (N : ℝ) * t := by
    have h := (div_lt_iff₀ ht).mp hN
    linarith
  let u : ℕ → ℂ := fun n => f (x + (n : ℝ) * t)
  have hz (n : ℕ) (hn : N ≤ n) : u n = 0 := by
    change f (x + (n : ℝ) * t) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hle := hC hm
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmon := mul_le_mul_of_nonneg_right hcast ht.le
    linarith
  have hrec (n : ℕ) : u n + u (n + 2) = (c : ℂ) * u (n + 1) := by
    have h := congrFun hB (x + ((n + 1 : ℕ) : ℝ) * t)
    change f (x + ((n + 1 : ℕ) : ℝ) * t - t) +
      f (x + ((n + 1 : ℕ) : ℝ) * t + t) -
      (c : ℂ) * f (x + ((n + 1 : ℕ) : ℝ) * t) = 0 at h
    rw [show x + ((n + 1 : ℕ) : ℝ) * t - t = x + (n : ℝ) * t by
          push_cast; ring,
        show x + ((n + 1 : ℕ) : ℝ) * t + t = x + ((n + 2 : ℕ) : ℝ) * t by
          push_cast; ring] at h
    exact sub_eq_zero.mp h
  simpa [u] using backward_recurrence u (c : ℂ) hrec N (hz N le_rfl)
    (hz (N + 1) (Nat.le_succ N))

private theorem mass_integrable {f : ℝ → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    Integrable (fun x => Complex.normSq (f x)) :=
  (Complex.continuous_normSq.comp hf).integrable_of_hasCompactSupport
    (hfs.comp_left (by simp : Complex.normSq (0 : ℂ) = 0))

private theorem correlation_zero {f : ℝ → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    (weilTest f f 0).re = ∫ x : ℝ, Complex.normSq (f x) := by
  rw [weilTest_apply]
  simp only [sub_zero]
  have hi : Integrable (fun x => f x * conj (f x)) := by
    simpa only [sub_zero] using cross_integrable hf hf hfs 0
  rw [← integral_re hi]
  apply integral_congr_ae
  filter_upwards with x
  simp [Complex.mul_conj]

private theorem normSq_three (a b z : ℂ) (c : ℝ) :
    Complex.normSq (a + b - (c : ℂ) * z) ≤
      3 * (Complex.normSq a + Complex.normSq b + c ^ 2 * Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  nlinarith [sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im),
    sq_nonneg (a.re + c * z.re), sq_nonneg (a.im + c * z.im),
    sq_nonneg (b.re + c * z.re), sq_nonneg (b.im + c * z.im)]

private theorem mass_defect_le {f : ℝ → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (t c : ℝ) :
    (∫ x : ℝ, Complex.normSq (symmetricShiftDefect t c f x)) ≤
      3 * (2 + c ^ 2) * ∫ x : ℝ, Complex.normSq (f x) := by
  have h0 := mass_integrable hf hfs
  have hm := mass_integrable (hf.comp (continuous_id.sub continuous_const))
    (compact_shift hfs t)
  have hp := mass_integrable (hf.comp (continuous_id.add continuous_const))
    (by simpa only [sub_neg_eq_add] using compact_shift hfs (-t))
  have hb := mass_integrable (continuous_defect hf t c) (compact_defect hfs t c)
  calc
    _ ≤ ∫ x : ℝ, 3 * (Complex.normSq (f (x - t)) +
        Complex.normSq (f (x + t)) + c ^ 2 * Complex.normSq (f x)) := by
      apply integral_mono hb (((hm.add hp).add (h0.const_mul (c ^ 2))).const_mul 3)
      intro x
      exact normSq_three (f (x - t)) (f (x + t)) (f x) c
    _ = 3 * (2 + c ^ 2) * ∫ x : ℝ, Complex.normSq (f x) := by
      rw [integral_const_mul, integral_add (hm.add hp) (h0.const_mul (c ^ 2)),
        integral_add hm hp, integral_const_mul, integral_sub_right_eq_self,
        integral_add_right_eq_self]
      ring

/-- Necessary residual cost of a candidate complement gap, for the concrete
arithmetic Weil form. Set `v = B f`, `w = B v`. The first hypothesis is the gap
inequality tested on `v`; the second is the squared real directional residual
bound tested on `w`. For an operator residual of norm `r`, the latter follows
from Cauchy--Schwarz whenever `w` is an admissible test for that operator.

The conclusion is independent of scale and uses no positivity of the complete
Weil operator. It obstructs `r / delta -> 0` for interior candidate families
whose translated variance has a nonzero limit. -/
theorem weil_symmetric_shift_residual_barrier {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (t c mu delta r : ℝ) (hdelta : 0 ≤ delta)
    (hgap :
      (mu + delta) * (∫ x : ℝ, Complex.normSq (symmetricShiftDefect t c f x)) ≤
        (literatureRHS (weilTest (symmetricShiftDefect t c f)
          (symmetricShiftDefect t c f))).re)
    (hres :
      ((literatureRHS (weilTest f
          (symmetricShiftDefect t c (symmetricShiftDefect t c f))) -
        (mu : ℂ) * weilTest f
          (symmetricShiftDefect t c (symmetricShiftDefect t c f)) 0).re) ^ 2 ≤
        r ^ 2 * (∫ x : ℝ,
          Complex.normSq (symmetricShiftDefect t c (symmetricShiftDefect t c f) x))) :
    delta ^ 2 * (∫ x : ℝ, Complex.normSq (symmetricShiftDefect t c f x)) ≤
      3 * (2 + c ^ 2) * r ^ 2 := by
  let v := symmetricShiftDefect t c f
  let w := symmetricShiftDefect t c v
  let m : ℝ := ∫ x : ℝ, Complex.normSq (v x)
  let E : ℝ := (literatureRHS (weilTest v v)).re - mu * m
  have hc := hf.continuous
  have hv := continuous_defect hc t c
  have hvs := compact_defect hfs t c
  have htransfer : weilTest v v = weilTest f w :=
    weil_symmetric_shift_transfer hc hv hfs t c
  have hR : E ^ 2 ≤ r ^ 2 * (∫ x : ℝ, Complex.normSq (w x)) := by
    have he : (literatureRHS (weilTest f w) - (mu : ℂ) * weilTest f w 0).re = E := by
      rw [← htransfer]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rw [correlation_zero hv hvs]
    change (literatureRHS (weilTest f w) - (mu : ℂ) * weilTest f w 0).re ^ 2 ≤ _ at hres
    rwa [he] at hres
  have hm : 0 ≤ m := integral_nonneg (fun x => Complex.normSq_nonneg (v x))
  have hE : delta * m ≤ E := by
    change (mu + delta) * m ≤ (literatureRHS (weilTest v v)).re at hgap
    dsimp [E]
    nlinarith
  have hEnn : 0 ≤ E := (mul_nonneg hdelta hm).trans hE
  have hsquare : delta ^ 2 * m ^ 2 ≤ E ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hE)
      (add_nonneg hEnn (mul_nonneg hdelta hm))
    nlinarith
  have hw := mass_defect_le hv hvs t c
  have hbound : r ^ 2 * (∫ x : ℝ, Complex.normSq (w x)) ≤
      r ^ 2 * (3 * (2 + c ^ 2) * m) :=
    mul_le_mul_of_nonneg_left hw (sq_nonneg r)
  have hfinal := hsquare.trans (hR.trans hbound)
  by_cases hz : m = 0
  · change delta ^ 2 * m ≤ _
    rw [hz, mul_zero]
    positivity
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
    change delta ^ 2 * m ≤ _
    apply (mul_le_mul_right hmpos).mp
    calc
      delta ^ 2 * m * m = delta ^ 2 * m ^ 2 := by ring
      _ ≤ r ^ 2 * (3 * (2 + c ^ 2) * m) := hfinal
      _ = (3 * (2 + c ^ 2) * r ^ 2) * m := by ring

#print axioms weil_symmetric_shift_transfer
#print axioms symmetric_shift_defect_ne_zero
#print axioms weil_symmetric_shift_residual_barrier

end
end D5.S3.Weil.ZetaBridge.WeilGroundModeShiftBarrier
