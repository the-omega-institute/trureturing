/- GID: D5/S3/Analytic/KarpZhangGamma/Kernel
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangGamma/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup, mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer]
   utility: none
   digest: Reciprocal-gamma convolutions have a closed form and nonnegative total kernel. -/

import D5.S3.Analytic.KarpZhangGamma.Smoothing
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
admission_basis: escape-witness
content theorems: reciprocalGamma_sum, kernel_sum_nonneg.
escape_witness: binomialGamma_sum carries the exact rising-factorial
convolution invariant by induction in degree, simultaneously for all positive
parameters. The finite Pascal recurrence and Gamma recurrence yield the
invariant at the next degree. This is the finite Vandermonde recurrence
route to identity (3.11), without analytic series or integrals.
bind-only helper: gamma_balanced_shift -> kernel_sum_nonneg (Jensen applied
twice to Real.convexOn_log_Gamma); it is also consumed by
Result.reciprocalPair_balanced. binomialGamma_sum is content and consumed
by reciprocalGamma_sum; reciprocalGamma_sum is consumed by kernel_sum_nonneg.
Direct frozen D5 dependencies: none on the mathematical proof path; the
imported Smoothing identities are same-delivery helpers.
These general identities and inequalities are not computational-content
instances. The paired-kernel sign pattern is not asserted in this module.
-/

noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace D5.S3.Analytic.KarpZhangGamma.Kernel

open Smoothing

private theorem binomialGamma_sum (m : ℕ) : ∀ b c : ℝ, 0 < b → 0 < c →
    binomialProduct (fun k => 1 / Real.Gamma (b + k))
      (fun k => 1 / Real.Gamma (c + k)) m =
    (ascPochhammer ℝ m).eval (b + c + m - 1) /
      (Real.Gamma (b + m) * Real.Gamma (c + m)) := by
  induction m with
  | zero => intro b c _ _; simp [binomialProduct, one_div_mul_one_div]
  | succ m ih =>
    intro b c hb hc
    have hbf : (fun k : ℕ => 1 / Real.Gamma (b + (k + 1 : ℕ))) =
        (fun k : ℕ => 1 / Real.Gamma (b + 1 + k)) := by
      funext k
      have he : b + (k + 1 : ℕ) = b + 1 + (k : ℝ) := by push_cast; ring
      rw [he]
    have hcf : (fun k : ℕ => 1 / Real.Gamma (c + (k + 1 : ℕ))) =
        (fun k : ℕ => 1 / Real.Gamma (c + 1 + k)) := by
      funext k
      have he : c + (k + 1 : ℕ) = c + 1 + (k : ℝ) := by push_cast; ring
      rw [he]
    rw [binomialProduct_succ, hbf, hcf,
      ih (b + 1) c (by linarith) hc, ih b (c + 1) hb (by linarith)]
    have hbarg : b + 1 + (m : ℝ) = b + m + 1 := by ring
    have hcarg : c + 1 + (m : ℝ) = c + m + 1 := by ring
    have hnum1 : b + 1 + c + (m : ℝ) - 1 = b + c + m := by ring
    have hnum2 : b + (c + 1) + (m : ℝ) - 1 = b + c + m := by ring
    have hnum3 : b + c + (m + 1 : ℕ) - 1 = b + c + (m : ℝ) := by
      push_cast
      ring
    have hbm : 0 < b + (m : ℝ) := by positivity
    have hcm : 0 < c + (m : ℝ) := by positivity
    have hgb := ne_of_gt (Real.Gamma_pos_of_pos hbm)
    have hgc := ne_of_gt (Real.Gamma_pos_of_pos hcm)
    rw [hnum1, hnum2, hnum3, hbarg, hcarg]
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc, Real.Gamma_add_one (ne_of_gt hbm),
      Real.Gamma_add_one (ne_of_gt hcm), ascPochhammer_succ_eval]
    field_simp [hgb, hgc, ne_of_gt hbm, ne_of_gt hcm]
    <;> ring

/-- Identity (3.11), stated as a finite sum. The m=0 case needs no positivity
of the displayed Pochhammer argument. -/
theorem reciprocalGamma_sum (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (m : ℕ) :
    (∑ k ∈ range (m + 1),
      1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
        Real.Gamma (b + k) * Real.Gamma (c + (m - k)))) =
    (ascPochhammer ℝ m).eval (b + c + m - 1) /
      ((m.factorial : ℝ) * Real.Gamma (b + m) * Real.Gamma (c + m)) := by
  calc
    _ = productCoeff (fun k => 1 / Real.Gamma (b + k))
        (fun k => 1 / Real.Gamma (c + k)) m := by
      unfold productCoeff
      apply sum_congr rfl
      intro k _
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = _ := by
      rw [productCoeff_eq, binomialGamma_sum m b c hb hc]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem gamma_balanced_shift (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Real.Gamma (a + α) * Real.Gamma (a + β) ≤
      Real.Gamma a * Real.Gamma (a + α + β) := by
  by_cases hz : α + β = 0
  · have hαz : α = 0 := by linarith
    have hβz : β = 0 := by linarith
    simp [hαz, hβz]
  · have ht : 0 < α + β := lt_of_le_of_ne (add_nonneg hα hβ) (Ne.symm hz)
    have hw : β / (α + β) + α / (α + β) = 1 := by
      field_simp [ne_of_gt ht]
      <;> ring
    have hw' : α / (α + β) + β / (α + β) = 1 := by linarith
    have harg1 : β / (α + β) * a + α / (α + β) * (a + α + β) = a + α := by
      field_simp [ne_of_gt ht]
      <;> ring
    have harg2 : α / (α + β) * a + β / (α + β) * (a + α + β) = a + β := by
      field_simp [ne_of_gt ht]
      <;> ring
    have h1 := Real.convexOn_log_Gamma.2 (x := a) ha (y := a + α + β)
      (show 0 < a + α + β by linarith)
      (a := β / (α + β)) (b := α / (α + β))
      (div_nonneg hβ (le_of_lt ht)) (div_nonneg hα (le_of_lt ht)) hw
    have h2 := Real.convexOn_log_Gamma.2 (x := a) ha (y := a + α + β)
      (show 0 < a + α + β by linarith)
      (a := α / (α + β)) (b := β / (α + β))
      (div_nonneg hα (le_of_lt ht)) (div_nonneg hβ (le_of_lt ht)) hw'
    simp only [Function.comp_apply, smul_eq_mul] at h1 h2
    rw [harg1] at h1
    rw [harg2] at h2
    have hlog : Real.log (Real.Gamma (a + α)) + Real.log (Real.Gamma (a + β)) ≤
        Real.log (Real.Gamma a) + Real.log (Real.Gamma (a + α + β)) := by
      calc
        _ ≤ (β / (α + β) * Real.log (Real.Gamma a) +
              α / (α + β) * Real.log (Real.Gamma (a + α + β))) +
            (α / (α + β) * Real.log (Real.Gamma a) +
              β / (α + β) * Real.log (Real.Gamma (a + α + β))) := add_le_add h1 h2
        _ = (β / (α + β) + α / (α + β)) * Real.log (Real.Gamma a) +
              (α / (α + β) + β / (α + β)) *
                Real.log (Real.Gamma (a + α + β)) := by ring
        _ = _ := by rw [hw, hw', one_mul, one_mul]
    have hp := Real.Gamma_pos_of_pos ha
    have hpα := Real.Gamma_pos_of_pos (show 0 < a + α by linarith)
    have hpβ := Real.Gamma_pos_of_pos (show 0 < a + β by linarith)
    have hpαβ := Real.Gamma_pos_of_pos (show 0 < a + α + β by linarith)
    apply (Real.log_le_log_iff (mul_pos hpα hpβ) (mul_pos hp hpαβ)).mp
    rw [Real.log_mul (ne_of_gt hpα) (ne_of_gt hpβ),
      Real.log_mul (ne_of_gt hp) (ne_of_gt hpαβ)]
    exact hlog

/-- The unpaired reciprocal-gamma kernel M from (3.3). -/
def kernel (a α β : ℝ) (m k : ℕ) : ℝ :=
  (1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ))) *
    (1 / (Real.Gamma (a + α + k) * Real.Gamma (a + β + (m - k))) -
      1 / (Real.Gamma (a + k) * Real.Gamma (a + α + β + (m - k))))

/-- The total unpaired kernel is nonnegative for all nonnegative real shifts.
This is the weak sum assertion needed by the weighting principle; it does
not supply the separate one-sign-change hypothesis for the paired kernel. -/
theorem kernel_sum_nonneg (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (m : ℕ) :
    0 ≤ ∑ k ∈ range (m + 1), kernel a α β m k := by
  have hsum : (∑ k ∈ range (m + 1), kernel a α β m k) =
      (ascPochhammer ℝ m).eval (2 * a + α + β + m - 1) / (m.factorial : ℝ) *
        (1 / (Real.Gamma (a + α + m) * Real.Gamma (a + β + m)) -
          1 / (Real.Gamma (a + m) * Real.Gamma (a + α + β + m))) := by
    calc
      _ = (∑ k ∈ range (m + 1),
          1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
            Real.Gamma (a + α + k) * Real.Gamma (a + β + (m - k)))) -
          ∑ k ∈ range (m + 1),
            1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
              Real.Gamma (a + k) * Real.Gamma (a + α + β + (m - k))) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro k _
        simp only [kernel, div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
      _ = _ := by
        rw [reciprocalGamma_sum (a + α) (a + β) (by linarith) (by linarith) m,
          reciprocalGamma_sum a (a + α + β) ha (by linarith) m]
        rw [show (a + α) + (a + β) + (m : ℝ) - 1 =
            2 * a + α + β + m - 1 by ring,
          show a + (a + α + β) + (m : ℝ) - 1 =
            2 * a + α + β + m - 1 by ring]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hp : 0 ≤ (ascPochhammer ℝ m).eval (2 * a + α + β + m - 1) := by
    cases m with
    | zero => simp
    | succ n =>
      apply le_of_lt
      apply ascPochhammer_pos
      push_cast
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  have hbal := gamma_balanced_shift (a + m) α β (by positivity) hα hβ
  have harg1 : (a + (m : ℝ)) + α = a + α + m := by ring
  have harg2 : (a + (m : ℝ)) + β = a + β + m := by ring
  have harg3 : (a + (m : ℝ)) + α + β = a + α + β + m := by ring
  rw [harg1, harg2, harg3] at hbal
  have hden : 0 < Real.Gamma (a + α + m) * Real.Gamma (a + β + m) :=
    mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  rw [hsum]
  exact mul_nonneg (div_nonneg hp (by positivity))
    (sub_nonneg.mpr (one_div_le_one_div_of_le hden hbal))

end D5.S3.Analytic.KarpZhangGamma.Kernel
