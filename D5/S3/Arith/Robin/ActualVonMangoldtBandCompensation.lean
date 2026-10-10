/- GID: D5/S3/Arith/Robin/ActualVonMangoldtBandCompensation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualVonMangoldtBandCompensation
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual finite von Mangoldt bands retain the cutoff atoms in the centered max-kernel response. -/

import D5.S3.Arith.Robin.QuotientIntegralBudget
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators Interval ArithmeticFunction

namespace D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation

open QuotientIntegralBudget (arithmeticPrefix prefix_as_finite_sum prefix_difference_finite)

def maxKernel (A t : ℝ) : ℝ := 1 / (max A t * Real.log (max A t))

def dilatedKernel (A c t : ℝ) : ℝ := c⁻¹ * maxKernel A (t / c)

def tangentKernel (A t : ℝ) : ℝ :=
  if t ≤ A then -(1 / (A * Real.log A)) else 1 / (t * (Real.log t) ^ 2)

def centeredKernel (A c t : ℝ) : ℝ :=
  dilatedKernel A c t - maxKernel A t - (c - 1) * tangentKernel A t

def plateau (A c : ℝ) : ℝ := (c - 1) ^ 2 / (c * A * Real.log A)

def smoothRemainder (c t : ℝ) : ℝ :=
  1 / (t * (Real.log t - Real.log c)) - 1 / (t * Real.log t) -
    (c - 1) / (t * (Real.log t) ^ 2)

def regularKernel (A c t : ℝ) : ℝ :=
  if t ≤ A then plateau A c else smoothRemainder c t

def residualKernel (A c t : ℝ) : ℝ := regularKernel A c t - centeredKernel A c t

def reciprocalLog (c t : ℝ) : ℝ := 1 / (t * Real.log (t / c))

def bandDerivative (c t : ℝ) : ℝ :=
  (Real.log (t / c) + 1) / (t ^ 2 * (Real.log (t / c)) ^ 2)

def bandLow (A c : ℝ) : ℝ := min A (c * A)
def bandHigh (A c : ℝ) : ℝ := max A (c * A)

/-- Literal right-closed finite arithmetic sum; no continuous replacement of Λ. -/
def weightedPrefix (f : ℝ → ℝ) (R : ℝ) : ℝ :=
  arithmeticPrefix (fun n => Λ n * f n) R

def actualCompensation (A c : ℝ) : ℝ := weightedPrefix (residualKernel A c) (bandHigh A c)

/-- The literal Lebesgue volume of the compact residual. -/
def bandVolume (A c : ℝ) : ℝ := ∫ t in (0 : ℝ)..bandHigh A c, residualKernel A c t

def discrepancy (t : ℝ) : ℝ := Chebyshev.psi t - t

def finiteResponse (A c R : ℝ) : ℝ :=
  weightedPrefix (centeredKernel A c) R - ∫ t in (0 : ℝ)..R, centeredKernel A c t

def smoothBoundary (A c R : ℝ) : ℝ :=
  (plateau A c - smoothRemainder c A) * discrepancy A +
    smoothRemainder c R * discrepancy R -
      ∫ t in A..R, discrepancy t * deriv (smoothRemainder c) t

def shortAllowance (A c H : ℝ) : ℝ :=
  (517 / 1000 : ℝ) * min (H ^ 2) (A ^ 2 * (c - 1) ^ 2) / (A ^ 2 * Real.log A)

def ThetaIncrementLower (X H ε : ℝ) : Prop :=
  ∀ u v : ℝ, X ≤ u → u < v → v ≤ 2 * X → H ≤ v - u →
    (1 - ε) * (v - u) ≤ Chebyshev.theta v - Chebyshev.theta u

private theorem prefix_eq_Ioc (k : ℕ → ℝ) (y : ℝ) :
    arithmeticPrefix k y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, k n := by
  rw [arithmeticPrefix, ← Finset.sum_Ico_eq_sum_range k 1 (⌊y⌋₊ + 1)]
  simp only [Nat.add_sub_cancel, Nat.Ico_add_one_add_one_eq_Ioc, zero_add]
  congr 1
  ext i
  congr 1
  omega

private theorem prefix_psi (t : ℝ) : arithmeticPrefix (fun n => Λ n) t = Chebyshev.psi t := by
  exact prefix_eq_Ioc _ _

private theorem theta_increment_le_psi {u v : ℝ} (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u ≤ Chebyshev.psi v - Chebyshev.psi u := by
  have h : Chebyshev.psi u - Chebyshev.theta u ≤ Chebyshev.psi v - Chebyshev.theta v := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Chebyshev.psi_sub_theta_eq_sum_not_prime]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
      exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono huv)⟩, hn.2⟩
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  linarith

private theorem actual_increment {u v : ℝ} {N : ℕ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hvN : v ≤ N) (hv : 0 < v) :
    Chebyshev.psi v - Chebyshev.psi u =
      ∑ i ∈ Finset.range N, if u < ((i + 1 : ℕ) : ℝ) ∧ ((i + 1 : ℕ) : ℝ) ≤ v
        then Λ (i + 1) else 0 := by
  have h := prefix_difference_finite (fun n => Λ n) (N := N) (c := u / v) (y := v)
    hv.le (by simpa [div_mul_cancel₀ _ hv.ne'] using hu)
    (by simpa [div_mul_cancel₀ _ hv.ne'] using huv) hvN
  simpa only [div_mul_cancel₀ _ hv.ne', prefix_psi] using h

private theorem reciprocalLog_deriv {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hz : Real.log (t / c) ≠ 0) :
    HasDerivAt (reciprocalLog c) (-bandDerivative c t) t := by
  have hl := (Real.hasDerivAt_log (div_ne_zero ht.ne' hc.ne')).comp t
    ((hasDerivAt_id t).div_const c)
  have h := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).mul hl)
    (mul_ne_zero ht.ne' hz)
  convert h using 1 <;> simp only [reciprocalLog, bandDerivative, id_eq, one_mul, zero_mul,
    zero_sub, neg_div]
  field_simp
  <;> ring

end D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
