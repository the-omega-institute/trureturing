/- GID: D5/S3/Analytic/Polynomial/OrderedCrossingGap
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/OrderedCrossingGap
   mirror-E: none(waiver:symbolic-inequality)
   anchors: []
   utility: none
   digest: Polynomial gap for ordered crossing indices. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The polynomial estimate uses unit gaps between the ordered parameters wherever the
corresponding inequalities are strict. Schiavo's increasing-rate comparison uses
natural-number crossing indices and supplies these gaps after coercion to the reals.
-/

set_option autoImplicit false

namespace OrderedCrossingGap

/-- The ordered crossing expression is nonnegative under the two threshold bounds. -/
theorem gap_nonneg {a b K L B N k : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hk : 0 < k) (hkB : k ≤ B) (hBN : B ≤ N) (hNL : N ≤ L)
    (hgapB : B < L → B + 1 ≤ L) (hgapk : k < B → k + 1 ≤ B)
    (hgapN : N < L → N + 1 ≤ L)
    (hK : a * L * (L - 1) / 2 ≤ K)
    (hcross : K ≤ a * N * (N + 1) / 2 + (b - a) * k * (k + 1) / 2) :
    let σ := k * (N - B) - (B - k) * (L - N)
    0 ≤ (K - a * L * B / 2) * σ +
      a * L * B * (L - N) * (N - B) / 2 + L * B * k * (b - a) * (B - k) / 2 := by
  dsimp only
  let σ := k * (N - B) - (B - k) * (L - N)
  let X := a * L * B * (L - N) * (N - B) / 2
  let Y := L * B * k * (b - a) * (B - k) / 2
  change 0 ≤ (K - a * L * B / 2) * σ + X + Y
  have hB : 0 ≤ B := by linarith
  have hL : 0 ≤ L := by linarith
  have hN : 0 ≤ N := by linarith
  have hd₁ : 0 ≤ L - N := sub_nonneg.mpr hNL
  have hd₂ : 0 ≤ N - B := sub_nonneg.mpr hBN
  have hd₃ : 0 ≤ B - k := sub_nonneg.mpr hkB
  have hd₄ : 0 ≤ b - a := sub_nonneg.mpr hab
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  rcases (show B ≤ L by linarith).eq_or_lt with hBL | hBL
  · have hN' : N = L := by linarith
    have hσ : σ = 0 := by simp [σ, hBL, hN']
    rw [hσ, mul_zero, zero_add]
    exact add_nonneg hX hY
  have hKL : 0 ≤ K - a * L * B / 2 := by
    have hpos := mul_nonneg (mul_nonneg ha hL) (show 0 ≤ L - 1 - B by linarith [hgapB hBL])
    nlinarith only [hK, hpos]
  by_cases hσ : 0 ≤ σ
  · exact add_nonneg (add_nonneg (mul_nonneg hKL hσ) hX) hY
  have hprod : 0 < (B - k) * (L - N) := by
    have ht := mul_nonneg hk.le hd₂
    dsimp [σ] at hσ
    linarith
  have hk' : k < B := by
    by_contra! h
    have heq : B - k = 0 := by linarith
    simp [heq] at hprod
  have hN' : N < L := by
    by_contra! h
    have heq : L - N = 0 := by linarith
    simp [heq] at hprod
  let x₀ := a * L * (L - 1) / 2
  let M := L * B * (B - k)
  let A (x : ℝ) := (k + 1) * (x - a * L * B / 2) * σ +
    (k + 1) * X + M * (x - a * N * (N + 1) / 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hY' : M * (K - a * N * (N + 1) / 2) ≤ (k + 1) * Y := by
    have h := mul_le_mul_of_nonneg_left
      (show K - a * N * (N + 1) / 2 ≤ (b - a) * k * (k + 1) / 2 by linarith) hM
    dsimp only [M, Y] at h ⊢
    nlinarith only [h]
  have htop : A K ≤ (k + 1) * ((K - a * L * B / 2) * σ + X + Y) := by
    dsimp only [A]
    nlinarith only [hY']
  have hgap := hgapk hk'
  have hgap' := hgapN hN'
  have hfactor : 0 ≤ L * B - (k + 1) * (L - N) := by
    have h := mul_nonneg hL (show 0 ≤ B - (k + 1) by linarith)
    have h' := mul_nonneg (show 0 ≤ k + 1 by linarith) hN
    nlinarith only [h, h']
  have hslope : 0 ≤ (k + 1) * σ + M := by
    have hid : (k + 1) * σ + M =
        (k + 1) * k * (N - B) + (B - k) * (L * B - (k + 1) * (L - N)) := by
      dsimp only [σ, M]
      ring
    rw [hid]
    positivity
  have hmono : A x₀ ≤ A K := by
    have h := mul_nonneg (sub_nonneg.mpr hK) hslope
    change 0 ≤ (K - x₀) * ((k + 1) * σ + M) at h
    dsimp only [A]
    nlinarith only [h]
  have hbase : 0 ≤ A x₀ := by
    have hid : A x₀ = a * L / 2 *
        ((k + 1) * k * (N - B) * (2 * L - 1 - B - N) +
         (B - k) * (L - N - 1) * (B * (L + N) - (k + 1) * (L - N))) := by
      dsimp only [A, x₀, σ, X, M]
      ring
    have h₁ : 0 ≤ 2 * L - 1 - B - N := by linarith
    have h₂ : 0 ≤ L - N - 1 := by linarith
    have h₃ : 0 ≤ B * (L + N) - (k + 1) * (L - N) := by
      have h := mul_nonneg hB hN
      nlinarith only [hfactor, h]
    rw [hid]
    positivity
  exact nonneg_of_mul_nonneg_right (hbase.trans (hmono.trans htop)) (by linarith)

end OrderedCrossingGap
