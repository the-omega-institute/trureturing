/- GID: D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/TerminalRatio
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6c
import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43UniformR2

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.TerminalRatio

open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.Section5

variable {a₀ α : ℝ} {n : ℕ}

/-- **`ThetaTight.n_mul_pow_mul_C1c` at `KcR`.**  `C1cR` differs from `C1c` only by `Kc → KcR`, so
the same identity holds and the combination is again α-free. -/
theorem n_mul_pow_mul_C1cR (ha : α ≠ 0) (hn : n ≠ 0) :
    (n : ℝ) * α ^ n * Lemma43R.C1cR a₀ α n
      = (α * rhoC a₀ α n) ^ n / 2 + Real.exp (1 / 2) * Lemma43R.KcR := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hpow : α ^ n ≠ 0 := pow_ne_zero n ha
  rw [Lemma43R.C1cR, mul_pow]
  field_simp

/-- `(α·ρ)ⁿ ≤ 1` at `a₀ = a0C n`: `√(a0C n) = (1 − 1/n)⁻¹`, so `α·ρ ≤ 1 − 3/(4n) < 1`. -/
theorem alpha_mul_rhoC_pow_le (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    (α * rhoC (a0C n) α n) ^ n ≤ 1 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have hsq : Real.sqrt (a0C n) = (1 - 1 / (n : ℝ))⁻¹ := by
    rw [a0C, show ((1 - 1 / (n : ℝ))⁻¹) ^ 2 = ((1 - 1 / (n : ℝ))⁻¹) ^ 2 from rfl,
      Real.sqrt_sq (by positivity)]
  have hle := ThetaTight.alpha_mul_rhoC_le (a₀ := a0C n) (ne_of_gt hα) (by omega) hdef
  rw [hsq, inv_inv] at hle
  have h1 : α * rhoC (a0C n) α n ≤ 1 := by
    have h4 : 1 / (4 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hn0]; linarith
    linarith
  have h0 : 0 ≤ α * rhoC (a0C n) α n :=
    mul_nonneg hα.le (rhoC_nonneg hα)
  exact pow_le_one₀ h0 h1

/-- **The terminal threshold is `Θ(n²)` with an absolute constant.**  `b` is the coefficient the
combined weight gives the terminal summand (`b = 1` for the bare radial bound, `b = 4` once
`ChainRaw3.tailT`'s own factor is counted). -/
theorem thetaTight_terminal_le {p : ℕ} {b : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hb : 0 ≤ b)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n)
    (hKcR : Real.exp (1 / 2) * Lemma43R.KcR ≤ 826) :
    ThetaTight.thetaTight p n (b * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2))
      ≤ 4 * b * 827 * (n : ℝ) ^ 2 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hd : (0 : ℝ) < (p : ℝ) ^ n - 1 := by linarith
  have hid := n_mul_pow_mul_C1cR (a₀ := a0C n) (ne_of_gt hα) (by omega : n ≠ 0)
  have hpw := alpha_mul_rhoC_pow_le hn hα hdef
  have hcomb : (n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n ≤ 827 := by
    rw [hid]; linarith
  have hcomb0 : 0 ≤ (n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n := by
    have : 0 ≤ Lemma43R.C1cR (a0C n) α n := Lemma43R.C1cR_nonneg hα
    positivity

  have hfac : ((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ n - 1 := by
    have hnn : n - 1 + 1 = n := by omega
    have hsplit : ((p ^ (n - 1) : ℕ) : ℝ) * (p : ℝ) = (p : ℝ) ^ n := by
      push_cast
      rw [← pow_succ, hnn]
    nlinarith [hpn, hsplit]
  have hkey : ThetaTight.thetaTight p n (b * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2))
      = (4 * b * (n : ℝ) ^ 2 * ((n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n))
        * ((((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ)) / ((p : ℝ) ^ n - 1)) := by
    rw [ThetaTight.thetaTight, ← halpha]
    field_simp
  rw [hkey]
  have hratio : (((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ)) / ((p : ℝ) ^ n - 1) ≤ 1 := by
    rw [div_le_one hd]; exact hfac
  have hratio0 : 0 ≤ (((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ)) / ((p : ℝ) ^ n - 1) := by
    apply div_nonneg _ hd.le
    have : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    positivity
  have hA0 : 0 ≤ 4 * b * (n : ℝ) ^ 2 * ((n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n) := by
    positivity
  have hA : 4 * b * (n : ℝ) ^ 2 * ((n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n)
      ≤ 4 * b * 827 * (n : ℝ) ^ 2 := by nlinarith [hcomb, hb, sq_nonneg ((n : ℝ))]
  nlinarith [hA, hA0, hratio, hratio0]

end D5.S3.Arith.Lattices.Klartag.Completion.TerminalRatio
