/- GID: D5/S3/Arith/Lattices/Klartag/State/RawDataInst
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/RawDataInst
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
import D5.S3.Arith.Lattices.Klartag.Construction.Section5
import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43Uniform

set_option linter.unusedSectionVars false

open MeasureTheory
open Finset
open scoped RealInnerProductSpace

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.RawDataInst

open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup

variable {n : ℕ}

/-- **The prime choice.**  `Section5.exists_prime_alpha_le` with the threshold chosen so that the
*product* `α·p` clears any prescribed `M`.  Everything `RawData` asks of `p` and `α` beyond the
lattice data reduces to a lower bound on `α·p`, because `(α·p)^n = κ_n·p`. -/
theorem exists_prime_alpha_mul (hn : 2 ≤ n) (M : ℝ) (hM : 1 ≤ M) :
    ∃ p : ℕ, Nat.Prime p ∧ ∃ α : ℝ, 0 < α ∧
      α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n ∧
      α ≤ 1 / (2 * (n : ℝ) * Real.sqrt n) ∧
      M ≤ α * (p : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hκ : 0 < kappa n := kappa_pos hn0
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  set ε : ℝ := min (kappa n / M ^ (n - 1)) (1 / (2 * (n : ℝ) * Real.sqrt n)) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨p, hp, α, hαpos, hαnorm, hαle⟩ := Section5.exists_prime_alpha_le hn hεpos
  refine ⟨p, hp, α, hαpos, hαnorm, le_trans hαle (min_le_right _ _), ?_⟩

  have hα1 : α ≤ kappa n / M ^ (n - 1) := le_trans hαle (min_le_left _ _)
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hαn : (0 : ℝ) < α ^ n := by positivity
  have hnorm' : α ^ n * (p : ℝ) ^ (n - 1) = kappa n := by
    rw [← hαnorm]; push_cast; ring
  have hpn : (p : ℝ) ^ (n - 1) = kappa n / α ^ n := by
    field_simp
    linarith [hnorm']
  have hMn : (0 : ℝ) < M ^ (n - 1) := by positivity
  have hstep : α ^ n ≤ (kappa n / M ^ (n - 1)) ^ n := pow_le_pow_left₀ hαpos.le hα1 n
  have hdiv : kappa n / (kappa n / M ^ (n - 1)) ^ n ≤ kappa n / α ^ n :=
    div_le_div_of_nonneg_left hκ.le hαn hstep
  have heq : kappa n / (kappa n / M ^ (n - 1)) ^ n = (M ^ n / kappa n) ^ (n - 1) := by
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul]
    rw [mul_comm (n - 1) n,
      show (kappa n) ^ n = kappa n ^ (n - 1) * kappa n by
        rw [← pow_succ]; congr 1; omega]
    field_simp
  have hb : (M ^ n / kappa n) ^ (n - 1) ≤ (p : ℝ) ^ (n - 1) := by
    rw [← heq, hpn]; exact hdiv
  have hn1 : n - 1 ≠ 0 := by omega
  have hn0' : n ≠ 0 := by omega
  have hp' : M ^ n / kappa n ≤ (p : ℝ) := le_of_pow_le_pow_left₀ hn1 hppos.le hb
  have hMnle : M ^ n ≤ kappa n * (p : ℝ) := by
    rw [div_le_iff₀ hκ] at hp'; linarith [hp']
  have hprod : (α * (p : ℝ)) ^ n = kappa n * (p : ℝ) := by
    rw [mul_pow, show n = (n - 1) + 1 by omega, pow_succ (p : ℝ) (n - 1)]
    rw [show (n - 1) + 1 = n by omega]
    calc α ^ n * ((p : ℝ) ^ (n - 1) * (p : ℝ))
        = (α ^ n * (p : ℝ) ^ (n - 1)) * (p : ℝ) := by ring
      _ = kappa n * (p : ℝ) := by rw [hnorm']
  exact le_of_pow_le_pow_left₀ hn0' (by positivity) (by rw [hprod]; exact hMnle)

end D5.S3.Arith.Lattices.Klartag.State.RawDataInst
