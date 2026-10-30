/- GID: D5/S3/Quantum/FockSpace/HigherOrderEPRTightness
   generality: I
   mirror-B: D5/B/S3/Quantum/FockSpace/HigherOrderEPRTightness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The nonnegative higher-order EPR bound is tight at every positive order. -/

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! Finite occupation-basis states for the tightness clause of (nS:2) in
Shchukin and van Loock, arXiv:1511.08444v1. The harmonic taper gives arbitrarily
small squared norms. No Gaussian or strict-positivity assertion is made. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.FockSpace.HigherOrderEPRTightness

open Finset

/-- Squared Hilbert norm in the two-mode occupation basis. -/
def normSq (ψ : ℕ × ℕ →₀ ℂ) : ℝ :=
  ψ.sum fun _ z => ‖z‖ ^ 2

/-- The power of the annihilation operator of the first mode. -/
def annihilateA (n : ℕ) : (ℕ × ℕ →₀ ℂ) →ₗ[ℂ] (ℕ × ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun p =>
    if n ≤ p.1 then Finsupp.single (p.1 - n, p.2)
      (Real.sqrt ((p.1.factorial : ℝ) / (p.1 - n).factorial) : ℂ) else 0

/-- The power of the creation operator of the second mode. -/
def createB (n : ℕ) : (ℕ × ℕ →₀ ℂ) →ₗ[ℂ] (ℕ × ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun p =>
    Finsupp.single (p.1, p.2 + n)
      (Real.sqrt (((p.2 + n).factorial : ℝ) / p.2.factorial) : ℂ)

/-- Tightness of the zero bound, for either sign and every positive order. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) →
    ∀ ε : ℝ, 0 < ε → ∃ ψ : ℕ × ℕ →₀ ℂ,
      normSq ψ = 1 ∧ normSq (annihilateA n ψ + σ • createB n ψ) < ε

private def taper (m k : ℕ) : ℝ := 1 - (harmonic k : ℝ) / harmonic m

private def coefficient (n k : ℕ) : ℝ :=
  Real.sqrt (((n * k).factorial : ℝ) / (n * k + n - 1).factorial)

private def vector (n : ℕ) (σ : ℂ) (m : ℕ) : ℕ × ℕ →₀ ℂ :=
  ∑ k ∈ range (m + 1), Finsupp.single (n * k + n - 1, n * k)
    ((-σ) ^ k * (taper m k * coefficient n k : ℝ))

private lemma taper_norm_bound (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    1 / ((n - 1).factorial : ℝ) ≤ normSq (vector n σ m) := by
  sorry

private lemma taper_energy (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    normSq (annihilateA n (vector n σ m) + σ • createB n (vector n σ m)) =
      (n : ℝ) / harmonic m := by
  sorry

private lemma harmonic_large (b : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ b < (harmonic m : ℝ) := by
  sorry

private lemma normalize (n : ℕ) (σ : ℂ) (v : ℕ × ℕ →₀ ℂ)
    (hv : 0 < normSq v) :
    ∃ ψ : ℕ × ℕ →₀ ℂ, normSq ψ = 1 ∧
      normSq (annihilateA n ψ + σ • createB n ψ) =
        normSq (annihilateA n v + σ • createB n v) / normSq v := by
  sorry

/-- Every positive order admits normalized finite states arbitrarily close to zero. -/
theorem result : claim := by
  intro n hn σ hσ ε hε
  obtain ⟨m, hm, hlarge⟩ := harmonic_large ((n.factorial : ℝ) / ε)
  have hp : 0 < ((n - 1).factorial : ℝ) := by positivity
  have hlow := taper_norm_bound n m hn hm σ hσ
  have hv : 0 < normSq (vector n σ m) := lt_of_lt_of_le (by positivity) hlow
  obtain ⟨ψ, hψ, he⟩ := normalize n σ (vector n σ m) hv
  refine ⟨ψ, hψ, ?_⟩
  rw [he, taper_energy n m hn hm σ hσ]
  have hfac : (n.factorial : ℝ) = n * ((n - 1).factorial : ℝ) := by
    have h := Nat.factorial_succ (n - 1)
    rw [Nat.sub_add_cancel hn] at h
    exact_mod_cast h
  have hh : 0 < (harmonic m : ℝ) := by
    have : 0 < (n.factorial : ℝ) / ε := by positivity
    linarith
  have hbound : (n : ℝ) / harmonic m / normSq (vector n σ m) ≤
      n.factorial / (harmonic m : ℝ) := by
    apply (div_le_iff₀ hv).2
    have h := mul_le_mul_of_nonneg_left hlow (show 0 ≤ (n : ℝ) / harmonic m by positivity)
    rw [hfac]
    nlinarith [mul_pos hp hh]
  exact hbound.trans_lt ((div_lt_iff₀ hh).2 ((div_lt_iff₀ hε).1 hlarge))

end D5.S3.Quantum.FockSpace.HigherOrderEPRTightness
