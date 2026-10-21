/- GID: D5/S3/Arith/InterlaceFan/Cyclotomic
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Cyclotomic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.NumberTheory.Cyclotomic.Basic]
   utility: none
   digest: Cosine evaluation, order-class propagation, and Ramanujan witnesses for the interlace fan. -/

import D5.S3.Arith.InterlaceFan.Defs
import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Cyclotomic.Basic

noncomputable section

open Finset
open scoped BigOperators Nat Real

namespace D5.S3.Arith.InterlaceFan.Cyclotomic

open D5.S3.Arith.InterlaceFan.Defs
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

/- The real evaluation of the palindromic Fourier polynomial at the j-th
   root.  Writing it as a real sum keeps the sigma-coordinate convention
   explicit and avoids a hidden choice of the middle coefficient. -/
def evalCos (n j : ℕ) (x : Fin (n / 2) → ℝ) : ℝ :=
  ∑ k : Fin (n / 2), 2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k

/- The factor two in `evalCos` is the pair of reciprocal monomials; `I` is
   the negative half of this real evaluation. -/
theorem I_eq_eval (n j : ℕ) (x : Fin (n / 2) → ℝ) :
    I n j x = -(1 / 2 : ℝ) * evalCos n j x := by
  simp only [I, evalCos]
  change (∑ k : Fin (n / 2),
      -Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k) =
    (-(1 / 2 : ℝ)) • ∑ k : Fin (n / 2),
      2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k
  rw [Finset.smul_sum (s := (Finset.univ : Finset (Fin (n / 2))))]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/- A rational polynomial evaluation which is invariant on an order class
   gives the corresponding equality of interlace functionals.  The
   `hconj` premise is the cyclotomic conjugacy step: for a rational
   polynomial it is supplied by the minimal-polynomial argument. -/
theorem const_on_orderClass (n d : ℕ) (x : Fin (n / 2) → ℝ) (c : ℝ)
    (s : ℕ) (hs : s ∈ orderClass n d) (hcs : I n s x = c)
    (hconj : ∀ s t, s ∈ orderClass n d → t ∈ orderClass n d →
      evalCos n s x = evalCos n t x) :
    ∀ t ∈ orderClass n d, I n t x = c := by
  intro t ht
  have hsI := hcs
  have heval := hconj s t hs ht
  rw [I_eq_eval] at hsI ⊢
  calc
    -(1 / 2 : ℝ) * evalCos n t x = -(1 / 2 : ℝ) * evalCos n s x := by rw [heval]
    _ = c := hsI

/- Rational target values for the Fourier inversion witness.  The target is
   the value prescribed by the Ramanujan order-class indicator. -/
def witnessValue (n d j : ℕ) : ℚ :=
  (-(1 : ℚ) / 2) *
    ((n : ℚ) * (if j ∈ orderClass n d then 1 else 0) - Nat.totient d)

/- The divisor-indicator identity is the Ramanujan-sum witness used below.
   It is paired with rational target values for the Fourier inversion step. -/
theorem witness (d n : ℕ) (_hd : 0 < d) :
    ((if d ∣ n then (1 : ℂ) else 0) =
      (d : ℂ)⁻¹ * ∑ q ∈ d.divisors, ramanujanSum q n) ∧
      ∃ y : Fin (n / 2 + 1) → ℚ,
        ∀ j, y j = witnessValue n d (j : ℕ) := by
  constructor
  · exact divisorIndicator_eq_normalized_sum_ramanujanSum d n _hd
  · exact ⟨fun j => witnessValue n d (j : ℕ), by intro j; rfl⟩

theorem witness_values (n d : ℕ) (hd : 0 < d) :
    ∃ y : Fin (n / 2 + 1) → ℚ,
      ∀ j, y j = witnessValue n d j := by
  exact (witness d n hd).2

end D5.S3.Arith.InterlaceFan.Cyclotomic
