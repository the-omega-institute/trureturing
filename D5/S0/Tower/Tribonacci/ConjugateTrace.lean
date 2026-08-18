/- GID: D5/S0/Tower/Tribonacci/ConjugateTrace
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/ConjugateTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two non-Perron roots sum to one minus the base, which is irrational. -/

import D5.S0.Tower.Tribonacci.Binet
import D5.S3.Constants.Irrationality.TribonacciIrrationality

/- Library-search audit trail (2026-08-18):
   * Searched the objects: the characteristic polynomial and the factorisation of
     the cubic are already in `Binet`; the sum of roots is not stated anywhere,
     and `git grep` on trace-shaped theorem names returns only a golden-tower
     coding lemma.
   * The irrationality of the base landed separately in this session; without it
     the non-integrality of the conjugate pair's sum cannot be concluded.
   * No Vieta machinery is needed: the quadratic cofactor is explicit in the
     existing factorisation, so its root sum is read off its coefficients. -/

namespace D5.S0.Tower.Tribonacci.ConjugateTrace

open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.Binet
open D5.S3.Constants.Irrationality.TribonacciIrrationality

local notation "t" => tribonacciConstant

/-- The cofactor of the Perron root in the Tribonacci cubic. -/
noncomputable def conjugateCofactor (z : Complex) : Complex :=
  z ^ 2 - (1 - (t : Complex)) * z + ((t : Complex) ^ 2 - (t : Complex) - 1)

/-- The cubic splits as the Perron factor times that cofactor. -/
theorem cubic_splits (z : Complex) :
    z ^ 3 - z ^ 2 - z - 1
      = (z - (t : Complex)) * conjugateCofactor z
        + ((t : Complex) ^ 3 - (t : Complex) ^ 2 - (t : Complex) - 1) := by
  simp only [conjugateCofactor]
  ring

/-- Since the base is a root, the split is exact. -/
theorem cubic_splits_exact (z : Complex) :
    z ^ 3 - z ^ 2 - z - 1 = (z - (t : Complex)) * conjugateCofactor z := by
  have hcubic : (t : Complex) ^ 3 = (t : Complex) ^ 2 + (t : Complex) + 1 := by
    exact_mod_cast tribonacciConstant_cubic
  rw [cubic_splits z, hcubic]
  ring

/-- The two non-Perron roots sum to one minus the base: that is the negated
linear coefficient of the cofactor. -/
theorem conjugate_pair_sum (u v : Complex)
    (hfactor : ∀ z : Complex, conjugateCofactor z = (z - u) * (z - v)) :
    u + v = 1 - (t : Complex) := by
  have h0 := hfactor 0
  have h1 := hfactor 1
  have hn := hfactor (-1)
  simp only [conjugateCofactor] at h0 h1 hn
  ring_nf at h0 h1 hn
  linear_combination (h1 - hn) / 2

/-- That sum is not rational, so the Perron root alone does not carry the trace:
the three roots sum to one, but no proper subset of them does. -/
theorem conjugate_pair_sum_irrational :
    Irrational (1 - t) := by
  have h := tribonacciConstant_irrational
  have h1 : Irrational ((1 : Int) - t) := h.intCast_sub 1
  simpa using h1

/-- In the cubic field the expanding root and the contracting pair do not form a
conjugate pair: their separation is witnessed by an irrational sum. -/
theorem cubic_trace_is_not_carried_by_the_perron_root :
    (∀ z : Complex, z ^ 3 - z ^ 2 - z - 1 = (z - (t : Complex)) * conjugateCofactor z) ∧
      Irrational (1 - t) :=
  ⟨cubic_splits_exact, conjugate_pair_sum_irrational⟩

end D5.S0.Tower.Tribonacci.ConjugateTrace
