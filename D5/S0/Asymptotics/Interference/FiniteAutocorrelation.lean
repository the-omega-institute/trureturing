/- GID: D5/S0/Asymptotics/Interference/FiniteAutocorrelation
   generality: G
   mirror-B: D5/B/S0/Asymptotics/Interference/FiniteAutocorrelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: EDIT-ME -/

import Mathlib

open scoped BigOperators

namespace D5.S0.Asymptotics.Interference.FiniteAutocorrelation

noncomputable def finiteSignal {N : Nat} (f : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∑ n, f n * z ^ (n : Nat)

noncomputable def finiteAutocorrelation {N : Nat} (f : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∑ n, ∑ k, (f n * star (f k)) * (z ^ (n : Nat) * star (z ^ (k : Nat)))

/-- The squared modulus of a finite Fourier sum expands into its finite autocorrelation.

This is the exact finite identity in clause (甲) of the source bundle.  The
remaining diffraction, asymptotic, and zero-window clauses are intentionally
outside this partial closure.
-/
theorem finite_autocorrelation_normSq {N : Nat} (f : Fin N → ℂ) (z : ℂ) :
    (Complex.normSq (finiteSignal f z) : ℂ) = finiteAutocorrelation f z := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [finiteSignal, finiteAutocorrelation, map_sum, map_mul, map_pow, star_pow,
    starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ =>
    Finset.sum_congr rfl fun k _ => by ring

example : finiteSignal (N := 0) (fun i => (i : ℂ)) 1 = 0 := by
  simp [finiteSignal]

#print axioms finite_autocorrelation_normSq

end D5.S0.Asymptotics.Interference.FiniteAutocorrelation
