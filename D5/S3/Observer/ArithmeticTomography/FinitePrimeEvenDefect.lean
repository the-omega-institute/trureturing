/- GID: D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonempty finite prime layers detect nonzero offsets by a positive even cosh defect. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository digest and statement-shape searches found no finite prime cosh
     defect whose unique zero is the mirror offset zero.
   * `CriticalDampingFlatness` is an unweighted centered finite-type criterion;
     it does not instantiate to the positive reciprocal-prime weights here.
   * Pinned Mathlib hits `Real.rpow_def_of_pos`, `Real.one_le_cosh`,
     `Real.one_lt_cosh`, and `Finset.sum_pos'` are applied directly below.
   * Loogle confirmed the exact `Real.one_lt_cosh` signature. A LeanSearch HTTP
     query for the complete finite-sum shape returned status 405. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Observer.ArithmeticTomography.FinitePrimeEvenDefect

/-- The symmetric mean of the positive and negative real prime powers is the
hyperbolic cosine of the logarithmic offset. -/
theorem prime_mirror_mean_eq_cosh (p : Nat.Primes) (delta : Real) :
    (((p.1 : Real) ^ delta + (p.1 : Real) ^ (-delta)) / 2) =
      Real.cosh (delta * Real.log (p.1 : Real)) := by
  have hp : 0 < (p.1 : Real) := by exact_mod_cast p.2.pos
  rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp, Real.cosh_eq]
  congr 2 <;> ring_nf

/-- The finite even defect over a selected prime layer. -/
noncomputable def finitePrimeEvenDefect
    (primes : Finset Nat.Primes) (delta : Real) : Real :=
  2 * ∑ p ∈ primes,
    (Real.cosh (delta * Real.log (p.1 : Real)) - 1) / (p.1 : Real)

/-- Every reciprocal-prime contribution to the even defect is nonnegative. -/
theorem prime_even_defect_term_nonneg (p : Nat.Primes) (delta : Real) :
    0 <= (Real.cosh (delta * Real.log (p.1 : Real)) - 1) / (p.1 : Real) := by
  have hp : 0 <= (p.1 : Real) := by exact_mod_cast p.2.pos.le
  exact div_nonneg (sub_nonneg.mpr (Real.one_le_cosh _)) hp

/-- On a nonempty finite prime layer, every nonzero mirror offset has strictly
positive even defect. -/
theorem finite_prime_even_defect_pos
    (primes : Finset Nat.Primes) (hprimes : primes.Nonempty)
    (delta : Real) (hdelta : delta ≠ 0) :
    0 < finitePrimeEvenDefect primes delta := by
  obtain ⟨p, hp⟩ := hprimes
  have hpReal : 0 < (p.1 : Real) := by exact_mod_cast p.2.pos
  have hpOne : (1 : Real) < (p.1 : Real) := by exact_mod_cast p.2.one_lt
  have hlog : Real.log (p.1 : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos hpOne)
  have hargument : delta * Real.log (p.1 : Real) ≠ 0 :=
    mul_ne_zero hdelta hlog
  have hterm :
      0 < (Real.cosh (delta * Real.log (p.1 : Real)) - 1) / (p.1 : Real) :=
    div_pos (sub_pos.mpr (Real.one_lt_cosh.mpr hargument)) hpReal
  have hsum :
      0 < ∑ q ∈ primes,
        (Real.cosh (delta * Real.log (q.1 : Real)) - 1) / (q.1 : Real) := by
    exact Finset.sum_pos'
      (fun q _ => prime_even_defect_term_nonneg q delta) ⟨p, hp, hterm⟩
  exact mul_pos (by norm_num) hsum

/-- A nonempty finite prime layer has zero even defect exactly at zero offset. -/
theorem finite_prime_even_defect_eq_zero_iff
    (primes : Finset Nat.Primes) (hprimes : primes.Nonempty) (delta : Real) :
    finitePrimeEvenDefect primes delta = 0 ↔ delta = 0 := by
  constructor
  · intro hzero
    by_contra hdelta
    exact (finite_prime_even_defect_pos primes hprimes delta hdelta).ne' hzero
  · rintro rfl
    simp [finitePrimeEvenDefect]

private def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The domain of nonempty finite prime layers is inhabited. -/
example : ({primeTwo} : Finset Nat.Primes).Nonempty := Finset.singleton_nonempty _

/-- The zero-offset case witnesses the theorem's hypotheses and conclusion. -/
example :
    finitePrimeEvenDefect ({primeTwo} : Finset Nat.Primes) 0 = 0 ↔ (0 : Real) = 0 :=
  finite_prime_even_defect_eq_zero_iff
    {primeTwo} (Finset.singleton_nonempty primeTwo) 0

#print axioms prime_mirror_mean_eq_cosh
#print axioms prime_even_defect_term_nonneg
#print axioms finite_prime_even_defect_pos
#print axioms finite_prime_even_defect_eq_zero_iff

end D5.S3.Observer.ArithmeticTomography.FinitePrimeEvenDefect
