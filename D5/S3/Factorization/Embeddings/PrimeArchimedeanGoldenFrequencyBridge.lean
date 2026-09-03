/- GID: D5/S3/Factorization/Embeddings/PrimeArchimedeanGoldenFrequencyBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A diagonal p-adic log defect recovers the first golden prime frequency. -/

import D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyBridge
import D5.S3.Factorization.Embeddings.RationalPadicProductFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Embeddings.PrimeArchimedeanGoldenFrequencyBridge

open D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyBridge
open D5.S3.Midline.GoldenHeatSpectrum

local instance (prime : Nat.Primes) : Fact prime.1.Prime := ⟨prime.2⟩

/-- The logarithmic defect seen at one finite prime place when observing a
prime target. -/
def finitePlaceLogDefect (place target : Nat.Primes) : ℝ :=
  -Real.log (((padicNorm place.1 (target.1 : ℚ) : ℚ) : ℝ))

/-- A prime has norm `1 / p` at its own finite place. -/
theorem own_place_padic_norm (prime : Nat.Primes) :
    padicNorm prime.1 (prime.1 : ℚ) = (prime.1 : ℚ)⁻¹ := by
  simpa using (padicNorm.padicNorm_p_of_prime (p := prime.1))

/-- A different prime is a unit at the selected finite place. -/
theorem off_place_padic_norm
    (place target : Nat.Primes) (hne : place ≠ target) :
    padicNorm place.1 (target.1 : ℚ) = 1 := by
  have hneNat : place.1 ≠ target.1 := by
    intro hvalue
    exact hne (Subtype.ext hvalue)
  simpa using
    (padicNorm.padicNorm_of_prime_of_ne
      (p := place.1) (q := target.1) hneNat)

/-- Taking the logarithm of the own-place norm recovers the Archimedean
prime scale `log p`. -/
theorem finite_place_log_defect_self (prime : Nat.Primes) :
    finitePlaceLogDefect prime prime = Real.log (prime : ℝ) := by
  rw [finitePlaceLogDefect, own_place_padic_norm]
  push_cast
  rw [Real.log_inv]
  ring

/-- Every off-diagonal prime place contributes zero logarithmic defect. -/
theorem finite_place_log_defect_off_diagonal
    (place target : Nat.Primes) (hne : place ≠ target) :
    finitePlaceLogDefect place target = 0 := by
  rw [finitePlaceLogDefect, off_place_padic_norm place target hne]
  norm_num

/-- Golden modulation of the finite-place logarithmic defect. -/
def goldenFinitePlaceFrequency (place target : Nat.Primes) : ℝ :=
  Real.goldenRatio ^ 2 * finitePlaceLogDefect place target

/-- On the diagonal, the finite-place compensation is exactly the frozen
first excited golden frequency. -/
theorem golden_finite_place_frequency_self (prime : Nat.Primes) :
    goldenFinitePlaceFrequency prime prime = goldenSpectrum (prime, 0) := by
  rw [goldenFinitePlaceFrequency, finite_place_log_defect_self,
    first_excited_prime_frequency]

/-- Off the diagonal, the finite-place golden frequency vanishes. -/
theorem golden_finite_place_frequency_off_diagonal
    (place target : Nat.Primes) (hne : place ≠ target) :
    goldenFinitePlaceFrequency place target = 0 := by
  rw [goldenFinitePlaceFrequency,
    finite_place_log_defect_off_diagonal place target hne, mul_zero]

/-- The full diagonal valuation-frequency profile of a target prime. -/
def goldenFinitePlaceProfile (target : Nat.Primes) : Nat.Primes → ℝ :=
  fun place => goldenFinitePlaceFrequency place target

/-- The diagonal finite-place profile is prime-faithful. -/
theorem golden_finite_place_profile_injective :
    Function.Injective goldenFinitePlaceProfile := by
  intro first second hprofile
  by_contra hne
  have hcoordinate := congrFun hprofile first
  change goldenFinitePlaceFrequency first first =
    goldenFinitePlaceFrequency first second at hcoordinate
  rw [golden_finite_place_frequency_self,
    golden_finite_place_frequency_off_diagonal first second hne] at hcoordinate
  have hpositive : 0 < goldenSpectrum (first, 0) := by
    rw [first_excited_prime_frequency]
    exact mul_pos (sq_pos_of_pos Real.goldenRatio_pos)
      (Real.log_pos (by exact_mod_cast first.prop.one_lt))
  exact (ne_of_gt hpositive) hcoordinate

#print axioms own_place_padic_norm
#print axioms off_place_padic_norm
#print axioms finite_place_log_defect_self
#print axioms finite_place_log_defect_off_diagonal
#print axioms golden_finite_place_frequency_self
#print axioms golden_finite_place_frequency_off_diagonal
#print axioms golden_finite_place_profile_injective

end D5.S3.Factorization.Embeddings.PrimeArchimedeanGoldenFrequencyBridge
