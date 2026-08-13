/- GID: D5/S3/Weil/PrimeAddress/PrimeAddress
   generality: I
   mirror-B: D5/B/S3/Weil/PrimeAddress/PrimeAddress
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime deletion preserves zeta zeros and separates silent from loud addresses. -/

import D5.S3.Weil.EulerProduct
import D5.S3.Weil.ZeroSum
import D5.S3.Zeros.EulerWindows
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace D5.S3.Weil.PrimeAddress

open D5.S3.Weil.EulerProduct
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Zeros.EulerWindows

open scoped BigOperators

noncomputable section

/-- The zeta function after a finite collection of local Euler modifications. -/
noncomputable def finitePrimeModification (S : Finset ℕ) (s : ℂ) : ℂ :=
  classicalZeta s / finiteEulerProduct S s

/-- A finite collection of prime modifications preserves the global nontrivial zero set. -/
theorem finite_prime_modification_preserves_global_zero_set
    (S : Finset ℕ) (hPrime : ∀ p ∈ S, p.Prime) (s : ℂ) :
    IsNontrivialZero s ↔
      finitePrimeModification S s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hs
    refine ⟨?_, hs.2⟩
    exact div_eq_zero_iff.mpr (Or.inl hs.1)
  · intro hs
    have hwindow : finiteEulerProduct S s ≠ 0 :=
      finite_euler_window_ne_zero S hPrime hs.2.1
    refine ⟨?_, hs.2⟩
    simpa [finitePrimeModification, hwindow] using hs.1

/-- Deleting the prime-seven local factor is the `{7}` instance of finite modification. -/
theorem prime_seven_deletion_preserves_nontrivial_zeta_zeros
    (s : ℂ) :
    IsNontrivialZero s ↔
      finitePrimeModification {7} s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  apply finite_prime_modification_preserves_global_zero_set ({7} : Finset ℕ)
  · intro p hp
    simp only [Finset.mem_singleton.mp hp]
    exact Nat.prime_seven

/-- For a positive real base, the real part of a complex power is its cosine amplitude. -/
theorem zero_contribution_amplitude_x_beta_cos_gamma_log_x
    {x β γ : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re =
      x ^ β * Real.cos (γ * Real.log x) := by
  rw [Complex.cpow_def, if_neg (by exact_mod_cast hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  rw [Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    sub_zero, zero_mul]
  simp only [mul_zero, add_zero, zero_add, mul_one]
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring_nf

/-- A Dirichlet character vanishes at every prime dividing its modulus. -/
theorem dirichlet_l_functions_silence_ramified_primes
    {R : Type*} [CommMonoidWithZero R] {q : ℕ}
    (χ : DirichletCharacter R q)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ q) :
    χ (p : ZMod q) = 0 := by
  apply MulChar.map_nonunit χ
  rw [ZMod.isUnit_iff_coprime]
  intro hcop
  exact (hp.coprime_iff_not_dvd.mp hcop) hpq

/-- Every prime address is loud because its von Mangoldt reading is `log p > 0`. -/
theorem zeta_has_no_silent_prime_address
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    singleAddressReading (p ^ k) ≠ 0 := by
  rw [(single_address_reading_spec.1 p k hp hk)]
  exact (Real.log_pos (by exact_mod_cast hp.two_le)).ne'

example : Nonempty ℂ := ⟨0⟩
example : Nonempty (Finset ℕ) := ⟨∅⟩
example : ∃ S : Finset ℕ, S.Nonempty ∧ ∀ p ∈ S, p.Prime := by
  refine ⟨{7}, Finset.singleton_nonempty 7, ?_⟩
  simpa using Nat.prime_seven
example : ∃ x β γ : ℝ, 0 < x ∧ β = 0 ∧ γ = 0 :=
  ⟨1, 0, 0, zero_lt_one, rfl, rfl⟩
example : ∃ (χ : DirichletCharacter ℂ 2) (p : ℕ),
    χ = 1 ∧ p.Prime ∧ p ∣ 2 :=
  ⟨1, 2, rfl, Nat.prime_two, dvd_rfl⟩
example : ∃ p k : ℕ, p.Prime ∧ k ≠ 0 := ⟨2, 1, Nat.prime_two, one_ne_zero⟩

#print axioms finite_prime_modification_preserves_global_zero_set
#print axioms prime_seven_deletion_preserves_nontrivial_zeta_zeros
#print axioms zero_contribution_amplitude_x_beta_cos_gamma_log_x
#print axioms dirichlet_l_functions_silence_ramified_primes
#print axioms zeta_has_no_silent_prime_address

end

end D5.S3.Weil.PrimeAddress
