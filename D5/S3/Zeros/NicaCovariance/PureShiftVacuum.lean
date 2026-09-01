/- GID: D5/S3/Zeros/NicaCovariance/PureShiftVacuum
   generality: I
   mirror-B: D5/B/S3/Zeros/NicaCovariance/PureShiftVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the pure arithmetic shift tail and the Euler-sieve vacuum. -/

import D5.S3.Zeros.ShiftOperators.BackwardShiftAdjoint
import Mathlib.Data.PNat.Prime

namespace D5.S3.Zeros.NicaCovariance.PureShiftVacuum

open D5.S1.Digit
open D5.S3.Weil.SpectralHilbert
open D5.S3.Zeros.ShiftOperators.BackwardShiftAdjoint

noncomputable local instance : DecidableEq PrimeAxisTable := Classical.decEq _

/-- The multiplicative identity, viewed as the vacuum prime-axis address. -/
noncomputable def vacuumAddress : PrimeAxisTable :=
  primeAxisEncoding.symm 1

@[simp]
theorem encoding_vacuumAddress : primeAxisEncoding vacuumAddress = 1 :=
  Equiv.apply_symm_apply _ _

/-- The `n`-fold normalized sum of an address with itself. -/
noncomputable def tablePow (u : PrimeAxisTable) (n : ℕ) : PrimeAxisTable :=
  primeAxisEncoding.symm (primeAxisEncoding u ^ n)

@[simp]
theorem encoding_tablePow (u : PrimeAxisTable) (n : ℕ) :
    primeAxisEncoding (tablePow u n) = primeAxisEncoding u ^ n :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem tablePow_zero (u : PrimeAxisTable) : tablePow u 0 = vacuumAddress := by
  apply primeAxisEncoding.injective
  simp

theorem tablePow_succ (u : PrimeAxisTable) (n : ℕ) :
    tablePow u (n + 1) = normalizedTableAdd (tablePow u n) u := by
  apply primeAxisEncoding.injective
  simp [normalizedTableAdd, pow_succ]

/-- A nontrivial arithmetic translation has no unitary tail: the intersection of the
subspaces supported on all powers of its address is zero. -/
theorem iInf_divisibleSubspace_tablePow_eq_bot {u : PrimeAxisTable}
    (hu : u ≠ vacuumAddress) :
    (⨅ n : ℕ, divisibleSubspace (tablePow u n)) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    apply lp.ext
    funext b
    have huEncoding : primeAxisEncoding u ≠ 1 := by
      intro h
      apply hu
      apply primeAxisEncoding.injective
      simpa using h
    let A : ℕ := ((primeAxisEncoding u : ℕ+) : ℕ)
    let B : ℕ := ((primeAxisEncoding b : ℕ+) : ℕ)
    have hAone : A ≠ 1 := by
      intro h
      apply huEncoding
      apply Subtype.ext
      exact h
    have hApos : 0 < A := (primeAxisEncoding u).pos
    have hAle : 1 ≤ A := hApos
    have hBpos : 0 < B := (primeAxisEncoding b).pos
    have hxPow : x ∈ divisibleSubspace (tablePow u (B + 1)) :=
      (Submodule.mem_iInf _).1 hx (B + 1)
    apply (mem_divisibleSubspace.1 hxPow) b
    intro hdvd
    have hdvdNat : A ^ (B + 1) ∣ B := by
      simpa [A, B, PNat.dvd_iff] using hdvd
    have hpowLe : A ^ (B + 1) ≤ B := Nat.le_of_dvd hBpos hdvdNat
    have hmulLe : A * (B + 1) ≤ A ^ (B + 1) := Nat.mul_le_pow hAone (B + 1)
    have hsuccLe : B + 1 ≤ A * (B + 1) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (B + 1) hAle
    omega
  · exact bot_le

/-- The ket at the multiplicative identity address. -/
noncomputable def vacuumKet : ZetaHilbertSpace :=
  lp.single 2 vacuumAddress (1 : ℂ)

/-- The prime address corresponding to a bundled natural prime. -/
noncomputable def primeAddress (p : Nat.Primes) : PrimeAxisTable :=
  primeAxisEncoding.symm ⟨(p : ℕ), p.2.pos⟩

@[simp]
theorem encoding_primeAddress (p : Nat.Primes) :
    primeAxisEncoding (primeAddress p) = ⟨(p : ℕ), p.2.pos⟩ :=
  Equiv.apply_symm_apply _ _

/-- Euler sieving leaves exactly the one-dimensional vacuum line. -/
theorem iInf_orthogonal_divisibleSubspace_primeAddress_eq_vacuum :
    (⨅ p : Nat.Primes, (divisibleSubspace (primeAddress p))ᗮ) = ℂ ∙ vacuumKet := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_span_singleton]
    refine ⟨x vacuumAddress, ?_⟩
    apply lp.ext
    funext b
    by_cases hb : b = vacuumAddress
    · subst b
      simp [vacuumKet]
    · have hbEncoding : primeAxisEncoding b ≠ 1 := by
        intro h
        apply hb
        apply primeAxisEncoding.injective
        simpa using h
      have hbNat : ((primeAxisEncoding b : ℕ+) : ℕ) ≠ 1 := by
        intro h
        apply hbEncoding
        apply Subtype.ext
        exact h
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hbNat
      let q : Nat.Primes := ⟨p, hp⟩
      have hxq : x ∈ (divisibleSubspace (primeAddress q))ᗮ :=
        (Submodule.mem_iInf _).1 hx q
      have hzero : x b = 0 :=
        (mem_orthogonal_divisibleSubspace (primeAddress q) x).1 hxq b (by
          rw [encoding_primeAddress]
          exact (PNat.dvd_iff).2 hpdvd)
      rw [hzero]
      simp [vacuumKet, hb]
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    refine (Submodule.mem_iInf _).2 ?_
    intro p
    rw [mem_orthogonal_divisibleSubspace]
    intro b hpb
    have hbne : b ≠ vacuumAddress := by
      intro hb
      subst b
      have hpdvdOne : (p : ℕ) ∣ 1 := by
        rw [encoding_primeAddress, encoding_vacuumAddress] at hpb
        exact (PNat.dvd_iff).1 hpb
      exact p.2.not_dvd_one hpdvdOne
    simp [vacuumKet, hbne]

#print axioms iInf_divisibleSubspace_tablePow_eq_bot
#print axioms iInf_orthogonal_divisibleSubspace_primeAddress_eq_vacuum

end D5.S3.Zeros.NicaCovariance.PureShiftVacuum
