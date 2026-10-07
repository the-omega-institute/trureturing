/- GID: D5/S3/Arith/Lattices/PureCubicExponentResidues
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicExponentResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime exponents split a positive radicand into coprime squarefree cubic residues. -/

import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicExponentResidues

/-- Cubic division of every prime exponent yields a canonical cube part
and two disjoint squarefree residue factors. -/
theorem pure_cubic_exponent_residues (B : ℕ) (hB : 0 < B) :
    ∃ c m n : ℕ,
      0 < c ∧ 0 < m ∧ 0 < n ∧ Squarefree m ∧ Squarefree n ∧
      m.Coprime n ∧ B = c ^ 3 * m * n ^ 2 ∧
      (∀ p, c.factorization p = B.factorization p / 3) ∧
      (∀ p, m.factorization p = if B.factorization p % 3 = 1 then 1 else 0) ∧
      (∀ p, n.factorization p = if B.factorization p % 3 = 2 then 1 else 0) ∧
      (∀ p, (B / c ^ 3).factorization p < 3) ∧
      UniqueFactorizationMonoid.radical (B / c ^ 3) = m * n ∧
      (∀ c' m' n' : ℕ, 0 < c' → 0 < m' → 0 < n' →
        (∀ p, c'.factorization p = B.factorization p / 3) →
        (∀ p, m'.factorization p =
          if B.factorization p % 3 = 1 then 1 else 0) →
        (∀ p, n'.factorization p =
          if B.factorization p % 3 = 2 then 1 else 0) →
        c' = c ∧ m' = m ∧ n' = n) := by
  let c := Nat.floorRoot 3 B
  let fm : ℕ →₀ ℕ := B.factorization.mapRange
    (fun e => if e % 3 = 1 then 1 else 0) (by decide)
  let fn : ℕ →₀ ℕ := B.factorization.mapRange
    (fun e => if e % 3 = 2 then 1 else 0) (by decide)
  let m := fm.prod (fun p e => p ^ e)
  let n := fn.prod (fun p e => p ^ e)
  have hfmle : fm ≤ B.factorization := fun p => by
    change (if B.factorization p % 3 = 1 then 1 else 0) ≤ B.factorization p
    split_ifs with h <;> omega
  have hfnle : fn ≤ B.factorization := fun p => by
    change (if B.factorization p % 3 = 2 then 1 else 0) ≤ B.factorization p
    split_ifs with h <;> omega
  have hc0 : c ≠ 0 := (Nat.floorRoot_ne_zero).mpr ⟨by decide, hB.ne'⟩
  have hmdiv : m ∣ B := Nat.prod_pow_dvd_of_le_factorization hfmle
  have hndiv : n ∣ B := Nat.prod_pow_dvd_of_le_factorization hfnle
  have hm0 : m ≠ 0 := by
    intro hz
    exact hB.ne' ((zero_dvd_iff.mp (hz ▸ hmdiv)))
  have hn0 : n ≠ 0 := by
    intro hz
    exact hB.ne' ((zero_dvd_iff.mp (hz ▸ hndiv)))
  have hcf (p : ℕ) : c.factorization p = B.factorization p / 3 := by
    simp [c, Nat.factorization_floorRoot, Finsupp.floorDiv_apply]
  have hmf (p : ℕ) : m.factorization p =
      if B.factorization p % 3 = 1 then 1 else 0 := by
    rw [show m.factorization = fm from
      Nat.factorization_prod_pow_eq_self_of_le_factorization hfmle]
    rfl
  have hnf (p : ℕ) : n.factorization p =
      if B.factorization p % 3 = 2 then 1 else 0 := by
    rw [show n.factorization = fn from
      Nat.factorization_prod_pow_eq_self_of_le_factorization hfnle]
    rfl
  have hmsq : Squarefree m := by
    apply Nat.squarefree_of_factorization_le_one hm0
    intro p
    rw [hmf]
    split_ifs <;> omega
  have hnsq : Squarefree n := by
    apply Nat.squarefree_of_factorization_le_one hn0
    intro p
    rw [hnf]
    split_ifs <;> omega
  have hcop : m.Coprime n := by
    by_contra h
    obtain ⟨p, hp, hpm, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hp1 := (hp.dvd_iff_one_le_factorization hm0).mp hpm
    have hp2 := (hp.dvd_iff_one_le_factorization hn0).mp hpn
    rw [hmf] at hp1
    rw [hnf] at hp2
    by_cases h1 : B.factorization p % 3 = 1
    · have h2 : B.factorization p % 3 ≠ 2 := by omega
      simp [h1] at hp2
    · simp [h1] at hp1
  have hprod0 : c ^ 3 * m * n ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc0) hm0) (pow_ne_zero _ hn0)
  have hprod : B = c ^ 3 * m * n ^ 2 := by
    apply Nat.eq_of_factorization_eq hB.ne' hprod0
    intro p
    rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ hc0) hm0)
      (pow_ne_zero _ hn0), Nat.factorization_mul (pow_ne_zero _ hc0) hm0,
      Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, hcf, hmf, hnf]
    have hr := Nat.mod_lt (B.factorization p) (by decide : 0 < 3)
    by_cases h1 : B.factorization p % 3 = 1
    · have h2 : B.factorization p % 3 ≠ 2 := by omega
      simp [h1]
      omega
    · by_cases h2 : B.factorization p % 3 = 2
      · simp [h2]
        omega
      · have h0 : B.factorization p % 3 = 0 := by omega
        simp [h0]
        omega
  have hquot : B / c ^ 3 = m * n ^ 2 := by
    rw [hprod]
    rw [mul_assoc, Nat.mul_div_cancel_left _ (pow_pos (Nat.pos_of_ne_zero hc0) _)]
  have hcube (p : ℕ) : (B / c ^ 3).factorization p < 3 := by
    rw [hquot, Nat.factorization_mul hm0 (pow_ne_zero _ hn0),
      Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, hmf, hnf]
    by_cases h1 : B.factorization p % 3 = 1
    · have h2 : B.factorization p % 3 ≠ 2 := by omega
      simp [h1]
    · by_cases h2 : B.factorization p % 3 = 2
      · simp [h2]
      · simp [h1, h2]
  have hradm : UniqueFactorizationMonoid.radical m = m := by
    rw [Nat.radical_eq_prod_primeFactors]
    exact Nat.prod_primeFactors_of_squarefree hmsq
  have hradn : UniqueFactorizationMonoid.radical n = n := by
    rw [Nat.radical_eq_prod_primeFactors]
    exact Nat.prod_primeFactors_of_squarefree hnsq
  refine ⟨c, m, n, Nat.pos_of_ne_zero hc0, Nat.pos_of_ne_zero hm0,
    Nat.pos_of_ne_zero hn0, hmsq, hnsq, hcop, hprod, hcf, hmf, hnf,
    hcube, ?_, ?_⟩
  · rw [hquot, UniqueFactorizationMonoid.radical_mul
      (Nat.coprime_iff_isRelPrime.mp (hcop.pow_right 2)),
      UniqueFactorizationMonoid.radical_pow n (by decide), hradm, hradn]
  · intro c' m' n' hc' hm' hn' hcf' hmf' hnf'
    refine ⟨?_, ?_, ?_⟩
    · apply Nat.eq_of_factorization_eq hc'.ne' hc0
      intro p
      exact (hcf' p).trans (hcf p).symm
    · apply Nat.eq_of_factorization_eq hm'.ne' hm0
      intro p
      exact (hmf' p).trans (hmf p).symm
    · apply Nat.eq_of_factorization_eq hn'.ne' hn0
      intro p
      exact (hnf' p).trans (hnf p).symm

#print axioms pure_cubic_exponent_residues

end D5.S3.Arith.Lattices.PureCubicExponentResidues
