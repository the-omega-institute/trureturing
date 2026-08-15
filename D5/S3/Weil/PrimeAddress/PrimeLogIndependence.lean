/- GID: D5/S3/Weil/PrimeAddress/PrimeLogIndependence
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeAddress/PrimeLogIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime logarithms admit no nontrivial finite rational linear relation. -/

import D5.S3.Factorization.PrimeLogIndependence

namespace D5.S3.Weil.PrimeAddress.PrimeLogIndependence

open scoped BigOperators

theorem prime_log_integer_independence :
    LinearIndependent ℤ (fun p : Nat.Primes => Real.log p) := by
  rw [linearIndependent_iff']
  intro s g hsum p hp
  let embedding : Nat.Primes ↪ ℕ :=
    ⟨fun q => q, fun _ _ h => Subtype.ext h⟩
  let S : Finset ℕ := s.map embedding
  let k : ℕ → ℤ := fun n => if hn : n.Prime then g ⟨n, hn⟩ else 0
  have hk (q : Nat.Primes) : k (embedding q) = g q := by
    change (if hn : (q : ℕ).Prime then g ⟨(q : ℕ), hn⟩ else 0) = g q
    rw [dif_pos q.prop]
    congr 1
  have hS : ∀ n ∈ S, n.Prime := by
    intro n hn
    change n ∈ s.map embedding at hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hn
    exact q.prop
  have hsum' : ∑ n ∈ S, (k n : ℝ) * Real.log n = 0 := by
    change ∑ n ∈ s.map embedding, (k n : ℝ) * Real.log n = 0
    rw [Finset.sum_map]
    calc
      ∑ q ∈ s, (k (embedding q) : ℝ) * Real.log (embedding q) =
          ∑ q ∈ s, (g q : ℝ) * Real.log q := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [hk]
            rfl
      _ = 0 := by simpa only [zsmul_eq_mul] using hsum
  have hzero :=
    D5.S3.Factorization.PrimeLogIndependence.prime_log_indep S k hS hsum'
      (p : ℕ) (by exact Finset.mem_map.mpr ⟨p, hp, rfl⟩)
  have hkp := hk p
  change k (p : ℕ) = g p at hkp
  rw [hkp] at hzero
  exact hzero

theorem prime_log_rational_independence :
    LinearIndependent ℚ (fun p : Nat.Primes => Real.log p) := by
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
  exact prime_log_integer_independence

theorem log_two_log_three_relation_eq_zero (a b : ℚ)
    (h : a • Real.log 2 + b • Real.log 3 = 0) : a = 0 ∧ b = 0 := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p3 : Nat.Primes := ⟨3, Nat.prime_three⟩
  have hp_ne : p2 ≠ p3 := by
    intro hp
    have := congrArg (fun p : Nat.Primes => (p : ℕ)) hp
    norm_num [p2, p3] at this
  have hp_ne' : p3 ≠ p2 := Ne.symm hp_ne
  let c : Nat.Primes → ℚ := fun p => if p = p2 then a else if p = p3 then b else 0
  have hc : ∑ p ∈ ({p2, p3} : Finset Nat.Primes), c p • Real.log p = 0 := by
    rw [Finset.sum_insert (by simpa using hp_ne), Finset.sum_singleton]
    simp only [c, if_pos, hp_ne', if_false]
    change a • Real.log 2 + b • Real.log 3 = 0
    exact h
  have hcoeff :=
    linearIndependent_iff'.mp prime_log_rational_independence
      ({p2, p3} : Finset Nat.Primes) c hc
  constructor
  · simpa [c] using hcoeff p2 (by simp)
  · simpa [c, hp_ne, hp_ne'] using hcoeff p3 (by simp)

theorem log_two_sub_log_three_ne_zero :
    (1 : ℚ) • Real.log 2 + (-1 : ℚ) • Real.log 3 ≠ 0 := by
  intro h
  have hcoeff := log_two_log_three_relation_eq_zero 1 (-1) h
  norm_num at hcoeff

example : ∃ a b : ℚ, a • Real.log 2 + b • Real.log 3 = 0 := ⟨0, 0, by simp⟩

example : Nonempty Nat.Primes := ⟨⟨2, Nat.prime_two⟩⟩

#print axioms prime_log_integer_independence
#print axioms prime_log_rational_independence
#print axioms log_two_log_three_relation_eq_zero
#print axioms log_two_sub_log_three_ne_zero

end D5.S3.Weil.PrimeAddress.PrimeLogIndependence
