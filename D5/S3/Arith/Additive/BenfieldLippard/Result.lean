/- GID: D5/S3/Arith/Additive/BenfieldLippard/Result
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/BenfieldLippard/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Benfield–Lippard Conjecture 10.5 on the sizes of stable exception sets. -/

import D5.S3.Arith.Additive.BenfieldLippard.EvenBound
import D5.S3.Arith.Additive.BenfieldLippard.OddBound
import Mathlib.Data.Nat.Prime.Infinite

open scoped BigOperators

namespace BenfieldLippard

private theorem prime_peak {p : ℕ} (hp : p.Prime) (hp193 : 193 ≤ p) :
    (gaps (p - 2)).ncard < (gaps (p - 1)).ncard ∧
      (gaps p).ncard < (gaps (p - 1)).ncard := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hodd' : Odd (p - 2) := by
    obtain ⟨a, ha⟩ := hodd
    exact ⟨a - 1, by omega⟩
  have lower := even_lower hp (by omega)
  have left := odd_upper p (p - 2) hp193 (by omega) (by omega) hodd'
  have right := odd_upper p p hp193 (by omega) le_rfl hodd
  omega

/-- Benfield–Lippard, arXiv:2404.08193v2, Conjecture 10.5.
The finite sets are the eventual positive missing offsets for exact-length positive sums. -/
theorem conjecture_10_5 :
    ∃ B : ℕ → Set ℕ,
      (∀ k : ℕ, 2 ≤ k → (B k).Finite ∧
        ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
          B k = {s : ℕ | 0 < s ∧
            ¬ (∃ f : Fin j → ℕ, (∀ i, 0 < f i) ∧ j + s = ∑ i, f i ^ k)}) ∧
      ∀ N : ℕ, 2 ≤ N →
        (∃ r : ℕ, N ≤ r ∧ (B r).ncard < (B (r + 1)).ncard) ∧
        (∃ d : ℕ, N ≤ d ∧ (B (d + 1)).ncard < (B d).ncard) := by
  refine ⟨gaps, ?_, ?_⟩
  · intro k hk
    obtain ⟨hfin, J, hJ, hstab⟩ := stabilization k hk
    exact ⟨hfin, J, hJ, fun j hj ↦ (hstab j hj).symm⟩
  · intro N _
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max 193 (N + 2))
    have h193 : 193 ≤ p := (le_max_left _ _).trans hp
    have hN : N + 2 ≤ p := (le_max_right _ _).trans hp
    obtain ⟨rise, fall⟩ := prime_peak hprime h193
    have rise_adjacent : p - 2 + 1 = p - 1 := by omega
    have fall_adjacent : p - 1 + 1 = p := by omega
    exact ⟨⟨p - 2, by omega, by simpa only [rise_adjacent] using rise⟩,
      ⟨p - 1, by omega, by simpa only [fall_adjacent] using fall⟩⟩

end BenfieldLippard
