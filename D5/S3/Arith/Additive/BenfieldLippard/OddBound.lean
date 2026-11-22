/- GID: D5/S3/Arith/Additive/BenfieldLippard/OddBound
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/BenfieldLippard/OddBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Small generators bound the number of gaps from above at odd exponents. -/

import D5.S3.Arith.Additive.BenfieldLippard.Stabilization
import D5.S3.Arith.Additive.BenfieldLippard.SmallGCD
import D5.S3.Arith.Additive.BenfieldLippard.Conductor

namespace BenfieldLippard

private theorem geometric_bound (n : ℕ) (hn : 8 ≤ n) : 2 * n * 2 ^ n < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    calc
      2 * (n + 1) * (2 ^ n * 2) = (2 * (n + 1) * 2) * 2 ^ n := by ring
      _ ≤ (2 * n * 3) * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * n * 2 ^ n) * 3 := by ring
      _ < 3 ^ n * 3 := Nat.mul_lt_mul_of_pos_right ih (by decide)

private theorem scaled_power_bound {p : ℕ} (hp : 193 ≤ p) :
    2 * (2 * (p / 3)) ^ p < p ^ (p - 1) := by
  have hb : (2 * (p / 3)) ^ p * 3 ^ p ≤ p ^ p * 2 ^ p := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (by omega) _
  have hpd : p ^ p = p ^ (p - 1) * p := by
    have h : p - 1 + 1 = p := by omega
    rw [← pow_succ, h]
  have hpow : 0 < p ^ (p - 1) := pow_pos (by omega) _
  have he : (2 * (2 * (p / 3)) ^ p) * 3 ^ p < p ^ (p - 1) * 3 ^ p := by
    calc
      _ = 2 * ((2 * (p / 3)) ^ p * 3 ^ p) := by ac_rfl
      _ ≤ 2 * (p ^ p * 2 ^ p) := Nat.mul_le_mul_left _ hb
      _ = p ^ (p - 1) * (2 * p * 2 ^ p) := by rw [hpd]; ac_rfl
      _ < _ := Nat.mul_lt_mul_of_pos_left (geometric_bound p (by omega)) hpow
  exact lt_of_not_ge fun h ↦ he.not_ge (Nat.mul_le_mul_right _ h)

theorem odd_upper (p k : ℕ) (hp : 193 ≤ p) (hk : 0 < k) (hkp : k ≤ p) (hodd : Odd k) :
    2 * (gaps k).ncard < p ^ (p - 1) := by
  let m := p / 3
  let A := 2 ^ k - 1
  let W := m ^ k - 1
  have hm : 2 ≤ m := by omega
  have hA : 0 < A := by
    have h : 2 ≤ 2 ^ k := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hk
    omega
  have hAS : A ∈ smallGenerators k m := ⟨2, ⟨by decide, hm⟩, rfl⟩
  have hW : ∀ s ∈ smallGenerators k m, s ≤ W := by
    rintro s ⟨a, ha, rfl⟩
    exact Nat.sub_le_sub_right (Nat.pow_le_pow_left ha.2 _) 1
  have hsub : smallGenerators k m ⊆ generators k := by
    rintro s ⟨a, ha, rfl⟩
    exact ⟨a, ha.1, rfl⟩
  have hconductor : ∀ n ≥ (A - 1) * W, n ∈ offsets k := fun n hn ↦
    AddSubmonoid.closure_mono hsub (bounded_conductor _ hA hAS hW (small_gcd p k hp hk hkp hodd) n hn)
  have hsubset : gaps k ⊆ (Finset.range ((A - 1) * W) : Set ℕ) := by
    intro n hn
    exact Finset.mem_range.mpr (lt_of_not_ge fun h ↦ hn.2 (hconductor n h))
  have hcard : (gaps k).ncard ≤ (A - 1) * W := by
    simpa only [Set.ncard_coe_finset, Finset.card_range] using Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
  have hsize : (A - 1) * W ≤ (2 * m) ^ k := by
    rw [mul_pow]
    exact Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
  have hexp : (2 * m) ^ k ≤ (2 * m) ^ p := Nat.pow_le_pow_right (by omega) hkp
  exact (Nat.mul_le_mul_left 2 (hcard.trans (hsize.trans hexp))).trans_lt (scaled_power_bound hp)

end BenfieldLippard
