/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedBalanceParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedBalanceParity
   mirror-E: none(waiver:matching-balance-parity)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: Paired symmetric offset colours on an odd circle force degree divisible by four. -/

import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedBalanceParity

open scoped BigOperators

/-- Pairing adjacent offsets and reversing the offset list force a fourfold degree. -/
theorem paired_offset_degree {m : ℕ} (hm : m % 2 = 0) (c : ℕ → ℕ)
    (hp : ∀ t < m, c (2 * t + 1) = c (2 * t + 2))
    (hs : ∀ d, 1 ≤ d → d ≤ 2 * m → c d = c (2 * m + 1 - d)) :
    4 ∣ ∑ d ∈ Finset.range (2 * m), c (d + 1) := by
  have pairs : ∀ u ≤ m,
      (∑ d ∈ Finset.range (2 * u), c (d + 1)) =
        2 * ∑ t ∈ Finset.range u, c (2 * t + 1) := by
    intro u
    induction u with
    | zero => simp
    | succ u ih =>
      intro hu
      have hu' : u < m := by omega
      have hu'' : u ≤ m := by omega
      rw [show 2 * (u + 1) = (2 * u + 1) + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih hu'']
      rw [Finset.sum_range_succ, ← hp u hu']
      omega
  obtain ⟨q, hq⟩ : ∃ q, m = 2 * q := ⟨m / 2, by omega⟩
  subst m
  have reverse : ∀ t < 2 * q,
      c (2 * t + 1) = c (2 * (2 * q - 1 - t) + 1) := by
    intro t ht
    have hr := hs (2 * t + 1) (by omega) (by omega)
    have hi : 2 * q - 1 - t < 2 * q := by omega
    rw [show 2 * (2 * q) + 1 - (2 * t + 1) =
      2 * (2 * q - 1 - t) + 2 by omega] at hr
    exact hr.trans (hp _ hi).symm
  have half : (∑ t ∈ Finset.range (2 * q), c (2 * t + 1)) =
      2 * ∑ t ∈ Finset.range q, c (2 * t + 1) := by
    rw [show 2 * q = q + q by omega, Finset.sum_range_add]
    have hr : (∑ i ∈ Finset.range q, c (2 * (q + i) + 1)) =
        ∑ i ∈ Finset.range q, c (2 * i + 1) := by
      calc
        _ = ∑ i ∈ Finset.range q, c (2 * (q - 1 - i) + 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' := Finset.mem_range.mp hi
          have hh := reverse (q + i) (by omega)
          simpa only [show 2 * q - 1 - (q + i) = q - 1 - i by omega] using hh
        _ = _ := Finset.sum_range_reflect (fun i => c (2 * i + 1)) q
    rw [hr]
    omega
  rw [pairs (2 * q) le_rfl, half]
  exact ⟨∑ t ∈ Finset.range q, c (2 * t + 1), by omega⟩

end D5.S3.Combinatorics.DihedralRamsey.NestedBalanceParity
