/- GID: D5/S3/Arith/Divisors/ErdosNicolas/DivisorBlocks
   generality: G
   mirror-B: none(waiver:symbolic-divisor-partition-used-by-kernel-criterion)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Prime-power divisor partitions and exact block cardinalities. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Removing one copy of the positive base from a positive power. -/
theorem prime_power_mul_div {p a m : ℕ} (hp : 0 < p) (ha : 0 < a) :
    (p ^ a * m) / p = p ^ (a - 1) * m := by
  have hpow : p ^ a * m = p * (p ^ (a - 1) * m) := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
  rw [hpow, Nat.mul_div_right _ hp]

/-- Inherited divisors and scaled divisors cover the full prime-power product. -/
theorem prime_power_divisors_partition {p a m : ℕ} (hp : p.Prime)
    (ha : 0 < a) :
    (p ^ a * m).divisors =
      m.divisors ∪ (p ^ (a - 1) * m).divisors.image (p * ·) := by
  by_cases hm : m = 0
  · simp [hm]
  have hn : p ^ a * m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm
  have hq : p ^ (a - 1) * m ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm
  have hpow : p ^ a * m = p * (p ^ (a - 1) * m) := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
  ext d
  simp only [mem_union, mem_image, Nat.mem_divisors]
  constructor
  · intro hd
    by_cases hpd : p ∣ d
    · right
      obtain ⟨e, rfl⟩ := hpd
      refine ⟨e, ⟨?_, hq⟩, rfl⟩
      rw [hpow] at hd
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hd.1
    · left
      refine ⟨?_, hm⟩
      exact (hp.coprime_pow_of_not_dvd hpd).dvd_of_dvd_mul_left hd.1
  · rintro (⟨hd, _⟩ | ⟨e, ⟨he, _⟩, rfl⟩)
    · exact ⟨hd.trans (dvd_mul_left m (p ^ a)), hn⟩
    · refine ⟨?_, hn⟩
      rw [hpow]
      exact Nat.mul_dvd_mul_left p he

/-- No divisor of the prime-free part belongs to the divisible block. -/
theorem prime_power_divisor_blocks_disjoint {p a m : ℕ} (hpm : ¬p ∣ m) :
    Disjoint m.divisors ((p ^ (a - 1) * m).divisors.image (p * ·)) := by
  apply Finset.disjoint_left.mpr
  intro d hd hb
  obtain ⟨e, _, rfl⟩ := mem_image.mp hb
  exact hpm ((dvd_mul_right p e).trans (Nat.dvd_of_mem_divisors hd))

/-- The familiar divisor-count product, with its prime-power factor evaluated. -/
theorem card_divisors_prime_power_mul {p m : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) (a : ℕ) :
    (p ^ a * m).divisors.card = (a + 1) * m.divisors.card := by
  rw [(hp.coprime_pow_of_not_dvd hpm).symm.card_divisors_mul,
    Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- Multiplication by a positive prime preserves the preceding block's size. -/
theorem prime_power_divisor_block_card {p a m : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hpm : ¬p ∣ m) :
    ((p ^ (a - 1) * m).divisors.image (p * ·)).card = a * m.divisors.card := by
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h),
    card_divisors_prime_power_mul hp hpm, Nat.sub_add_cancel ha]

#print axioms prime_power_mul_div
#print axioms prime_power_divisors_partition
#print axioms prime_power_divisor_blocks_disjoint
#print axioms card_divisors_prime_power_mul
#print axioms prime_power_divisor_block_card

end D5.S3.Arith.ErdosNicolas
