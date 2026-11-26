/- GID: D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/McCormackZelinskyQuestion38
   mirror-E: none(waiver:explicit-divisor-family)
   anchors: [mathlib/module/Mathlib.Data.Finset.NatDivisors]
   utility: none
   digest: Every number sixty times a power of two is strongly pseudoperfect. -/

import D5.S3.Arith.Abundancy.StrongPseudoperfectDensity

/-! Complementary binary layers give divisor sets of sum twice the ambient number. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38

open StrongPseudoperfectDensity (StronglyPseudoperfect)

private def pairs (k : ℕ) : Finset (ℕ × ℕ) :=
  ({0, k + 5} ×ˢ {1, 15}) ∪ ({1, k + 4} ×ˢ {1, 3, 5, 15}) ∪
    (Ico 3 (k + 3) ×ˢ {3, 5})

private lemma pair_bounds {k i d : ℕ} (h : (i, d) ∈ pairs k) :
    i ≤ k + 5 ∧ d ∈ ({1, 3, 5, 15} : Finset ℕ) := by
  simp only [pairs, mem_union, mem_product, mem_insert, mem_singleton, mem_Ico] at h ⊢
  omega

private lemma pair_complement {k i d : ℕ} (h : (i, d) ∈ pairs k) :
    (k + 5 - i, 15 / d) ∈ pairs k := by
  have hd := (pair_bounds h).2
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    norm_num [pairs] at h ⊢ <;> omega

private lemma pair_divisors {k i d : ℕ} (h : (i, d) ∈ pairs k) :
    (2 ^ i, d) ∈ (2 ^ (k + 5)).divisors ×ˢ (15 : ℕ).divisors := by
  obtain ⟨hi, hd⟩ := pair_bounds h
  refine mem_product.mpr ⟨?_, ?_⟩
  · exact (Nat.mem_divisors_prime_pow Nat.prime_two _).mpr ⟨i, hi, rfl⟩
  · have h15 : (15 : ℕ).divisors = {1, 3, 5, 15} := by decide
    rwa [h15]

private lemma encode_injective (k : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => 2 ^ p.1 * p.2) ↑(pairs k) := by
  rintro ⟨i, d⟩ hp ⟨j, e⟩ hq he
  have hc : (2 ^ (k + 5)).Coprime 15 := (by decide : Nat.Coprime 2 15).pow_left _
  have hh := hc.mul_injOn_divisors (pair_divisors hp) (pair_divisors hq) he
  have hij : i = j := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (congrArg (fun x : ℕ × ℕ => x.1) hh)
  have hde : d = e := congrArg (fun x : ℕ × ℕ => x.2) hh
  exact Prod.ext hij hde

private def divisorSet (k : ℕ) : Finset ℕ :=
  (pairs k).image (fun p => 2 ^ p.1 * p.2)

private lemma divisorSet_subset (k : ℕ) :
    divisorSet k ⊆ (15 * 2 ^ (k + 5)).divisors := by
  intro x hx
  obtain ⟨⟨i, d⟩, hp, rfl⟩ := mem_image.mp hx
  obtain ⟨hi, hd⟩ := mem_product.mp (pair_divisors hp)
  apply Nat.mem_divisors.mpr
  refine ⟨?_, by positivity⟩
  simpa [mul_comm] using Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hi)
    (Nat.dvd_of_mem_divisors hd)

private lemma complement_formula {k i d : ℕ} (h : (i, d) ∈ pairs k) :
    15 * 2 ^ (k + 5) / (2 ^ i * d) = 2 ^ (k + 5 - i) * (15 / d) := by
  have hi := (pair_bounds h).1
  have hd := Nat.dvd_of_mem_divisors (mem_product.mp (pair_divisors h)).2
  have hm : (2 ^ i * d) * (2 ^ (k + 5 - i) * (15 / d)) =
      15 * 2 ^ (k + 5) := by
    calc
      _ = (2 ^ i * 2 ^ (k + 5 - i)) * (d * (15 / d)) := by ring
      _ = 15 * 2 ^ (k + 5) := by
        rw [← pow_add, Nat.add_sub_of_le hi, Nat.mul_div_cancel' hd, mul_comm]
  have hdpos := Nat.pos_of_mem_divisors (mem_product.mp (pair_divisors h)).2
  exact Nat.div_eq_of_eq_mul_left (by positivity) (by simpa [mul_comm] using hm.symm)

private lemma divisorSet_closed (k : ℕ) :
    ∀ x ∈ (15 * 2 ^ (k + 5)).divisors,
      x ∈ divisorSet k ↔ 15 * 2 ^ (k + 5) / x ∈ divisorSet k := by
  have hf : ∀ x ∈ divisorSet k, 15 * 2 ^ (k + 5) / x ∈ divisorSet k := by
    intro x hx
    obtain ⟨⟨i, d⟩, hp, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨(k + 5 - i, 15 / d), pair_complement hp,
      (complement_formula hp).symm⟩
  intro x hx
  refine ⟨hf x, fun h => ?_⟩
  have hh := hf _ h
  rwa [Nat.div_div_self (Nat.dvd_of_mem_divisors hx)
    (Nat.ne_zero_of_mem_divisors hx)] at hh

private lemma middle_sum (k : ℕ) :
    (∑ i ∈ Ico 3 (k + 3), 2 ^ i) + 8 = 2 ^ (k + 3) := by
  have h := geom_sum_Ico_mul (2 : ℤ) (show 3 ≤ k + 3 by omega)
  norm_num at h
  have h' : (∑ i ∈ Ico 3 (k + 3), (2 : ℤ) ^ i) + 8 = 2 ^ (k + 3) := by
    linarith
  exact_mod_cast h'

private lemma pair_sum (k : ℕ) :
    ∑ p ∈ pairs k, 2 ^ p.1 * p.2 = 30 * 2 ^ (k + 5) := by
  have hab : Disjoint ({0, k + 5} ×ˢ {1, 15} : Finset (ℕ × ℕ))
      ({1, k + 4} ×ˢ {1, 3, 5, 15}) := by
    apply disjoint_left.mpr
    intro p hp hq
    simp only [mem_product, mem_insert, mem_singleton] at hp hq
    omega
  have hc : Disjoint
      (({0, k + 5} ×ˢ {1, 15}) ∪ ({1, k + 4} ×ˢ {1, 3, 5, 15}) : Finset (ℕ × ℕ))
      (Ico 3 (k + 3) ×ˢ {3, 5}) := by
    apply disjoint_left.mpr
    intro p hp hq
    simp only [mem_union, mem_product, mem_insert, mem_singleton, mem_Ico] at hp hq
    omega
  have he : (∑ p ∈ pairs k, 2 ^ p.1 * p.2) =
      16 * (1 + 2 ^ (k + 5)) + 24 * (2 + 2 ^ (k + 4)) +
        8 * ∑ i ∈ Ico 3 (k + 3), 2 ^ i := by
    rw [pairs, sum_union hc, sum_union hab]
    simp [sum_product, ← mul_add, ← sum_mul]
    ring
  rw [he]
  have hm := middle_sum k
  have h4 : (2 : ℕ) ^ (k + 4) = 2 * 2 ^ (k + 3) := by
    rw [show k + 4 = (k + 3) + 1 by omega, pow_succ, mul_comm]
  have h5 : (2 : ℕ) ^ (k + 5) = 4 * 2 ^ (k + 3) := by
    rw [show k + 5 = (k + 3) + 2 by omega, pow_add]
    norm_num
    ring
  rw [h4, h5]
  omega

private lemma large_family (k : ℕ) : StronglyPseudoperfect (15 * 2 ^ (k + 5)) := by
  refine ⟨by positivity, divisorSet k, divisorSet_subset k, divisorSet_closed k, ?_⟩
  rw [divisorSet, sum_image (encode_injective k), pair_sum]
  ring

/-- Every sixty times a nonnegative integral power of two is strongly pseudoperfect. -/
theorem result : ∀ j : ℕ, StronglyPseudoperfect (60 * 2 ^ j) := by
  intro j
  rcases j with _ | _ | _ | j
  · refine ⟨by norm_num, (60 : ℕ).divisors \ {2, 30, 6, 10}, sdiff_subset, ?_, ?_⟩
    · decide
    · decide
  · refine ⟨by norm_num, (120 : ℕ).divisors \ {3, 40, 5, 24, 6, 20, 10, 12},
      sdiff_subset, ?_, ?_⟩
    · decide
    · decide
  · refine ⟨by norm_num, (240 : ℕ).divisors \ {2, 120, 4, 60, 6, 40, 12, 20},
      sdiff_subset, ?_, ?_⟩
    · decide
    · decide
  · convert large_family j using 1
    simp only [pow_succ]
    ring

end D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38
