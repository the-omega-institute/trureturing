/- GID: D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum
   generality: G
   mirror-B: D5/B/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   utility: none
   digest: The first Morken conjecture expresses the coprime Moebius sum as a divisor double sum. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The source sums use positive indices, inclusive endpoints and integer Moebius values. -/

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta

noncomputable section
namespace D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum

private theorem summand (d m : ℕ) :
    (if moebius d ≠ 0 ∧ m.Coprime d then moebius m else 0) =
      moebius (d * m) * moebius d := by
  classical
  by_cases hd : moebius d = 0
  · simp [hd]
  have hds := moebius_ne_zero_iff_squarefree.mp hd
  by_cases hc : m.Coprime d
  · rw [ite_eq_left ⟨hd, hc⟩, isMultiplicative_moebius.map_mul_of_coprime hc.symm]
    have hs := moebius_sq_eq_one_of_squarefree hds
    calc
      moebius m = moebius m * (moebius d ^ 2) := by rw [hs, mul_one]
      _ = _ := by ring
  · rw [ite_eq_right (by simp [hc])]
    have hns : ¬ Squarefree (d * m) := fun h => hc (Nat.coprime_of_squarefree_mul h).symm
    rw [moebius_eq_zero_of_not_squarefree hns, zero_mul]

private theorem reindex (n d : ℕ) (hd : 0 < d) :
    (∑ m ∈ Icc 1 (n / d), moebius (d * m) * moebius d) =
      ∑ k ∈ (Icc 1 n).filter (fun k => d ∣ k), moebius k * moebius d := by
  classical
  apply sum_bij (fun m _ => d * m)
  · intro m hm
    obtain ⟨hm1, hmn⟩ := mem_Icc.mp hm
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by exact Nat.mul_pos hd (by omega), ?_⟩, dvd_mul_right d m⟩
    have h := (Nat.le_div_iff_mul_le hd).mp hmn
    simpa [Nat.mul_comm] using h
  · intro a ha b hb h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro k hk
    obtain ⟨hk, hdk⟩ := mem_filter.mp hk
    obtain ⟨hk1, hkn⟩ := mem_Icc.mp hk
    refine ⟨k / d, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hkn⟩, Nat.mul_div_cancel' hdk⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdk) hd
  · intro m hm
    rfl

/-- The first conjectured identity in OEIS A112399, on every positive input. -/
theorem result (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ (Icc 1 n).filter (fun k => k.Coprime n), moebius k) =
      ∑ d ∈ n.divisors.filter (fun d => moebius d ≠ 0),
        ∑ m ∈ (Icc 1 (n / d)).filter (fun m => m.Coprime d), moebius m := by
  classical
  symm
  calc
    _ = ∑ d ∈ n.divisors, ∑ m ∈ Icc 1 (n / d),
          moebius (d * m) * moebius d := by
      rw [sum_filter]
      apply sum_congr rfl
      intro d hd
      by_cases hmu : moebius d ≠ 0
      · rw [ite_eq_left hmu, sum_filter]
        apply sum_congr rfl
        intro m hm
        simpa [hmu] using summand d m
      · simp [not_not.mp hmu]
    _ = ∑ d ∈ n.divisors,
          ∑ k ∈ (Icc 1 n).filter (fun k => d ∣ k), moebius k * moebius d := by
      apply sum_congr rfl
      intro d hd
      exact reindex n d (Nat.pos_of_mem_divisors hd)
    _ = ∑ k ∈ Icc 1 n, moebius k *
          (∑ d ∈ n.divisors.filter (fun d => d ∣ k), moebius d) := by
      simp only [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      by_cases h : d ∣ k <;> simp [h]
    _ = ∑ k ∈ (Icc 1 n).filter (fun k => k.Coprime n), moebius k := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k hk
      have hk0 : 0 < k := (mem_Icc.mp hk).1
      have hg0 : k.gcd n ≠ 0 := (Nat.gcd_pos_of_pos_left n hk0).ne'
      have hg : n.divisors.filter (fun d => d ∣ k) = (k.gcd n).divisors := by
        ext d
        simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdk⟩
          exact ⟨⟨hdk, hdn⟩, hg0⟩
        · rintro ⟨⟨hdk, hdn⟩, _⟩
          exact ⟨⟨hdn, hn.ne'⟩, hdk⟩
      rw [hg, ← ArithmeticFunction.coe_mul_zeta_apply,
        moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
      by_cases hc : k.Coprime n
      · simp [Nat.Coprime] at hc
        simp [hc]
      · have hgc : k.gcd n ≠ 1 := hc
        simp [hgc]

#print axioms result
end D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum
