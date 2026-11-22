/- GID: D5/S3/Arith/Additive/Waring/WaringSymm
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringSymm.lean#L1-L169
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

import D5.S3.Arith.Additive.Waring.WaringLemma6
import D5.S3.Arith.Additive.Waring.WaringLemma3

open Finset

namespace Waring

/-- ℤ 上的 `[1,K]` 求和等于 ℕ 上的 `[1,K]` 求和。 -/
theorem sum_int_Icc_eq_sum_nat_Icc (K : ℕ) (f : ℕ → ℚ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), f n.natAbs) = ∑ m ∈ Finset.Icc 1 K, f m := by
  refine Finset.sum_bij (fun n _ => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    constructor
    · rw [Int.le_toNat (by linarith [hn.1])]
      exact_mod_cast hn.1
    · rw [Int.toNat_le]
      exact hn.2
  · intro n hn n' hn' heq
    rw [Finset.mem_Icc] at hn hn'
    have h1 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by linarith [hn.1])
    have h2 : (n'.toNat : ℤ) = n' := Int.toNat_of_nonneg (by linarith [hn'.1])
    rw [← h1, ← h2, heq]
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨(m : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · exact_mod_cast hm.1
      · exact_mod_cast hm.2
    · exact Int.toNat_natCast m
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have h0 : (0 : ℤ) ≤ n := by linarith [hn.1]
    have h : n.natAbs = n.toNat := by
      have h1 : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg h0
      have h2 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h0
      have h3 : (n.natAbs : ℤ) = (n.toNat : ℤ) := by rw [h1, h2]
      exact_mod_cast h3
    rw [h]

/-- 对称区间上的求和 = 中间项 + 两倍正半边（偶函数）。 -/
theorem sum_Icc_symm_eq (K : ℤ) (hK : 0 ≤ K) (f : ℤ → ℕ) (hf : ∀ n, f (-n) = f n) :
    (∑ n ∈ Finset.Icc (-K) K, f n) = f 0 + 2 * ∑ n ∈ Finset.Icc 1 K, f n := by
  have h1 : Finset.Icc (-K) K = Finset.Icc (-K) (-1) ∪ Finset.Icc 0 K := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt n (-1) with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by omega⟩
      · exact ⟨by omega, h2⟩
  have hdisj : Disjoint (Finset.Icc (-K) (-1)) (Finset.Icc 0 K) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rw [Finset.mem_Icc] at h1 h2
    omega
  have h2 : Finset.Icc (0 : ℤ) K = insert 0 (Finset.Icc 1 K) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨le_refl 0, hK⟩
      · exact ⟨by omega, h2⟩
  have h3 : (∑ n ∈ Finset.Icc (-K) (-1), f n) = ∑ n ∈ Finset.Icc 1 K, f n := by
    refine Finset.sum_bij (fun n _ => -n) ?_ ?_ ?_ ?_
    · -- maps
      intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · -- inj
      intro n _ n' _ heq
      omega
    · -- surj
      intro m hm
      rw [Finset.mem_Icc] at hm
      refine ⟨-m, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · ring
    · -- val
      intro n _
      exact (hf n).symm
  rw [h1, Finset.sum_union hdisj, h2, Finset.sum_insert (by simp), h3]
  ring

end Waring
