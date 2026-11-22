/- GID: D5/S3/Arith/Additive/Waring/WaringSymm
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringSymm.lean#L1-L169
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

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

/-- `Q(0)` 的界。 -/
theorem Q_zero_le (H M : ℕ) :
    Q H M 0 ≤ (M + 1) ^ 2 + 4 * H * (H + 1) * (M + 1) := by
  classical
  have hcardD : (box2 (0 : ℤ) (M : ℤ)).card = (M + 1) ^ 2 := by
    rw [box2, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Int.card_Icc]
    have h : (M : ℤ) + 1 - 0 = (M : ℤ) + 1 := by ring
    rw [h]
    omega
  set B : Finset (Fin 2 → ℤ) := box2 (-(H : ℤ)) (H : ℤ) with hB
  set D : Finset (Fin 2 → ℤ) := box2 (0 : ℤ) (M : ℤ) with hD
  set F : (Fin 2 → ℤ) → ℕ :=
    fun h => (D.filter (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = 0)).card with hF
  have hQ : Q H M 0 = ∑ h ∈ B, F h := Q_eq_sum_fiber H M 0
  have hzero : F 0 = (M + 1) ^ 2 := by
    have hmain : (D.filter (fun m : Fin 2 → ℤ =>
        (0 : Fin 2 → ℤ) 0 * m 0 + (0 : Fin 2 → ℤ) 1 * m 1 = 0)).card = (M + 1) ^ 2 := by
      have hfil : (D.filter (fun m : Fin 2 → ℤ =>
          (0 : Fin 2 → ℤ) 0 * m 0 + (0 : Fin 2 → ℤ) 1 * m 1 = 0)) = D := by
        apply Finset.filter_true_of_mem
        intro m _
        simp
      rw [hfil, hD, hcardD]
    rw [hF]
    exact hmain
  have h0mem : (0 : Fin 2 → ℤ) ∈ B := by
    rw [hB]
    exact mem_box2_of_abs_le (fun i => by simp)
  have hrest : ∀ h ∈ B.erase 0, F h ≤ M + 1 := by
    intro h hh
    rw [Finset.mem_erase] at hh
    obtain ⟨hne, -⟩ := hh
    have hb := fiber_le_gcd hne M 0
    rw [← hD] at hb
    rw [hF]
    refine le_trans hb ?_
    have hprim : prim h ≠ 0 := by
      intro hp
      apply hne
      funext i
      rw [h_eq_gcd_mul_prim h i, congrFun hp i]
      simp
    have hmax : 0 < max (prim h 0).natAbs (prim h 1).natAbs := by
      rcases eq_or_ne (prim h 0) 0 with h0 | h0
      · rcases eq_or_ne (prim h 1) 0 with h1 | h1
        · exact absurd (by funext i; fin_cases i <;> assumption) hprim
        · rw [h0]
          exact Nat.lt_of_lt_of_le (Int.natAbs_pos.mpr h1) (le_max_right _ _)
      · exact Nat.lt_of_lt_of_le (Int.natAbs_pos.mpr h0) (le_max_left _ _)
    have hle : M / max (prim h 0).natAbs (prim h 1).natAbs ≤ M := Nat.div_le_self M _
    omega
  have hsplit : (∑ h ∈ B, F h) = F 0 + ∑ h ∈ B.erase 0, F h := by
    have hmem : (0 : Fin 2 → ℤ) ∉ B.erase 0 := by
      rw [Finset.mem_erase]
      intro h
      exact h.1 rfl
    rw [← Finset.insert_erase h0mem, Finset.sum_insert hmem, Finset.erase_insert hmem]
  have hcardE : (B.erase 0).card = 4 * H * (H + 1) := by
    rw [Finset.card_erase_of_mem h0mem, hB, card_box2]
    have hsq : (2 * H + 1) ^ 2 = 4 * H * (H + 1) + 1 := by ring
    rw [hsq, Nat.add_sub_cancel]
  calc Q H M 0 = ∑ h ∈ B, F h := hQ
    _ = F 0 + ∑ h ∈ B.erase 0, F h := hsplit
    _ ≤ (M + 1) ^ 2 + (B.erase 0).card * (M + 1) := by
        rw [hzero]
        have hsum : (∑ h ∈ B.erase 0, F h) ≤ ∑ h ∈ B.erase 0, (M + 1) :=
          Finset.sum_le_sum hrest
        rw [Finset.sum_const, nsmul_eq_mul] at hsum
        exact Nat.add_le_add_left hsum _
    _ = (M + 1) ^ 2 + 4 * H * (H + 1) * (M + 1) := by
        rw [hcardE]

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
