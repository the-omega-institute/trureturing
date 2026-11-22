/- GID: D5/S3/Arith/Additive/Waring/WaringLinnik
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringLinnik.lean#L1-L100
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringSchnirelmann

/-!
# 从正密度到 Waring：Linnik 证明的最后一次接线

`WaringSchnirelmann.schnirelmann` 证明：正 Shnirelman 密度集合是有限阶加法基。
这里把它与 `IsSumOfKthPowers` 组合起来，得到

```lean
theorem isWaringBound_of_positive_density {k s : ℕ} {δ : ℚ} (hδ : 0 < δ)
    (h : HasDensity {n | ∃ t ≤ s, IsSumOfKthPowers k n t} δ) :
    ∃ g, IsWaringBound k g
```

即：**若「至多 `s` 个 `k` 次幂之和」的集合有正密度，则 Waring 对 `k` 成立。**
配合 Linnik 的均值和估计（`WARING-M3-PLAN.md` Theorem 1，取 `s = 8^{k-1}`）
就得到完整的 Waring–Hilbert 定理；那条分析不等式是本仓库唯一剩下的缺口。

本文件不含任何分析；它只是把「`h` 重和集」展开成 `h×s` 个 `k` 次幂。
-/

open Finset

namespace Waring

/-- `sumsetPow S h` 的成员可以写成 `h` 个 `S` 中元素之和。 -/
theorem exists_sum_repr {S : Set ℕ} :
    ∀ (h n : ℕ), n ∈ sumsetPow S h → ∃ f : Fin h → ℕ, (∀ i, f i ∈ S) ∧ n = ∑ i, f i
  | 0, n, hn => by
    have hn0 : n = 0 := by simpa [sumsetPow] using hn
    exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [hn0]⟩
  | h + 1, n, hn => by
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sumset.mp hn
    obtain ⟨f, hf, hsum⟩ := exists_sum_repr h a ha
    refine ⟨Fin.snoc f b, ?_, ?_⟩
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using hf j
      · simpa using hb
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hab, hsum]

/-- 逐项把表示拼起来：`∑ f i` 是 `∑ t i` 个 `k` 次幂之和。 -/
theorem IsSumOfKthPowers.sum_fin {k : ℕ} (h : ℕ) :
    ∀ (f t : Fin h → ℕ), (∀ i, IsSumOfKthPowers k (f i) (t i)) →
      IsSumOfKthPowers k (∑ i, f i) (∑ i, t i) := by
  induction h with
  | zero =>
    intro f t _
    have hf0 : (∑ i : Fin 0, f i) = 0 := by simp
    have ht0 : (∑ i : Fin 0, t i) = 0 := by simp
    rw [hf0, ht0]
    exact ⟨fun i => i.elim0, by simp⟩
  | succ h ih =>
    intro f t H
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    exact IsSumOfKthPowers.add
      (ih (fun i => f (Fin.castSucc i)) (fun i => t (Fin.castSucc i))
        (fun i => H (Fin.castSucc i)))
      (H (Fin.last h))

/-- **密度 ⟹ Waring。** 若「至多 `s` 个 `k` 次幂之和」全体有正 Shnirelman 密度，
则存在 `g` 使每个自然数都是至多 `g` 个 `k` 次幂之和。 -/
theorem isWaringBound_of_positive_density {k s : ℕ} {δ : ℚ} (hδ : 0 < δ)
    (hdens : HasDensity {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} δ) :
    ∃ g : ℕ, IsWaringBound k g := by
  classical
  set S : Set ℕ := {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} with hS
  have hdens' : HasDensity S δ := by rw [hS]; exact hdens
  have h0 : (0 : ℕ) ∈ S := by
    refine ⟨0, Nat.zero_le s, ?_⟩
    exact ⟨fun i => 0, by simp⟩
  obtain ⟨h, hh⟩ := schnirelmann h0 hδ hdens'
  refine ⟨h * s, fun n => ?_⟩
  obtain ⟨f, hf, hsum⟩ := exists_sum_repr h n (hh n)
  have hf' : ∀ i, ∃ t, t ≤ s ∧ IsSumOfKthPowers k (f i) t := fun i => hf i
  choose t ht hrep using hf'
  refine ⟨∑ i : Fin h, t i, ?_, ?_⟩
  · calc (∑ i : Fin h, t i) ≤ ∑ _i : Fin h, s := Finset.sum_le_sum (fun i _ => ht i)
      _ = h * s := by simp
  · rw [hsum]
    exact IsSumOfKthPowers.sum_fin h f t hrep

/-- Linnik 路线的最终接口：若对每个 `k` 都存在正密度的 `k` 次幂和集，
则 Waring 定理成立。 -/
theorem waringTheorem_of_positive_density
    (h : ∀ k : ℕ, 0 < k → ∃ s : ℕ, ∃ δ : ℚ, 0 < δ ∧
      HasDensity {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} δ) :
    WaringTheorem := by
  intro k hk
  obtain ⟨s, δ, hδ, hdens⟩ := h k hk
  exact isWaringBound_of_positive_density hδ hdens

end Waring
