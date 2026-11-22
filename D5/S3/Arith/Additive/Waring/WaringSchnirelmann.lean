/- GID: D5/S3/Arith/Additive/Waring/WaringSchnirelmann
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringSchnirelmann.lean#L1-L435
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringDensity
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Shnirelman 密度：Schnirelmann 不等式

`WaringDensity.lean` 证明了「两个集合的密度之和 `> 1` 时它们的和集覆盖 `ℕ`」。
本文件证明真正的 **Schnirelmann 不等式**

```text
δ(A + B) ≥ δ(A) + δ(B) − δ(A)δ(B)        （0 ∈ A ∩ B）
```

从而（迭代）`δ(hA) ≥ 1 − (1 − δ(A))^h`，于是正密度集合是有限阶加法基。

## 证明思路

固定 `n`。把 `[1,n]` 按 `A` 的元素分段：`A ∩ [1,n]` 的点本身都在 `A+B` 里；
其余的点按「前一个 `A` 元素」`p = prevA z` 分组，第 `p` 组有 `d = z - p ∈ [1, g_p]`
其中 `g_p = gapLen A n p` 是从 `p` 出发、在 `[1,n]` 内的空隙长度。组内偏移 `d`
从 `1` 连续取到 `g_p`，所以至少有 `β·g_p` 个 `d` 落在 `B` 里，对应到 `A+B` 的点。
于是

```text
|A+B ∩ [1,n]| ≥ |A ∩ [1,n]| + β·Σ_p g_p = a + β(n − a) ≥ (α + β − αβ) n.
```
-/

open Finset

namespace Waring

/-- 两集合的和集。 -/
def sumset (A B : Set ℕ) : Set ℕ :=
  {z | ∃ a ∈ A, ∃ b ∈ B, a + b = z}

theorem mem_sumset {A B : Set ℕ} {z : ℕ} :
    z ∈ sumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = z := Iff.rfl

/-! ## 前一个 `A` 元素 -/

/-- 不超过 `z-1` 的最大 `A` 中元素（`0 ∈ A` 且 `z ≥ 1` 时存在）。 -/
noncomputable def prevA (A : Set ℕ) (z : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun a => a ∈ A) (z - 1)

theorem prevA_mem {A : Set ℕ} (hA0 : 0 ∈ A) {z : ℕ} (hz : 1 ≤ z) : prevA A z ∈ A := by
  classical
  unfold prevA
  exact Nat.findGreatest_spec (by omega : (0 : ℕ) ≤ z - 1) hA0

theorem prevA_le (A : Set ℕ) (z : ℕ) : prevA A z ≤ z - 1 := by
  classical
  unfold prevA
  exact Nat.findGreatest_le (z - 1)

theorem le_prevA {A : Set ℕ} {z a : ℕ} (ha : a ∈ A) (haz : a ≤ z - 1) : a ≤ prevA A z := by
  classical
  unfold prevA
  exact Nat.le_findGreatest haz ha

/-- 若 `p ∈ A` 且 `p` 与 `z` 之间没有 `A` 的元素，则 `p = prevA z`。 -/
theorem prevA_eq {A : Set ℕ} (hA0 : 0 ∈ A) {z p : ℕ} (hz : 1 ≤ z) (hp : p ∈ A) (hpz : p ≤ z - 1)
    (hnone : ∀ e, p < e → e < z → e ∉ A) : prevA A z = p := by
  classical
  have h1 : p ≤ prevA A z := le_prevA hp hpz
  have h2 : prevA A z ≤ z - 1 := prevA_le A z
  have h3 : prevA A z ∈ A := prevA_mem hA0 hz
  by_contra hne
  have hlt : p < prevA A z := by omega
  exact hnone (prevA A z) hlt (by omega) h3

/-! ## 空隙长度 -/

/-- 从 `p` 出发、在 `[1,n]` 内的空隙长度：最大的 `d`，使 `p+d ≤ n`、`p+d ∉ A`，
并且 `p` 与 `p+d` 之间没有 `A` 的元素。 -/
noncomputable def gapLen (A : Set ℕ) (n p : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun d => 1 ≤ d ∧ p + d ≤ n ∧ p + d ∉ A ∧ ∀ e, p < e → e < p + d → e ∉ A) (n - p)

theorem gapLen_le (A : Set ℕ) (n p : ℕ) : gapLen A n p ≤ n - p := by
  classical
  unfold gapLen
  exact Nat.findGreatest_le (n - p)

theorem gapLen_spec {A : Set ℕ} {n p : ℕ} (h : 1 ≤ gapLen A n p) :
    p + gapLen A n p ≤ n ∧ p + gapLen A n p ∉ A ∧
      ∀ e, p < e → e < p + gapLen A n p → e ∉ A := by
  classical
  have hpos : 0 < Nat.findGreatest
      (fun d => 1 ≤ d ∧ p + d ≤ n ∧ p + d ∉ A ∧ ∀ e, p < e → e < p + d → e ∉ A) (n - p) := by
    have h' : 0 < gapLen A n p := h
    simpa [gapLen] using h'
  obtain ⟨m, hm0, hmb, hmP⟩ := (Nat.findGreatest_pos (k := n - p)).mp hpos
  have hG := Nat.findGreatest_spec (P := fun d =>
      1 ≤ d ∧ p + d ≤ n ∧ p + d ∉ A ∧ ∀ e, p < e → e < p + d → e ∉ A) hmb hmP
  exact ⟨hG.2.1, hG.2.2.1, hG.2.2.2⟩

/-- 小于等于空隙长度的每个 `d` 都满足空隙性质。 -/
theorem gapLen_prop {A : Set ℕ} {n p d : ℕ} (hd1 : 1 ≤ d) (hdG : d ≤ gapLen A n p) :
    p + d ≤ n ∧ p + d ∉ A ∧ ∀ e, p < e → e < p + d → e ∉ A := by
  classical
  set G := gapLen A n p with hG
  have hG1 : 1 ≤ G := le_trans hd1 hdG
  have hPG : p + G ≤ n ∧ p + G ∉ A ∧ ∀ e, p < e → e < p + G → e ∉ A := gapLen_spec hG1
  -- 向下封闭一步
  have hstep : ∀ d', 2 ≤ d' → d' ≤ G → p + d' ∉ A →
      (∀ e, p < e → e < p + d' → e ∉ A) →
      p + (d' - 1) ∉ A ∧ ∀ e, p < e → e < p + (d' - 1) → e ∉ A := by
    intro d' hd' _ hnot hno
    refine ⟨?_, ?_⟩
    · by_contra hmem
      exact hno (p + (d' - 1)) (by omega) (by omega) hmem
    · intro e he1 he2
      exact hno e he1 (by omega)
  -- 从 `G` 向下归纳
  have key : ∀ k, k ≤ G - 1 →
      p + (G - k) ∉ A ∧ ∀ e, p < e → e < p + (G - k) → e ∉ A := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using ⟨hPG.2.1, hPG.2.2⟩
    | succ k ih =>
      intro hk
      have hk' : k ≤ G - 1 := by omega
      obtain ⟨hnot, hno⟩ := ih hk'
      have h2 : 2 ≤ G - k := by omega
      have hle : G - k ≤ G := by omega
      have := hstep (G - k) h2 hle hnot hno
      have heq : G - (k + 1) = G - k - 1 := by omega
      rwa [heq]
  have hk : G - d ≤ G - 1 := by omega
  obtain ⟨hnot, hno⟩ := key (G - d) hk
  have heq : G - (G - d) = d := by omega
  rw [heq] at hnot hno
  exact ⟨by have := gapLen_le A n p; omega, hnot, hno⟩

/-! ## 单射性 -/

/-- 不同的 `(p, d)` 给出不同的和。 -/
theorem pair_inj {A : Set ℕ} {n p d p' d' : ℕ} (hp : p ∈ A) (hd1 : 1 ≤ d)
    (hdG : d ≤ gapLen A n p) (hp' : p' ∈ A) (hd1' : 1 ≤ d')
    (hdG' : d' ≤ gapLen A n p') (h : p + d = p' + d') : p = p' ∧ d = d' := by
  classical
  have hpd : p + d ∉ A := (gapLen_prop hd1 hdG).2.1
  have hp'd' : p' + d' ∉ A := (gapLen_prop hd1' hdG').2.1
  have hno : ∀ e, p < e → e < p + d → e ∉ A := (gapLen_prop hd1 hdG).2.2
  have hno' : ∀ e, p' < e → e < p' + d' → e ∉ A := (gapLen_prop hd1' hdG').2.2
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · -- p' = p + (d - d')，落在 (p, p+d) 内，与空隙矛盾
    have hd'd : d' < d := by omega
    have hp'eq : p' = p + (d - d') := by omega
    exact absurd (hp'eq ▸ hp') (hno (p + (d - d')) (by omega) (by omega))
  · subst heq
    exact ⟨rfl, by omega⟩
  · have hdd' : d < d' := by omega
    have hpeq : p = p' + (d' - d) := by omega
    exact absurd (hpeq ▸ hp) (hno' (p' + (d' - d)) (by omega) (by omega))

/-! ## Schnirelmann 不等式 -/

theorem add_density {A B : Set ℕ} {α β : ℚ}
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hβ0 : 0 ≤ β)
    (hA : HasDensity A α) (hB : HasDensity B β) :
    HasDensity (sumset A B) (α + β - α * β) := by
  classical
  intro n hn
  -- 计数集合
  set p1 : Finset ℕ := (Finset.Icc 1 n).filter (fun z => z ∈ A) with hp1
  set p2 : Finset ℕ := (Finset.Icc 1 n).filter (fun z => z ∉ A ∧ (z - prevA A z) ∈ B) with hp2
  set gap : Finset ℕ := (Finset.Icc 1 n).filter (fun z => z ∉ A) with hgap
  have hcard : (Finset.Icc 1 n).card = n := by simp
  have hp1card : p1.card = densityCount A n := by
    rw [hp1]
    simp [densityCount]
  have hgapcard : gap.card = n - p1.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 n) (p := fun z => z ∈ A)
    rw [← hp1, ← hgap, hcard] at h
    omega
  -- 两部分都落在和集里
  have hsub1 : p1 ⊆ (Finset.Icc 1 n).filter (fun z => z ∈ sumset A B) := by
    intro z hz
    rw [hp1, Finset.mem_filter, Finset.mem_Icc] at hz
    obtain ⟨⟨hz1, hzn⟩, hzA⟩ := hz
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hz1, hzn⟩, mem_sumset.mpr ⟨z, hzA, 0, hB0, by simp⟩⟩
  have hsub2 : p2 ⊆ (Finset.Icc 1 n).filter (fun z => z ∈ sumset A B) := by
    intro z hz
    rw [hp2, Finset.mem_filter, Finset.mem_Icc] at hz
    obtain ⟨⟨hz1, hzn⟩, hzA, hzB⟩ := hz
    have hpA : prevA A z ∈ A := prevA_mem hA0 hz1
    have hpz : prevA A z ≤ z - 1 := prevA_le A z
    have hzeq : prevA A z + (z - prevA A z) = z := by omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hz1, hzn⟩, mem_sumset.mpr ⟨prevA A z, hpA, z - prevA A z, hzB, hzeq⟩⟩
  have hdisj : Disjoint p1 p2 := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [hp1, Finset.mem_filter] at hz1
    rw [hp2, Finset.mem_filter] at hz2
    exact hz2.2.1 hz1.2
  have hmain : p1.card + p2.card ≤ densityCount (sumset A B) n := by
    have hd : densityCount (sumset A B) n
        = ((Finset.Icc 1 n).filter (fun z => z ∈ sumset A B)).card := by
      simp [densityCount]
    rw [hd, ← Finset.card_union_of_disjoint hdisj]
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with h | h
    · exact hsub1 h
    · exact hsub2 h
  -- `p2` 由 `Σ_p |B ∩ [1, gapLen p]|` 从下方控制
  set T : Finset (Σ _ : ℕ, ℕ) :=
    ((Finset.Icc 0 n).filter (fun p => p ∈ A)).sigma
      (fun p => (Finset.Icc 1 (gapLen A n p)).filter (fun d => d ∈ B)) with hT
  have hT_le : T.card ≤ p2.card := by
    refine Finset.card_le_card_of_injOn (fun x : (Σ _ : ℕ, ℕ) => x.1 + x.2) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, hT, Finset.mem_sigma] at hx
      obtain ⟨hxp, hxd⟩ := hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hxp
      obtain ⟨⟨hx0, hxn⟩, hxA⟩ := hxp
      rw [Finset.mem_filter, Finset.mem_Icc] at hxd
      obtain ⟨⟨hxd1, hxdn⟩, hxB⟩ := hxd
      obtain ⟨hle, hnotA, hnoA⟩ := gapLen_prop hxd1 hxdn
      have hz1 : 1 ≤ x.1 + x.2 := le_trans hxd1 (Nat.le_add_left x.2 x.1)
      rw [Finset.mem_coe, hp2, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hz1, hle⟩, hnotA, ?_⟩
      have hprev : prevA A (x.1 + x.2) = x.1 := by
        refine prevA_eq hA0 hz1 hxA (by omega) ?_
        intro e he1 he2
        exact hnoA e he1 he2
      rw [hprev]
      rw [Nat.add_sub_cancel_left x.1 x.2]
      exact hxB
    · intro x hx y hy hxy
      rw [Finset.mem_coe, hT, Finset.mem_sigma] at hx hy
      obtain ⟨hxp, hxd⟩ := hx
      obtain ⟨hyp, hyd⟩ := hy
      rw [Finset.mem_filter, Finset.mem_Icc] at hxp hyp
      rw [Finset.mem_filter, Finset.mem_Icc] at hxd hyd
      have hinj := pair_inj hxp.2 hxd.1.1 hxd.1.2 hyp.2 hyd.1.1 hyd.1.2 hxy
      obtain ⟨p, d⟩ := x
      obtain ⟨p', d'⟩ := y
      simp only at hinj hxy ⊢
      rw [hinj.1, hinj.2]
  -- `Σ_p gapLen p ≥ n - p1.card`：空隙点与 `(p,d)` 单射
  set T' : Finset (Σ _ : ℕ, ℕ) :=
    ((Finset.Icc 0 n).filter (fun p => p ∈ A)).sigma
      (fun p => Finset.Icc 1 (gapLen A n p)) with hT'
  have hT'_le : T'.card ≤ gap.card := by
    refine Finset.card_le_card_of_injOn (fun x : (Σ _ : ℕ, ℕ) => x.1 + x.2) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, hT', Finset.mem_sigma] at hx
      obtain ⟨hxp, hxd⟩ := hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hxp
      obtain ⟨⟨hx0, hxn⟩, hxA⟩ := hxp
      rw [Finset.mem_Icc] at hxd
      obtain ⟨hxd1, hxdn⟩ := hxd
      obtain ⟨hle, hnotA, -⟩ := gapLen_prop hxd1 hxdn
      have hz1 : 1 ≤ x.1 + x.2 := le_trans hxd1 (Nat.le_add_left x.2 x.1)
      rw [Finset.mem_coe, hgap, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hz1, hle⟩, hnotA⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe, hT', Finset.mem_sigma] at hx hy
      obtain ⟨hxp, hxd⟩ := hx
      obtain ⟨hyp, hyd⟩ := hy
      rw [Finset.mem_filter, Finset.mem_Icc] at hxp hyp
      rw [Finset.mem_Icc] at hxd hyd
      have hinj := pair_inj hxp.2 hxd.1 hxd.2 hyp.2 hyd.1 hyd.2 hxy
      obtain ⟨p, d⟩ := x
      obtain ⟨p', d'⟩ := y
      simp only at hinj hxy ⊢
      rw [hinj.1, hinj.2]
  have hT'_card : T'.card = ∑ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A), gapLen A n p := by
    rw [hT', Finset.card_sigma]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Nat.card_Icc]
    omega
  -- 反向单射：每个空隙点给出一个 `(p, d)`
  have hgap_le : gap.card ≤ T'.card := by
    refine Finset.card_le_card_of_injOn
      (fun z => (⟨prevA A z, z - prevA A z⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, hgap, Finset.mem_filter, Finset.mem_Icc] at hz
      obtain ⟨⟨hz1, hzn⟩, hzA⟩ := hz
      have hpA : prevA A z ∈ A := prevA_mem hA0 hz1
      have hpz : prevA A z ≤ z - 1 := prevA_le A z
      have hpz' : prevA A z ≤ z := by omega
      have hzeq : prevA A z + (z - prevA A z) = z := Nat.add_sub_of_le hpz'
      have hd1 : 1 ≤ z - prevA A z := by omega
      have hP : 1 ≤ z - prevA A z ∧ prevA A z + (z - prevA A z) ≤ n ∧
          prevA A z + (z - prevA A z) ∉ A ∧
          ∀ e, prevA A z < e → e < prevA A z + (z - prevA A z) → e ∉ A := by
        refine ⟨hd1, ?_, ?_, ?_⟩
        · rw [hzeq]; exact hzn
        · rw [hzeq]; exact hzA
        · intro e he1 he2 heA
          have hez : e < z := by rw [← hzeq]; exact he2
          have hle := le_prevA heA (z := z) (by omega)
          omega
      have hdG : z - prevA A z ≤ gapLen A n (prevA A z) :=
        Nat.le_findGreatest (Nat.sub_le_sub_right hzn (prevA A z)) hP
      rw [Finset.mem_coe, hT', Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_Icc]
      exact ⟨⟨⟨Nat.zero_le _, le_trans hpz' hzn⟩, hpA⟩, hd1, hdG⟩
    · intro z hz z' hz' heq
      simp only [Sigma.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have h2' : z - prevA A z = z' - prevA A z' := eq_of_heq h2
      have hzp : prevA A z ≤ z := by
        have := prevA_le A z
        omega
      have hzp' : prevA A z' ≤ z' := by
        have := prevA_le A z'
        omega
      calc z = prevA A z + (z - prevA A z) := (Nat.add_sub_of_le hzp).symm
        _ = prevA A z' + (z' - prevA A z') := by rw [h2', h1]
        _ = z' := Nat.add_sub_of_le hzp'
  have hT'_eq : T'.card = gap.card := le_antisymm hT'_le hgap_le
  -- ℚ 上的两条界
  have hsum_bound : β * (∑ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A), (gapLen A n p : ℚ))
      ≤ (p2.card : ℚ) := by
    have h : (T.card : ℚ) ≤ (p2.card : ℚ) := by exact_mod_cast hT_le
    rw [hT, Finset.card_sigma] at h
    rw [Nat.cast_sum] at h
    -- 逐项用密度
    have hterm : ∀ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A),
        β * (gapLen A n p : ℚ)
          ≤ (((Finset.Icc 1 (gapLen A n p)).filter (fun d => d ∈ B)).card : ℚ) := by
      intro p _
      rcases Nat.eq_zero_or_pos (gapLen A n p) with h0 | hpos
      · simp [h0]
      · exact hB (gapLen A n p) hpos
    calc β * (∑ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A), (gapLen A n p : ℚ))
        = ∑ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A), β * (gapLen A n p : ℚ) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A),
            (((Finset.Icc 1 (gapLen A n p)).filter (fun d => d ∈ B)).card : ℚ) :=
          Finset.sum_le_sum hterm
      _ ≤ (p2.card : ℚ) := h
  have hgap_bound : (n : ℚ) - (p1.card : ℚ)
      ≤ ∑ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A), (gapLen A n p : ℚ) := by
    rw [← Nat.cast_sum]
    have hsumcast : ((∑ p ∈ (Finset.Icc 0 n).filter (fun p => p ∈ A), gapLen A n p : ℕ) : ℚ)
        = (gap.card : ℚ) := by
      exact_mod_cast (hT'_card.symm.trans hT'_eq)
    have hle : p1.card ≤ n := by
      have hsub := Finset.card_le_card (Finset.filter_subset (fun z => z ∈ A) (Finset.Icc 1 n))
      rw [← hp1] at hsub
      rw [hcard] at hsub
      exact hsub
    have hgapq : (gap.card : ℚ) = (n : ℚ) - (p1.card : ℚ) := by
      rw [hgapcard, Nat.cast_sub hle]
    rw [hsumcast, hgapq]
  -- 主不等式
  have hα : α * (n : ℚ) ≤ (p1.card : ℚ) := by
    have h := hA n hn
    rwa [← hp1card] at h
  have hβle : β ≤ 1 := hasDensity_le_one hB
  have hfin : (α + β - α * β) * (n : ℚ) ≤ (p1.card : ℚ) + (p2.card : ℚ) := by
    nlinarith [hα, hβ0, hβle, hsum_bound, hgap_bound]
  have hmainq : ((p1.card : ℚ) + (p2.card : ℚ)) ≤ (densityCount (sumset A B) n : ℚ) := by
    exact_mod_cast hmain
  linarith

/-! ## 迭代：`δ(hA) ≥ 1 − (1 − δ(A))^h` -/

/-- `k` 重和集。 -/
def sumsetPow (A : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | (k + 1) => sumset (sumsetPow A k) A

theorem zero_mem_sumsetPow {A : Set ℕ} (hA0 : 0 ∈ A) : ∀ k : ℕ, 0 ∈ sumsetPow A k
  | 0 => rfl
  | (k + 1) => mem_sumset.mpr ⟨0, zero_mem_sumsetPow hA0 k, 0, hA0, by simp⟩

/-- 叠加 `k` 次后密度至少是 `1 - (1 - δ(A))^k`。 -/
theorem density_pow {A : Set ℕ} {α : ℚ} (hA0 : 0 ∈ A) (hα0 : 0 ≤ α) (hA : HasDensity A α) :
    ∀ k : ℕ, HasDensity (sumsetPow A k) (1 - (1 - α) ^ k) := by
  intro k
  induction k with
  | zero =>
    intro n _
    have h0 : (1 - (1 - α) ^ 0) = 0 := by simp
    rw [h0]
    simp
  | succ m ih =>
    have hmem : (0 : ℕ) ∈ sumsetPow A m := zero_mem_sumsetPow hA0 m
    have hres := add_density hmem hA0 hα0 ih hA
    have heq : 1 - (1 - α) ^ m + α - (1 - (1 - α) ^ m) * α = 1 - (1 - α) ^ (m + 1) := by
      ring
    rwa [heq] at hres

/-- **Shnirelman 定理**：正密度集合是有限阶加法基。 -/
theorem schnirelmann {A : Set ℕ} (hA0 : 0 ∈ A) {α : ℚ} (hα0 : 0 < α) (hA : HasDensity A α) :
    ∃ h : ℕ, ∀ n : ℕ, n ∈ sumsetPow A h := by
  have hαle : α ≤ 1 := hasDensity_le_one hA
  -- 用 `α/2` 避开 `α = 1` 的边界
  set α' : ℚ := α / 2 with hα'def
  have hα'0 : 0 < α' := by rw [hα'def]; linarith
  have hα'lt : α' < 1 := by rw [hα'def]; linarith
  have hα'le : α' ≤ α := by rw [hα'def]; linarith
  have hpos : (0 : ℚ) < 1 - α' := by linarith
  have hA' : HasDensity A α' := by
    intro m hm
    have h := hA m hm
    have hle : α' * (m : ℚ) ≤ α * (m : ℚ) :=
      mul_le_mul_of_nonneg_right hα'le (by positivity)
    linarith
  have hy : 1 < (1 - α')⁻¹ := (one_lt_inv₀ hpos).mpr (by linarith)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (x := (α')⁻¹) (y := (1 - α')⁻¹) hy
  have hk' : (1 - α') ^ k < α' := by
    have hb : (0 : ℚ) < (1 - α') ^ k := pow_pos hpos k
    rw [inv_pow] at hk
    exact (inv_lt_inv₀ hα'0 hb).mp hk
  have hdens : HasDensity (sumsetPow A k) (1 - (1 - α') ^ k) :=
    density_pow hA0 (le_of_lt hα'0) hA' k
  have hσ : 1 - α' < 1 - (1 - α') ^ k := by linarith
  have hmem : (0 : ℕ) ∈ sumsetPow A k := zero_mem_sumsetPow hA0 k
  refine ⟨k + 1, fun n => ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ :=
    add_eq_univ_of_density hmem hA0 hdens hA' (by linarith) n
  exact mem_sumset.mpr ⟨a, ha, b, hb, hab⟩

end Waring
