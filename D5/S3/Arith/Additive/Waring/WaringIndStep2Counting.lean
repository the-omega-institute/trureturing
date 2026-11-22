/- GID: D5/S3/Arith/Additive/Waring/WaringIndStep2Counting
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringIndStep2.lean#L494-L1003
   Modified for this repository. Local imports use their D5 module paths.
   This file contains one segment of a split upstream module.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringIndStep2Estimates

open Finset intervalIntegral

namespace Waring

/-- `n ∈ TS M h ⇒ n ≤ M`。 -/
theorem mem_TS_le {M : ℕ} {h : ℤ} {n : ℕ} (hn : n ∈ TS M h) : n ≤ M := by
  rw [TS, Finset.mem_filter, Finset.mem_range] at hn
  omega

/-- `Q ∈ QSet` 可以写成两个 `Qsum` 之差。 -/
theorem QSet_exists {f : ℤ → ℤ} {M : ℕ} {h : ℤ} {s : ℕ} {Q : ℤ}
    (hQ : Q ∈ QSet f M h s) :
    ∃ u ∈ PIdx M h s, ∃ v ∈ PIdx M h s, Q = Qsum f h u - Qsum f h v := by
  classical
  rw [QSet] at hQ
  obtain ⟨a, ha, hQa⟩ := Finset.mem_biUnion.mp hQ
  rw [Finset.mem_image] at ha hQa
  obtain ⟨v, hv, hav⟩ := ha
  obtain ⟨b, hb, hQb⟩ := hQa
  rw [Finset.mem_image] at hb
  obtain ⟨u, hu, hbu⟩ := hb
  subst hav hbu
  exact ⟨u, hu, v, hv, hQb.symm⟩

/-- 多项式情形：`QSet` 中的每个频率都被 `h` 整除。 -/
theorem QSet_dvd {a : ℕ → ℤ} {d : ℕ} {M : ℕ} {h : ℤ} {s : ℕ} {Q : ℤ}
    (hQ : Q ∈ QSet (fun n => polyEval a d n) M h s) : h ∣ Q := by
  obtain ⟨u, hu, v, hv, hQeq⟩ := QSet_exists hQ
  rw [hQeq, Qsum_polyEval, Qsum_polyEval]
  exact ⟨(∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
      - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ)), by ring⟩

/-- `φ(n) = polyEval (diffCoeff a d h) d n` 在 `|n| ≤ N` 上的界。 -/
theorem polyEval_diffCoeff_abs_le {a : ℕ → ℤ} {d : ℕ} {h : ℤ} {c N : ℕ}
    (hd : 1 ≤ d) (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j))
    (hh : |h| ≤ (N : ℤ)) {n : ℤ} (hn : |n| ≤ (N : ℤ)) :
    |polyEval (diffCoeff a d h) d n| ≤ (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) := by
  unfold polyEval
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j ∈ Finset.range (d + 1),
      |diffCoeff a d h j * n ^ j| ≤ ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases lt_or_eq_of_le (show j ≤ d from by omega) with hjd | hjd
    · rw [abs_mul, abs_pow]
      have h1 := diffCoeff_bound' (a := a) (d := d) (h := h) (c := c) (N := N) ha hh j hjd
      have hnabs : |n| ^ j ≤ (N : ℤ) ^ j := pow_le_pow_left₀ (abs_nonneg n) hn j
      have hN0 : (0 : ℤ) ≤ (N : ℤ) := by positivity
      calc |diffCoeff a d h j| * |n| ^ j
          ≤ ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1 - j)) * (N : ℤ) ^ j :=
            mul_le_mul h1 hnabs (by positivity) (by positivity)
        _ = (coeffConst c d : ℤ) * ((N : ℤ) ^ (d - 1 - j) * (N : ℤ) ^ j) := by ring
        _ = (coeffConst c d : ℤ) * (N : ℤ) ^ ((d - 1 - j) + j) := by rw [pow_add]
        _ = (coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1) := by
            rw [show d - 1 - j + j = d - 1 by omega]
    · rw [hjd, diffCoeff_eq_zero_of_le le_rfl]
      simp only [zero_mul, abs_zero]
      positivity
  calc ∑ j ∈ Finset.range (d + 1), |diffCoeff a d h j * n ^ j|
      ≤ ∑ j ∈ Finset.range (d + 1), ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1)) :=
        Finset.sum_le_sum hterm
    _ = ((d + 1 : ℕ) : ℤ) * ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) := by
        push_cast
        ring

/-- **频率比的大小界**：`Q ∈ QSet`、`h ≠ 0` 时 `|Q/h| ≤ 2s·(d+1)·coeffConst·N^{d−1}`。 -/
theorem QSet_div_abs_le {a : ℕ → ℤ} {d : ℕ} {c N M : ℕ} {h : ℤ} {s : ℕ} {Q : ℤ}
    (hd : 1 ≤ d) (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j))
    (hhN : |h| ≤ (N : ℤ)) (hNM : M ≤ N) (hh0 : h ≠ 0)
    (hQ : Q ∈ QSet (fun n => polyEval a d n) M h s) :
    |Q / h| ≤ ((2 * s * ((d + 1) * coeffConst c d) * N ^ (d - 1) : ℕ) : ℤ) := by
  obtain ⟨u, hu, v, hv, hQeq⟩ := QSet_exists hQ
  have hU : ∀ i, u i ∈ TS M h := fun i => Fintype.mem_piFinset.mp hu i
  have hV : ∀ i, v i ∈ TS M h := fun i => Fintype.mem_piFinset.mp hv i
  have hb : ∀ (w : Fin s → ℕ), (∀ i, w i ∈ TS M h) →
      |∑ i : Fin s, polyEval (diffCoeff a d h) d (w i : ℤ)|
        ≤ (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1)) := by
    intro w hw
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i : Fin s, |polyEval (diffCoeff a d h) d (w i : ℤ)|
        ≤ (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) := by
      intro i
      have hi : w i ≤ M := mem_TS_le (hw i)
      have hn : |((w i : ℕ) : ℤ)| ≤ (N : ℤ) := by
        rw [abs_of_nonneg (by positivity)]
        have h1 : ((w i : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast hi
        have h2 : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNM
        linarith
      exact polyEval_diffCoeff_abs_le hd ha hhN hn
    calc ∑ i : Fin s, |polyEval (diffCoeff a d h) d (w i : ℤ)|
        ≤ ∑ i : Fin s, (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hQeq, Qsum_polyEval, Qsum_polyEval]
  have heq : (h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
        - h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))) / h
      = (∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
        - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ)) := by
    rw [show h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
          - h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))
        = h * ((∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
          - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))) by ring]
    exact Int.mul_ediv_cancel_left _ hh0
  rw [heq]
  have h1 := hb u hU
  have h2 := hb v hV
  have h3 : |(∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
      - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))|
      ≤ |∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ)|
        + |∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ)| := abs_sub _ _
  have h4 : |(∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
      - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))|
      ≤ (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1))
        + (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1)) := by
    linarith
  refine le_trans h4 (le_of_eq ?_)
  push_cast
  ring

/-- `Fintype.piFinset` 在 `Fin 4` 上展开成 4 层求和。 -/
theorem sum_piFinset_fin4 {α : Type*} [DecidableEq α] (S : Finset α)
    (F : (Fin 4 → α) → ℝ) :
    (∑ f ∈ Fintype.piFinset (fun _ : Fin 4 => S), F f)
      = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S,
          F (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) := by
  classical
  let g : α × (α × (α × α)) → ℝ := fun y => F (fun i => if i = 0 then y.1
    else if i = 1 then y.2.1 else if i = 2 then y.2.2.1 else y.2.2.2)
  have hsplit : (∑ x ∈ S ×ˢ (S ×ˢ (S ×ˢ S)), g x)
      = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S,
          F (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) := by
    have h1 : (∑ x ∈ S ×ˢ (S ×ˢ (S ×ˢ S)), g x)
        = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S, g (a, (b, (c, d))) := by
      simp only [Finset.sum_product]
    rw [h1]
  rw [← hsplit]
  refine Finset.sum_bij
    (fun (f : Fin 4 → α) (_ : f ∈ Fintype.piFinset (fun _ : Fin 4 => S)) =>
      (f 0, (f 1, (f 2, f 3)))) ?_ ?_ ?_ ?_
  · -- 像落入盒子
    intro f hf
    rw [Fintype.mem_piFinset] at hf
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_product]
    exact ⟨hf 0, hf 1, hf 2, hf 3⟩
  · -- 单射
    intro f _ f' _ heq
    have h1 : f 0 = f' 0 := by simpa using congrArg (fun z => z.1) heq
    have h2 : f 1 = f' 1 := by simpa using congrArg (fun z => z.2.1) heq
    have h3 : f 2 = f' 2 := by simpa using congrArg (fun z => z.2.2.1) heq
    have h4 : f 3 = f' 3 := by simpa using congrArg (fun z => z.2.2.2) heq
    funext i
    fin_cases i <;> assumption
  · -- 满射
    intro x hx
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_product] at hx
    obtain ⟨ha, hb, hc, hd⟩ := hx
    obtain ⟨a, b, c, d⟩ := x
    refine ⟨fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d,
      ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i <;> simp [ha, hb, hc, hd]
    · simp
  · -- 被求和项一致
    intro f _
    show F f = g (f 0, (f 1, (f 2, f 3)))
    simp only [g]
    congr 1
    funext i
    fin_cases i <;> simp

/-- 第 9 步的 `K`：`|Q/h| ≤ K`（`Q ∈ QSet`，`h ≠ 0`）。 -/
def Kf (c d N : ℕ) : ℕ :=
  2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) * N ^ (d - 1)

/-- 符号函数（`z = 0` 时取 `1`）。 -/
def sgn (z : ℤ) : ℤ := if 0 ≤ z then 1 else -1

theorem sgn_mul_abs (z : ℤ) : sgn z * |z| = z := by
  rw [sgn]
  by_cases h : 0 ≤ z
  · rw [if_pos h, one_mul, abs_of_nonneg h]
  · rw [if_neg h, neg_one_mul, abs_of_neg (by omega)]
    ring

theorem sgn_ne_zero (z : ℤ) : sgn z ≠ 0 := by
  rw [sgn]; split <;> norm_num

theorem sgn_abs (z : ℤ) : |sgn z| = 1 := by
  rw [sgn]; split <;> norm_num

theorem sgn_mul_self (z : ℤ) : sgn z * sgn z = 1 := by
  rw [sgn]; split <;> norm_num

/-- 符号收缩映射 `(h, m) ↦ ((sgn(mᵢ)·hᵢ, |mᵢ|), sgn(mᵢ))`。 -/
noncomputable def sgnMap :
    (Fin 4 → ℤ) × (Fin 4 → ℤ) → ((Fin 4 → ℤ) × (Fin 4 → ℤ)) × (Fin 4 → ℤ) :=
  fun p => ((fun i => sgn (p.2 i) * p.1 i, fun i => |p.2 i|), fun i => sgn (p.2 i))

/-- 符号向量盒子 `{±1}⁴`。 -/
noncomputable def SymBox : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => ({1, -1} : Finset ℤ))

theorem SymBox_card : SymBox.card = 16 := by
  rw [SymBox, Fintype.card_piFinset]
  simp

/-- **(9b) 符号收缩**：`|mᵢ| ≤ K` 的四元组计数不超过 `16·hmCount7 M K`。

映射 `sgnMap : (h, m) ↦ ((sgn(mᵢ)·hᵢ, |mᵢ|), sgn(mᵢ))` 把 `h` 的符号翻转与 `m` 一起，
故 `Σᵢ (sgn(mᵢ)hᵢ)·|mᵢ| = Σᵢ hᵢmᵢ`，方程保持不变；像落在 `hmCount7` 的盒子 `× SymBox`。 -/
theorem card_sym_shrink (M K : ℕ) :
    ((hBox7 M ×ˢ (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(K : ℤ)) (K : ℤ)))).filter
        (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i, p.1 i * p.2 i = 0)).card
      ≤ 16 * hmCount7 M K := by
  classical
  set Msign : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(K : ℤ)) (K : ℤ)) with hMsign
  set A : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ)) :=
    (hBox7 M ×ˢ Msign).filter (fun p => ∑ i, p.1 i * p.2 i = 0) with hA
  set B : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ)) :=
    (hBox7 M ×ˢ mBox7 K).filter (fun p => ∑ i, p.1 i * p.2 i = 0) with hB
  have hBcard : B.card = hmCount7 M K := by
    rw [hB, hmCount7, show (hBox7 M).product (mBox7 K) = hBox7 M ×ˢ mBox7 K from rfl]
  have hmain : A.card ≤ (B ×ˢ SymBox).card := by
    refine Finset.card_le_card_of_injOn sgnMap ?_ ?_
    · -- 像落在 `B × SymBox`
      intro p hp
      rw [Finset.mem_coe, hA, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hp0⟩ := hp
      rw [hBox7, Fintype.mem_piFinset] at hp1
      rw [hMsign, Fintype.mem_piFinset] at hp2
      rw [Finset.mem_coe, Finset.mem_product, hB, Finset.mem_filter, Finset.mem_product]
      simp only [sgnMap]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · -- `sgn m * h ∈ hBox7 M`
        rw [hBox7, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_erase, Finset.mem_Icc]
        have h1 := hp1 i
        rw [Finset.mem_erase, Finset.mem_Icc] at h1
        have habs : |p.1 i| ≤ (M : ℤ) := abs_le.mpr h1.2
        have hmul : |sgn (p.2 i) * p.1 i| = |p.1 i| := by
          rw [abs_mul, sgn_abs, one_mul]
        have habs' : |sgn (p.2 i) * p.1 i| ≤ (M : ℤ) := by
          rw [hmul]; exact habs
        exact ⟨mul_ne_zero (sgn_ne_zero _) h1.1, (abs_le.mp habs').1, (abs_le.mp habs').2⟩
      · -- `|m| ∈ mBox7 K`
        rw [mBox7, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_Icc]
        have h2 := hp2 i
        rw [Finset.mem_Icc] at h2
        have h2' : |p.2 i| ≤ (K : ℤ) := by
          rw [abs_le]; exact h2
        exact ⟨abs_nonneg _, h2'⟩
      · -- 和为零
        have hsum : (∑ i : Fin 4, (sgn (p.2 i) * p.1 i) * |p.2 i|)
            = ∑ i : Fin 4, p.1 i * p.2 i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          calc (sgn (p.2 i) * p.1 i) * |p.2 i| = p.1 i * (sgn (p.2 i) * |p.2 i|) := by ring
            _ = p.1 i * p.2 i := by rw [sgn_mul_abs]
        rw [hsum]
        exact hp0
      · -- `sgn m ∈ {±1}⁴`
        rw [SymBox, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_insert, Finset.mem_singleton]
        by_cases h : 0 ≤ p.2 i
        · rw [sgn, if_pos h]; exact Or.inl rfl
        · rw [sgn, if_neg h]; exact Or.inr rfl
    · -- 单射
      intro p hp q hq heq
      simp only [sgnMap, Prod.mk.injEq] at heq
      obtain ⟨⟨h1, h2⟩, h3⟩ := heq
      have hm : p.2 = q.2 := by
        funext i
        have e1 := congrFun h3 i
        have e2 := congrFun h2 i
        calc p.2 i = sgn (p.2 i) * |p.2 i| := (sgn_mul_abs _).symm
          _ = sgn (q.2 i) * |q.2 i| := by rw [e1, e2]
          _ = q.2 i := sgn_mul_abs _
      have hh : p.1 = q.1 := by
        funext i
        have e1 := congrFun h1 i
        have e3 := congrFun h3 i
        have hfin : sgn (p.2 i) * p.1 i = sgn (p.2 i) * q.1 i := by rw [e1, ← e3]
        calc p.1 i = sgn (p.2 i) * (sgn (p.2 i) * p.1 i) := by
              rw [← mul_assoc, sgn_mul_self, one_mul]
          _ = sgn (p.2 i) * (sgn (p.2 i) * q.1 i) := by rw [hfin]
          _ = q.1 i := by rw [← mul_assoc, sgn_mul_self, one_mul]
      exact Prod.ext hh hm
  rw [Finset.card_product, hBcard, SymBox_card] at hmain
  linarith

/-- `polyEval a 2` 与 `qf (a 2) (a 1)` 差一个常数项。 -/
theorem polyEval_two_eq (a : ℕ → ℤ) (n : ℤ) :
    polyEval a 2 n = qf (a 2) (a 1) n + a 0 := by
  unfold polyEval qf
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, Nat.reduceAdd]
  ring

/-- `expSum` 与 `qSum` 差一个模 1 的因子。 -/
theorem expSum_polyEval_two (a : ℕ → ℤ) (N : ℕ) (α : ℝ) :
    expSum (fun n => polyEval a 2 n) N α
      = e ((a 0 : ℝ) * α) * qSum (a 2) (a 1) N α := by
  unfold expSum qSum
  rw [Fin.sum_univ_eq_sum_range
    (f := fun m : ℕ => e (((qf (a 2) (a 1) (m : ℤ) : ℤ) : ℝ) * α))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hbeta : (fun n => polyEval a 2 n) (n : ℤ) = polyEval a 2 (n : ℤ) := rfl
  rw [hbeta, polyEval_two_eq]
  have hsplit : (((qf (a 2) (a 1) (n : ℤ) + a 0 : ℤ)) : ℝ) * α
      = ((qf (a 2) (a 1) (n : ℤ) : ℤ) : ℝ) * α + ((a 0 : ℤ) : ℝ) * α := by
    push_cast
    ring
  rw [hsplit, e_add]
  ring

/-- **加强版基例的计数界**（求和长度 `M ≤ N`、系数尺度 `N`）。 -/
theorem qEqCount_le_MN (a b : ℤ) (ha : a ≠ 0) (c₁ c₂ N M : ℕ)
    (hM1 : 1 ≤ M) (hM : M ≤ N) (ha2 : a.natAbs ≤ c₂) (hb1 : b.natAbs ≤ c₁ * N) :
    qEqCount a b M ≤ 10000 * (4 * c₂ + 2 * c₁) * N ^ 6 := by
  classical
  -- 链：`qEqCount ≤ qHMCount ≤ Σ qQ² ≤ 10000·qK·M⁴`
  have hstep : (qEqCount a b M : ℚ) ≤ 10000 * (qK a b M : ℚ) * (M : ℚ) ^ 4 := by
    have h1 : (qEqCount a b M : ℚ) ≤ (qHMCount a b M : ℚ) := by
      exact_mod_cast qEqCount_le_qHMCount a b M
    have h2 : (qHMCount a b M : ℚ)
        ≤ ((∑ n ∈ Finset.Icc (-(qK a b M)) (qK a b M), qQ a b M (2 * M) n ^ 2 : ℕ) : ℚ) := by
      exact_mod_cast qHMCount_le_sum_sq a b M
    exact le_trans h1 (le_trans h2 (sum_qQ_sq_le_K a b ha M hM1))
  -- `qK ≤ (4c₂+2c₁)·N·M`
  have hKz : qK a b M ≤ ((4 * (c₂ : ℤ) + 2 * (c₁ : ℤ)) * (N : ℤ)) * (M : ℤ) := by
    have h1 : (a.natAbs : ℤ) ≤ (c₂ : ℤ) := by exact_mod_cast ha2
    have h2 : (b.natAbs : ℤ) ≤ (c₁ : ℤ) * (N : ℤ) := by
      have hcast : ((c₁ * N : ℕ) : ℤ) = (c₁ : ℤ) * (N : ℤ) := by push_cast; ring
      rw [← hcast]
      exact_mod_cast hb1
    have hM0 : (0 : ℤ) ≤ (M : ℤ) := by positivity
    have hMN : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hM
    have hsq : (M : ℤ) ^ 2 ≤ (N : ℤ) * (M : ℤ) := by nlinarith [hM0, hMN]
    have hA : 4 * (M : ℤ) ^ 2 * (a.natAbs : ℤ) ≤ 4 * (N : ℤ) * (M : ℤ) * (c₂ : ℤ) := by
      nlinarith [hsq, h1, hM0, hMN]
    have hB : 2 * (M : ℤ) * (b.natAbs : ℤ) ≤ 2 * (N : ℤ) * (M : ℤ) * (c₁ : ℤ) := by
      nlinarith [h2, hM0]
    unfold qK
    calc 4 * (M : ℤ) ^ 2 * (a.natAbs : ℤ) + 2 * (M : ℤ) * (b.natAbs : ℤ)
        ≤ 4 * (N : ℤ) * (M : ℤ) * (c₂ : ℤ) + 2 * (N : ℤ) * (M : ℤ) * (c₁ : ℤ) := by
          linarith [hA, hB]
      _ = ((4 * (c₂ : ℤ) + 2 * (c₁ : ℤ)) * (N : ℤ)) * (M : ℤ) := by ring
  -- 合并（ℚ）
  have hKq : (qK a b M : ℚ)
      ≤ ((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ)) * (M : ℚ) := by
    exact_mod_cast hKz
  have hMq1 : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM1
  have hMNq : (M : ℚ) ≤ (N : ℚ) := by exact_mod_cast hM
  have hfinal : (qEqCount a b M : ℚ) ≤ 10000 * (4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ) ^ 6 := by
    refine le_trans hstep ?_
    have h4 : (0 : ℚ) ≤ (M : ℚ) ^ 4 := by positivity
    have h16 : (10000 : ℚ) * (qK a b M : ℚ) * (M : ℚ) ^ 4
        ≤ 10000 * (((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ)) * (M : ℚ)) * (M : ℚ) ^ 4 := by
      nlinarith [hKq, h4, sq_nonneg (M : ℚ)]
    refine le_trans h16 ?_
    have hM5 : (M : ℚ) ^ 5 ≤ (N : ℚ) ^ 5 := pow_le_pow_left₀ (by positivity) hMNq 5
    nlinarith [hM5, hMNq, pow_pos (by positivity : (0 : ℚ) < (M : ℚ)) 5]
  exact_mod_cast hfinal

/-- **加强版基例 `P(2)`**（`M ≤ N`）：`≤ R(c)·N⁶`。 -/
theorem meanValueBoundS_two : MeanValueBoundS 2 := by
  refine ⟨fun c : ℕ => 100000 * (((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4), ?_, ?_⟩
  · intro c
    positivity
  · intro c N M hN hM1 hM a ha2nz ha
    have h2 : (a 2).natAbs ≤ c := by
      have h := ha 2 (le_refl 2)
      rw [pow_zero, mul_one] at h
      rw [Int.abs_eq_natAbs] at h
      exact_mod_cast h
    have h1 : (a 1).natAbs ≤ c * N := by
      have h := ha 1 (by norm_num)
      rw [pow_one] at h
      rw [Int.abs_eq_natAbs] at h
      exact_mod_cast h
    have h2' : (a 2 : ℤ) ≠ 0 := ha2nz
    have hfun : ∀ α : ℝ, ‖expSum (fun n => polyEval a 2 n) M α‖ ^ (8 ^ (2 - 1))
        = (Complex.normSq (qSum (a 2) (a 1) M α)) ^ 4 := by
      intro α
      rw [expSum_polyEval_two, norm_mul, norm_e, one_mul]
      rw [Complex.normSq_eq_norm_sq]
      norm_num
      ring
    simp_rw [hfun]
    rw [integral_normSq_pow_four_q]
    -- `qEqCount a b M ≤ 10⁴(4c+2c)N⁶`
    have hcnt := qEqCount_le_MN (a 2) (a 1) h2' c c N M hM1 hM h2 h1
    have hc : (qEqCount (a 2) (a 1) M : ℝ) ≤ 10000 * ((4 * c + 2 * c : ℕ) : ℝ) * (N : ℝ) ^ 6 := by
      exact_mod_cast hcnt
    refine le_trans hc ?_
    have hR : (10000 : ℝ) * ((4 * c + 2 * c : ℕ) : ℝ) * (N : ℝ) ^ 6
        ≤ 100000 * (((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4) * (N : ℝ) ^ (8 ^ (2 - 1) - 2) := by
      have hexp : (8 ^ (2 - 1) - 2 : ℕ) = 6 := by norm_num
      rw [hexp]
      have h1 : (1 : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ 4 * c + 2 * c + 1 := by omega
        exact_mod_cast this
      have h2 : ((4 * c + 2 * c : ℕ) : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4 := by
        have hle : ((4 * c + 2 * c : ℕ) : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) := by
          push_cast
          linarith only [h1]
        calc ((4 * c + 2 * c : ℕ) : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) := hle
          _ = ((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 1 := by ring
          _ ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
      have hkey : (10000 : ℝ) * ((4 * c + 2 * c : ℕ) : ℝ)
          ≤ 100000 * (((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4) := by
        nlinarith [h2, pow_nonneg (by linarith only [h1] : (0:ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ)) 4]
      exact mul_le_mul_of_nonneg_right hkey (by positivity)
    exact hR

end Waring
