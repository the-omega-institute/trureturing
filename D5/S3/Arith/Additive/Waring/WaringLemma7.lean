/- GID: D5/S3/Arith/Additive/Waring/WaringLemma7
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringLemma7.lean#L1-L607
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/

import D5.S3.Arith.Additive.Waring.WaringTheorem1

/-!
# Lemma 7（Jameson）：`h₁,…,h₄` 全部非零的解数界

Weyl 归纳需要的是「`hᵢ ≠ 0`」版本的八次矩计数：

```text
N(H, M) = #{(h, m) : hᵢ ∈ [-H,H]\{0}, mᵢ ∈ [0,M], Σ hᵢmᵢ = 0} ≤ C·(HM)³
```

本文件把它化归为 `q₇` 的平方和（Fubini），再用 Lemma 3 + Lemma 6 逐项估计。
零点的项用「`h ≠ 0` 排除 `(0,0)`」单独算，不给 `(M+1)²`。
-/

open Finset

namespace Waring

/-! ## 非零 `h` 的二元盒子 -/

/-- `h ∈ [−H,H]² \ {0}`。 -/
noncomputable def box2nz (H : ℕ) : Finset (Fin 2 → ℤ) :=
  (box2 (-(H : ℤ)) (H : ℤ)).erase 0

/-- 原点属于 `box2 (−H) H`。 -/
theorem zero_mem_box2 (H : ℕ) : (0 : Fin 2 → ℤ) ∈ box2 (-(H : ℤ)) (H : ℤ) :=
  mem_box2_of_abs_le (fun _ => by simp)

/-- `box2nz H` 的基数：`(2H+1)² − 1 = 4H(H+1)`。 -/
theorem card_box2nz (H : ℕ) : (box2nz H).card = 4 * H * (H + 1) := by
  rw [box2nz, Finset.card_erase_of_mem (zero_mem_box2 H), card_box2]
  have hsq : (2 * H + 1) ^ 2 = 4 * H * (H + 1) + 1 := by ring
  rw [hsq, Nat.add_sub_cancel]

/-- `box2nz` 的成员刻画。 -/
theorem mem_box2nz {H : ℕ} {h : Fin 2 → ℤ} :
    h ∈ box2nz H ↔ h ≠ 0 ∧ ∀ i, |h i| ≤ (H : ℤ) := by
  rw [box2nz, Finset.mem_erase]
  constructor
  · rintro ⟨hne, hmem⟩
    exact ⟨hne, fun i => abs_le_of_mem_box2 hmem i⟩
  · rintro ⟨hne, hle⟩
    exact ⟨hne, mem_box2_of_abs_le hle⟩

/-- `h ↦ −h` 保持 `box2nz`。 -/
theorem neg_mem_box2nz {H : ℕ} {h : Fin 2 → ℤ} (hh : h ∈ box2nz H) : -h ∈ box2nz H := by
  rw [mem_box2nz] at hh ⊢
  refine ⟨neg_ne_zero.mpr hh.1, fun i => ?_⟩
  simpa using hh.2 i

/-! ## `q₇`：`h ≠ 0` 的二元部分和 -/

/-- `h ∈ [−H,H]²\{0}`、`m ∈ [0,M]²` 里 `h₀m₀ + h₁m₁ = n` 的解数。 -/
noncomputable def Q7 (H M : ℕ) (n : ℤ) : ℕ :=
  (((box2nz H).product (box2 (0 : ℤ) (M : ℤ))).filter
    (fun x : (Fin 2 → ℤ) × (Fin 2 → ℤ) => x.1 0 * x.2 0 + x.1 1 * x.2 1 = n)).card

/-- **擦除只会减少计数**：`q₇(n) ≤ Q(n)`。 -/
theorem Q7_le_Q (H M : ℕ) (n : ℤ) : Q7 H M n ≤ Q H M n := by
  classical
  unfold Q7 Q box2nz
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_product.mpr
    ⟨Finset.mem_of_mem_erase (Finset.mem_product.mp hx.1).1, (Finset.mem_product.mp hx.1).2⟩, hx.2⟩

/-- **Lemma 3 的 `q₇` 版**：`q₇(n) ≤ 4H(H+1) + 8HM·σ₋₁(|n|)`（`n ≠ 0`）。 -/
theorem Q7_le_sigma (H M : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (Q7 H M n : ℚ) ≤ 4 * (H : ℚ) * ((H : ℚ) + 1)
      + 8 * (H : ℚ) * (M : ℚ) * sigmaMinusOne n.natAbs := by
  refine le_trans ?_ (Q_le_sigma H M hn)
  have h := Q7_le_Q H M n
  have h' : ((Q7 H M n : ℕ) : ℚ) ≤ ((Q H M n : ℕ) : ℚ) := by exact_mod_cast h
  exact h'

/-- `q₇` 按 `h` 拆成纤维的卡片和。 -/
theorem Q7_eq_sum_fiber (H M : ℕ) (n : ℤ) :
    Q7 H M n = ∑ h ∈ box2nz H,
        ((box2 (0 : ℤ) (M : ℤ)).filter
          (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n)).card := by
  classical
  rw [Q7, Finset.card_filter]
  rw [show (∑ i ∈ (box2nz H).product (box2 (0 : ℤ) (M : ℤ)),
        (if i.1 0 * i.2 0 + i.1 1 * i.2 1 = n then (1 : ℕ) else 0))
      = ∑ h ∈ box2nz H, ∑ m ∈ box2 (0 : ℤ) (M : ℤ),
        (if h 0 * m 0 + h 1 * m 1 = n then (1 : ℕ) else 0) from
    Finset.sum_product (box2nz H) (box2 (0 : ℤ) (M : ℤ))
      (fun i : (Fin 2 → ℤ) × (Fin 2 → ℤ) =>
        if i.1 0 * i.2 0 + i.1 1 * i.2 1 = n then (1 : ℕ) else 0)]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.card_filter]

/-- **零点的界**：`q₇(0) ≤ 4H(H+1)(M+1)`（`h ≠ 0` 时每个纤维 ≤ `M+1`）。 -/
theorem Q7_zero_le (H M : ℕ) : Q7 H M 0 ≤ 4 * H * (H + 1) * (M + 1) := by
  classical
  rw [Q7_eq_sum_fiber]
  have hterm : ∀ h ∈ box2nz H,
      ((box2 (0 : ℤ) (M : ℤ)).filter
        (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = 0)).card ≤ M + 1 := by
    intro h hh
    have hne : h ≠ 0 := (mem_box2nz.mp hh).1
    have hb := fiber_le_gcd hne M 0
    refine le_trans hb ?_
    have hle : M / max (prim h 0).natAbs (prim h 1).natAbs ≤ M := Nat.div_le_self M _
    omega
  calc (∑ h ∈ box2nz H,
        ((box2 (0 : ℤ) (M : ℤ)).filter
          (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = 0)).card)
      ≤ ∑ _h ∈ box2nz H, (M + 1) := Finset.sum_le_sum hterm
    _ = (box2nz H).card * (M + 1) := by
        rw [Finset.sum_const]
        simp
    _ = 4 * H * (H + 1) * (M + 1) := by rw [card_box2nz]

/-- **`q₇` 的对称性**：`q₇(−n) = q₇(n)`。 -/
theorem Q7_neg (H M : ℕ) (n : ℤ) : Q7 H M (-n) = Q7 H M n := by
  classical
  unfold Q7
  set B : Finset (Fin 2 → ℤ) := box2nz H with hB
  set C : Finset (Fin 2 → ℤ) := box2 (0 : ℤ) (M : ℤ) with hC
  have hBneg : ∀ x ∈ B, -x ∈ B := by
    intro x hx
    rw [hB] at hx ⊢
    exact neg_mem_box2nz hx
  have hmap : ∀ x ∈ (B.product C).filter
      (fun x : (Fin 2 → ℤ) × (Fin 2 → ℤ) => x.1 0 * x.2 0 + x.1 1 * x.2 1 = -n),
      negFst x ∈ (B.product C).filter
        (fun x : (Fin 2 → ℤ) × (Fin 2 → ℤ) => x.1 0 * x.2 0 + x.1 1 * x.2 1 = n) := by
    intro x hx
    obtain ⟨x1, x2⟩ := x
    rw [Finset.mem_filter] at hx
    obtain ⟨hxS, hxeq⟩ := hx
    have hx1 : x1 ∈ B := ((Finset.mem_product).mp hxS).1
    have hx2 : x2 ∈ C := ((Finset.mem_product).mp hxS).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨hBneg x1 hx1, hx2⟩, ?_⟩
    simp only [negFst, Pi.neg_apply] at hxeq ⊢
    linarith
  refine Finset.card_bij (fun x _ => negFst x) hmap ?_ ?_
  · intro x _ y _ hxy
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only [negFst, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have : x1 = y1 := by
      funext i
      have := congrFun h1 i
      simp only [Pi.neg_apply] at this
      omega
    rw [this, h2]
  · intro y hy
    obtain ⟨y1, y2⟩ := y
    rw [Finset.mem_filter] at hy
    obtain ⟨hyS, hyeq⟩ := hy
    have hy1 : y1 ∈ B := ((Finset.mem_product).mp hyS).1
    have hy2 : y2 ∈ C := ((Finset.mem_product).mp hyS).2
    refine ⟨(-y1, y2), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨hBneg y1 hy1, hy2⟩, ?_⟩
      simp only [Pi.neg_apply] at hyeq ⊢
      linarith
    · simp [negFst]

/-! ## Fubini：`Σ_n q₇(n)²` 等于四元计数 -/

/-- `q₇` 的索引盒子。 -/
noncomputable def Pbox7 (H M : ℕ) : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (box2nz H).product (box2 (0 : ℤ) (M : ℤ))

/-- `q₇` 是 `Pbox7` 的水平层。 -/
theorem Q7_eq_Pbox7 (H M : ℕ) (n : ℤ) :
    Q7 H M n = ((Pbox7 H M).filter (fun p => Aval p = n)).card := rfl

/-- `Pbox7` 里 `|Aval p| ≤ 2HM`。 -/
theorem Aval_bound7 {H M : ℕ} {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)} (hp : p ∈ Pbox7 H M) :
    |Aval p| ≤ 2 * (H : ℤ) * (M : ℤ) := by
  have hp1 : p.1 ∈ box2nz H := (Finset.mem_product.mp hp).1
  have hp2 : p.2 ∈ box2 (0 : ℤ) (M : ℤ) := (Finset.mem_product.mp hp).2
  rw [mem_box2nz] at hp1
  rw [box2, Fintype.mem_piFinset] at hp2
  have hb1 : |p.1 0| ≤ (H : ℤ) := hp1.2 0
  have hb2 : |p.1 1| ≤ (H : ℤ) := hp1.2 1
  have hb3 : |p.2 0| ≤ (M : ℤ) := by
    have := Finset.mem_Icc.mp (hp2 0)
    rw [abs_of_nonneg this.1]; exact this.2
  have hb4 : |p.2 1| ≤ (M : ℤ) := by
    have := Finset.mem_Icc.mp (hp2 1)
    rw [abs_of_nonneg this.1]; exact this.2
  unfold Aval
  calc |p.1 0 * p.2 0 + p.1 1 * p.2 1|
      ≤ |p.1 0 * p.2 0| + |p.1 1 * p.2 1| := abs_add_le _ _
    _ = |p.1 0| * |p.2 0| + |p.1 1| * |p.2 1| := by rw [abs_mul, abs_mul]
    _ ≤ (H : ℤ) * (M : ℤ) + (H : ℤ) * (M : ℤ) := by
        have h1 := mul_le_mul hb1 hb3 (abs_nonneg _) (by positivity : (0:ℤ) ≤ H)
        have h2 := mul_le_mul hb2 hb4 (abs_nonneg _) (by positivity : (0:ℤ) ≤ H)
        linarith
    _ = 2 * (H : ℤ) * (M : ℤ) := by ring

/-- 两个 `Pbox7` 块的和为零的计数。 -/
noncomputable def count7 (H M : ℕ) : ℕ :=
  (((Pbox7 H M).product (Pbox7 H M)).filter (fun pq => Aval pq.1 + Aval pq.2 = 0)).card

/-- **Fubini 分解**：`count7 = Σ_n q₇(n)·q₇(−n)`。 -/
theorem count7_eq_sum (H M : ℕ) :
    count7 H M = ∑ n ∈ Finset.Icc (-(2 * (H : ℤ) * (M : ℤ))) (2 * (H : ℤ) * (M : ℤ)),
      Q7 H M n * Q7 H M (-n) := by
  classical
  have hstep1 : count7 H M = ∑ p ∈ Pbox7 H M, Q7 H M (-(Aval p)) := by
    rw [count7, Finset.card_filter]
    rw [show (∑ i ∈ (Pbox7 H M).product (Pbox7 H M),
        (if Aval i.1 + Aval i.2 = 0 then (1 : ℕ) else 0))
        = ∑ p ∈ Pbox7 H M, ∑ q ∈ Pbox7 H M,
            (if Aval p + Aval q = 0 then (1 : ℕ) else 0) from
      Finset.sum_product (Pbox7 H M) (Pbox7 H M)
        (fun i => if Aval i.1 + Aval i.2 = 0 then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl ?_
    intro p _
    have hc : (Pbox7 H M).filter (fun q => Aval p + Aval q = 0)
        = (Pbox7 H M).filter (fun q => Aval q = -(Aval p)) := by
      apply Finset.filter_congr
      intro q _
      constructor <;> intro h <;> linarith
    rw [← Finset.card_filter, hc, ← Q7_eq_Pbox7]
  rw [hstep1]
  have hpoint : ∀ p ∈ Pbox7 H M, Q7 H M (-(Aval p))
      = ∑ n ∈ Finset.Icc (-(2 * (H : ℤ) * (M : ℤ))) (2 * (H : ℤ) * (M : ℤ)),
          (if Aval p = n then Q7 H M (-n) else 0) := by
    intro p hp
    rw [Finset.sum_ite_eq]
    rw [if_pos]
    · rw [Finset.mem_Icc]
      have h := Aval_bound7 hp
      rw [abs_le] at h
      exact h
  rw [Finset.sum_congr rfl (fun p hp => hpoint p hp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [← Q7_eq_Pbox7]
  push_cast
  ring

/-- `count7 = Σ_n q₇(n)²`。 -/
theorem count7_eq_sum_sq (H M : ℕ) :
    count7 H M = ∑ n ∈ Finset.Icc (-(2 * (H : ℤ) * (M : ℤ))) (2 * (H : ℤ) * (M : ℤ)),
      Q7 H M n ^ 2 := by
  rw [count7_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [Q7_neg]
  ring

/-! ## 四元盒子：`hᵢ ≠ 0` -/

/-- `hᵢ ∈ [−H,H]\{0}` 的四元盒子。 -/
noncomputable def hBox7 (H : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0)

/-- `mᵢ ∈ [0,M]` 的四元盒子。 -/
noncomputable def mBox7 (M : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (0 : ℤ) (M : ℤ))

/-- Lemma 7 的左端。 -/
noncomputable def hmCount7 (H M : ℕ) : ℕ :=
  (((hBox7 H).product (mBox7 M)).filter
    (fun hm => (∑ i : Fin 4, hm.1 i * hm.2 i) = 0)).card

/-- `hBox7` 的成员刻画。 -/
theorem mem_hBox7 {H : ℕ} {h : Fin 4 → ℤ} :
    h ∈ hBox7 H ↔ ∀ i, h i ≠ 0 ∧ -(H : ℤ) ≤ h i ∧ h i ≤ (H : ℤ) := by
  rw [hBox7, Fintype.mem_piFinset]
  constructor
  · intro hh i
    have hi := hh i
    rw [Finset.mem_erase, Finset.mem_Icc] at hi
    exact ⟨hi.1, hi.2.1, hi.2.2⟩
  · intro hh i
    rw [Finset.mem_erase, Finset.mem_Icc]
    exact ⟨(hh i).1, (hh i).2.1, (hh i).2.2⟩

/-- `mBox7` 的成员刻画。 -/
theorem mem_mBox7 {M : ℕ} {m : Fin 4 → ℤ} :
    m ∈ mBox7 M ↔ ∀ i, (0 : ℤ) ≤ m i ∧ m i ≤ (M : ℤ) := by
  rw [mBox7, Fintype.mem_piFinset]
  constructor
  · intro hh i
    exact Finset.mem_Icc.mp (hh i)
  · intro hh i
    exact Finset.mem_Icc.mpr (hh i)

/-- `split4` 把 `hBox7` 的两半送回 `box2nz`。 -/
theorem split4_mem_box2nz {H : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ hBox7 H) :
    (split4 h).1 ∈ box2nz H ∧ (split4 h).2 ∈ box2nz H := by
  have hh' := mem_hBox7.mp hh
  constructor
  · rw [mem_box2nz]
    refine ⟨?_, ?_⟩
    · intro h0
      have h00 : (split4 h).1 0 = 0 := by rw [h0]; rfl
      simp only [split4] at h00
      exact (hh' 0).1 h00
    · intro i
      have h1 : (split4 h).1 i = h ⟨i.val, by omega⟩ := rfl
      rw [h1, abs_le]
      exact ⟨(hh' _).2.1, (hh' _).2.2⟩
  · rw [mem_box2nz]
    refine ⟨?_, ?_⟩
    · intro h0
      have h20 : (split4 h).2 0 = 0 := by rw [h0]; rfl
      simp only [split4] at h20
      exact (hh' 2).1 h20
    · intro i
      have h1 : (split4 h).2 i = h ⟨i.val + 2, by omega⟩ := rfl
      rw [h1, abs_le]
      exact ⟨(hh' _).2.1, (hh' _).2.2⟩

/-- `split4` 把 `mBox7` 的两半送回 `box2`。 -/
theorem split4_mem_box2 {M : ℕ} {m : Fin 4 → ℤ} (hm : m ∈ mBox7 M) :
    (split4 m).1 ∈ box2 (0 : ℤ) (M : ℤ) ∧ (split4 m).2 ∈ box2 (0 : ℤ) (M : ℤ) := by
  have hm' := mem_mBox7.mp hm
  constructor
  · rw [box2, Fintype.mem_piFinset]
    intro i
    have h1 : (split4 m).1 i = m ⟨i.val, by omega⟩ := rfl
    rw [Finset.mem_Icc, h1]
    exact hm' _
  · rw [box2, Fintype.mem_piFinset]
    intro i
    have h1 : (split4 m).2 i = m ⟨i.val + 2, by omega⟩ := rfl
    rw [Finset.mem_Icc, h1]
    exact hm' _

/-- **对接**：`hmCount7 ≤ count7`。 -/
theorem hmCount7_le_count7 (H M : ℕ) : hmCount7 H M ≤ count7 H M := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun hm : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      (((split4 hm.1).1, (split4 hm.2).1), ((split4 hm.1).2, (split4 hm.2).2))) ?_ ?_
  · intro hm hhm
    rw [Finset.mem_coe, Finset.mem_filter] at hhm
    obtain ⟨hhmS, hhm0⟩ := hhm
    have hh : hm.1 ∈ hBox7 H := ((Finset.mem_product).mp hhmS).1
    have hm2 : hm.2 ∈ mBox7 M := ((Finset.mem_product).mp hhmS).2
    obtain ⟨hA, hB⟩ := split4_mem_box2nz hh
    obtain ⟨mA, mB⟩ := split4_mem_box2 hm2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hA, mA⟩,
      Finset.mem_product.mpr ⟨hB, mB⟩⟩, ?_⟩
    obtain ⟨e1, e2⟩ := split4_fst_val hm.1
    obtain ⟨e3, e4⟩ := split4_fst_val hm.2
    obtain ⟨e5, e6⟩ := split4_snd_val hm.1
    obtain ⟨e7, e8⟩ := split4_snd_val hm.2
    simp only [Aval, e1, e2, e3, e4, e5, e6, e7, e8]
    have hsum := hhm0
    rw [sum_fin4] at hsum
    linarith
  · intro x _ y _ hxy
    obtain ⟨h1, m1⟩ := x
    obtain ⟨h2, m2⟩ := y
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨⟨hh1, hm1⟩, hh2, hm2⟩ := hxy
    have hsp1 : split4 h1 = split4 h2 := Prod.ext hh1 hh2
    have hsp2 : split4 m1 = split4 m2 := Prod.ext hm1 hm2
    rw [split4_injective hsp1, split4_injective hsp2]

/-! ## 常数账：正半边 `Σ_{1≤n≤2HM} q₇(n)² ≤ 1408·(HM)³` -/

/-- `A = 4H(H+1) ≤ 8H²`（`H ≥ 1`）。 -/
theorem le_four_mul (H : ℕ) (hH : 1 ≤ H) :
    (4 : ℚ) * (H : ℚ) * ((H : ℚ) + 1) ≤ 8 * (H : ℚ) ^ 2 := by
  have h : (1 : ℚ) ≤ (H : ℚ) := by exact_mod_cast hH
  nlinarith

/-- **正半边的界**：`Σ_{n=1}^{2HM} q₇(n)² ≤ 1408·(HM)³`（`1 ≤ H ≤ M`）。 -/
theorem sum_Q7_sq_pos_le (H M : ℕ) (hH : 1 ≤ H) (hHM : H ≤ M) :
    (∑ n ∈ Finset.Icc (1 : ℤ) ((2 * H * M : ℕ) : ℤ), ((Q7 H M n : ℚ)) ^ 2)
      ≤ 1408 * ((H : ℚ) * (M : ℚ)) ^ 3 := by
  classical
  set K : ℕ := 2 * H * M with hK
  set A : ℚ := 4 * (H : ℚ) * ((H : ℚ) + 1) with hA
  set B : ℚ := 8 * (H : ℚ) * (M : ℚ) with hB
  have hA0 : (0 : ℚ) ≤ A := by rw [hA]; positivity
  have hB0 : (0 : ℚ) ≤ B := by rw [hB]; positivity
  have hHq : (1 : ℚ) ≤ (H : ℚ) := by exact_mod_cast hH
  have hHMq : (H : ℚ) ≤ (M : ℚ) := by exact_mod_cast hHM
  have hM0 : (0 : ℚ) ≤ (M : ℚ) := by positivity
  have hKQ : (K : ℚ) = 2 * (H : ℚ) * (M : ℚ) := by
    rw [hK]; push_cast; ring
  have hA_le : A ≤ 8 * (H : ℚ) ^ 2 := by rw [hA]; exact le_four_mul H hH
  have hA2 : A ^ 2 ≤ 64 * (H : ℚ) ^ 4 := by
    have h := pow_le_pow_left₀ hA0 hA_le 2
    calc A ^ 2 ≤ (8 * (H : ℚ) ^ 2) ^ 2 := h
      _ = 64 * (H : ℚ) ^ 4 := by ring
  -- 1) 逐项用 Lemma 3
  have hbound : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q7 H M n : ℚ)) ^ 2)
      ≤ ∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hq : (Q7 H M n : ℚ) ≤ A + B * sigmaMinusOne n.natAbs := by
      rw [hA, hB]
      exact Q7_le_sigma H M hn0
    exact pow_le_pow_left₀ (by positivity) hq 2
  -- 2) 展开
  have hexp : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), (A + B * sigmaMinusOne n.natAbs) ^ 2)
      = (K : ℚ) * A ^ 2
        + 2 * A * B * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs)
        + B ^ 2 * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2) := by
    have hpt : ∀ n : ℤ, (A + B * sigmaMinusOne n.natAbs) ^ 2
        = A ^ 2 + 2 * A * B * sigmaMinusOne n.natAbs
          + B ^ 2 * sigmaMinusOne n.natAbs ^ 2 := fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hpt n)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcardK : ((Finset.Icc (1 : ℤ) (K : ℤ)).card : ℚ) = (K : ℚ) := by
      rw [Int.card_Icc]
      simp
    have e1 : (∑ _n ∈ Finset.Icc (1 : ℤ) (K : ℤ), A ^ 2) = (K : ℚ) * A ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcardK]
    have e2 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), 2 * A * B * sigmaMinusOne n.natAbs)
        = 2 * A * B * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs) := by
      rw [Finset.mul_sum]
    have e3 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), B ^ 2 * sigmaMinusOne n.natAbs ^ 2)
        = B ^ 2 * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2) := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3]
  -- 3) Lemma 6 的两条界
  have hs1 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs) ≤ 2 * (K : ℚ) := by
    rw [sum_int_Icc_eq_sum_nat_Icc K (fun m => sigmaMinusOne m)]
    exact sum_sigmaMinusOne_le K
  have hs2 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2) ≤ 6 * (K : ℚ) := by
    rw [sum_int_Icc_eq_sum_nat_Icc K (fun m => sigmaMinusOne m ^ 2)]
    exact sum_sigmaMinusOne_sq_le K
  -- 4) 代入
  have hm1 : 2 * A * B * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs)
      ≤ 2 * A * B * (2 * (K : ℚ)) :=
    mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hm2 : B ^ 2 * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2)
      ≤ B ^ 2 * (6 * (K : ℚ)) :=
    mul_le_mul_of_nonneg_left hs2 (by positivity)
  have hK0 : (0 : ℚ) ≤ (K : ℚ) := by positivity
  -- 5) 常数账
  have hb1 : (K : ℚ) * A ^ 2 ≤ 128 * (H : ℚ) ^ 5 * (M : ℚ) := by
    have h1 : (K : ℚ) * A ^ 2 ≤ (K : ℚ) * (64 * (H : ℚ) ^ 4) :=
      mul_le_mul_of_nonneg_left hA2 hK0
    have h2 : (K : ℚ) * (64 * (H : ℚ) ^ 4) = 128 * (H : ℚ) ^ 5 * (M : ℚ) := by
      rw [hKQ]; ring
    linarith [h1, h2.le, h2.ge]
  have hmul1 : A * B ≤ (8 * (H : ℚ) ^ 2) * (8 * (H : ℚ) * (M : ℚ)) :=
    mul_le_mul hA_le le_rfl hB0 (by positivity)
  have hb2 : 2 * A * B * (2 * (K : ℚ)) ≤ 512 * (H : ℚ) ^ 4 * (M : ℚ) ^ 2 := by
    have h1 : A * B * (K : ℚ) ≤ (8 * (H : ℚ) ^ 2 * (8 * (H : ℚ) * (M : ℚ)))
        * (2 * (H : ℚ) * (M : ℚ)) := by
      rw [hKQ]
      exact mul_le_mul hmul1 le_rfl (by positivity) (by positivity)
    have h2 : (8 * (H : ℚ) ^ 2 * (8 * (H : ℚ) * (M : ℚ))) * (2 * (H : ℚ) * (M : ℚ))
        = 128 * (H : ℚ) ^ 4 * (M : ℚ) ^ 2 := by ring
    nlinarith [h1, h2]
  have hb3 : B ^ 2 * (6 * (K : ℚ)) = 768 * (H : ℚ) ^ 3 * (M : ℚ) ^ 3 := by
    rw [hB, hKQ]; ring
  have hsq : (H : ℚ) ^ 2 ≤ (M : ℚ) ^ 2 := by nlinarith
  have h5 : (H : ℚ) ^ 5 * (M : ℚ) ≤ (H : ℚ) ^ 3 * (M : ℚ) ^ 3 := by
    calc (H : ℚ) ^ 5 * (M : ℚ) = (H : ℚ) ^ 2 * ((H : ℚ) ^ 3 * (M : ℚ)) := by ring
      _ ≤ (M : ℚ) ^ 2 * ((H : ℚ) ^ 3 * (M : ℚ)) := by
          apply mul_le_mul_of_nonneg_right hsq
          positivity
      _ = (H : ℚ) ^ 3 * (M : ℚ) ^ 3 := by ring
  have h4 : (H : ℚ) ^ 4 * (M : ℚ) ^ 2 ≤ (H : ℚ) ^ 3 * (M : ℚ) ^ 3 := by
    calc (H : ℚ) ^ 4 * (M : ℚ) ^ 2 = (H : ℚ) * ((H : ℚ) ^ 3 * (M : ℚ) ^ 2) := by ring
      _ ≤ (M : ℚ) * ((H : ℚ) ^ 3 * (M : ℚ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right hHMq
          positivity
      _ = (H : ℚ) ^ 3 * (M : ℚ) ^ 3 := by ring
  have htarget : (K : ℚ) * A ^ 2 + 2 * A * B * (2 * (K : ℚ)) + B ^ 2 * (6 * (K : ℚ))
      ≤ 1408 * ((H : ℚ) * (M : ℚ)) ^ 3 := by
    have h1 : (128 : ℚ) * (H : ℚ) ^ 5 * (M : ℚ) ≤ 128 * ((H : ℚ) * (M : ℚ)) ^ 3 := by
      have := mul_le_mul_of_nonneg_left h5 (by norm_num : (0:ℚ) ≤ 128)
      calc 128 * (H : ℚ) ^ 5 * (M : ℚ) = 128 * ((H : ℚ) ^ 5 * (M : ℚ)) := by ring
        _ ≤ 128 * ((H : ℚ) ^ 3 * (M : ℚ) ^ 3) := this
        _ = 128 * ((H : ℚ) * (M : ℚ)) ^ 3 := by ring
    have h2 : (512 : ℚ) * (H : ℚ) ^ 4 * (M : ℚ) ^ 2 ≤ 512 * ((H : ℚ) * (M : ℚ)) ^ 3 := by
      have := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℚ) ≤ 512)
      calc 512 * (H : ℚ) ^ 4 * (M : ℚ) ^ 2 = 512 * ((H : ℚ) ^ 4 * (M : ℚ) ^ 2) := by ring
        _ ≤ 512 * ((H : ℚ) ^ 3 * (M : ℚ) ^ 3) := this
        _ = 512 * ((H : ℚ) * (M : ℚ)) ^ 3 := by ring
    have h3 : (768 : ℚ) * (H : ℚ) ^ 3 * (M : ℚ) ^ 3 = 768 * ((H : ℚ) * (M : ℚ)) ^ 3 := by ring
    linarith [hb1, hb2, hb3, h1, h2, h3]
  calc (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q7 H M n : ℚ)) ^ 2)
      ≤ ∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), (A + B * sigmaMinusOne n.natAbs) ^ 2 := hbound
    _ = (K : ℚ) * A ^ 2
        + 2 * A * B * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs)
        + B ^ 2 * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2) := hexp
    _ ≤ (K : ℚ) * A ^ 2 + 2 * A * B * (2 * (K : ℚ)) + B ^ 2 * (6 * (K : ℚ)) := by
        linarith [hm1, hm2]
    _ ≤ 1408 * ((H : ℚ) * (M : ℚ)) ^ 3 := htarget

/-! ## 主定理 -/

/-- **Lemma 7（Jameson，本项目版本）**：`1 ≤ H ≤ M` 时
`#{(h,m) : hᵢ ∈ [−H,H]\{0}, mᵢ ∈ [0,M], Σ hᵢmᵢ = 0} ≤ 5250·(HM)³`。 -/
theorem hmCount7_le (H M : ℕ) (hH : 1 ≤ H) (hHM : H ≤ M) :
    hmCount7 H M ≤ 5250 * (H * M) ^ 3 := by
  classical
  set K : ℕ := 2 * H * M with hK
  have hKZ : (K : ℤ) = 2 * (H : ℤ) * (M : ℤ) := by
    rw [hK]; push_cast; ring
  have hHq : (1 : ℚ) ≤ (H : ℚ) := by exact_mod_cast hH
  have hHMq : (H : ℚ) ≤ (M : ℚ) := by exact_mod_cast hHM
  have hM0 : (0 : ℚ) ≤ (M : ℚ) := by positivity
  -- 对称拆分
  have h1 : (count7 H M : ℚ)
      = ((Q7 H M 0 : ℚ)) ^ 2
        + 2 * ∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q7 H M n : ℚ)) ^ 2 := by
    rw [count7_eq_sum_sq, ← hKZ]
    have hnat := sum_Icc_symm_eq (K : ℤ) (by positivity)
      (fun n => Q7 H M n ^ 2) (fun n => by rw [Q7_neg])
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hnat
    push_cast at hcast
    push_cast
    exact hcast
  -- 零项
  have h0 : ((Q7 H M 0 : ℚ)) ^ 2 ≤ 256 * ((H : ℚ) * (M : ℚ)) ^ 3 := by
    have hz : (Q7 H M 0 : ℚ) ≤ 16 * (H : ℚ) ^ 2 * (M : ℚ) := by
      have h1 : (Q7 H M 0 : ℚ) ≤ ((4 * H * (H + 1) * (M + 1) : ℕ) : ℚ) := by
        exact_mod_cast Q7_zero_le H M
      refine le_trans h1 ?_
      push_cast
      have hH1 : (H : ℚ) + 1 ≤ 2 * (H : ℚ) := by linarith
      have hM1 : (M : ℚ) + 1 ≤ 2 * (M : ℚ) := by linarith [le_trans hHq hHMq]
      have hH0 : (0 : ℚ) ≤ (H : ℚ) := by linarith
      have hstep1 : (4 : ℚ) * (H : ℚ) * ((H : ℚ) + 1) ≤ 4 * (H : ℚ) * (2 * (H : ℚ)) := by
        have := mul_le_mul (le_refl ((4 : ℚ) * (H : ℚ))) hH1 (by linarith) (by linarith)
        simpa [mul_assoc] using this
      have hstep2 : (4 : ℚ) * (H : ℚ) * ((H : ℚ) + 1) * ((M : ℚ) + 1)
          ≤ (4 * (H : ℚ) * (2 * (H : ℚ))) * (2 * (M : ℚ)) :=
        mul_le_mul hstep1 hM1 (by linarith) (by positivity)
      calc (4 : ℚ) * (H : ℚ) * ((H : ℚ) + 1) * ((M : ℚ) + 1)
          ≤ (4 * (H : ℚ) * (2 * (H : ℚ))) * (2 * (M : ℚ)) := hstep2
        _ = 16 * (H : ℚ) ^ 2 * (M : ℚ) := by ring
    calc ((Q7 H M 0 : ℚ)) ^ 2 ≤ (16 * (H : ℚ) ^ 2 * (M : ℚ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hz 2
      _ = 256 * (H : ℚ) ^ 4 * (M : ℚ) ^ 2 := by ring
      _ ≤ 256 * ((H : ℚ) * (M : ℚ)) ^ 3 := by
          have h4 : (H : ℚ) ^ 4 * (M : ℚ) ^ 2 ≤ (H : ℚ) ^ 3 * (M : ℚ) ^ 3 := by
            calc (H : ℚ) ^ 4 * (M : ℚ) ^ 2
                = (H : ℚ) * ((H : ℚ) ^ 3 * (M : ℚ) ^ 2) := by ring
              _ ≤ (M : ℚ) * ((H : ℚ) ^ 3 * (M : ℚ) ^ 2) := by
                  apply mul_le_mul_of_nonneg_right hHMq
                  positivity
              _ = (H : ℚ) ^ 3 * (M : ℚ) ^ 3 := by ring
          have h := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℚ) ≤ 256)
          calc 256 * (H : ℚ) ^ 4 * (M : ℚ) ^ 2
              = 256 * ((H : ℚ) ^ 4 * (M : ℚ) ^ 2) := by ring
            _ ≤ 256 * ((H : ℚ) ^ 3 * (M : ℚ) ^ 3) := h
            _ = 256 * ((H : ℚ) * (M : ℚ)) ^ 3 := by ring
  -- 汇总
  have h3 := sum_Q7_sq_pos_le H M hH hHM
  have hfin : (count7 H M : ℚ) ≤ ((5250 * (H * M) ^ 3 : ℕ) : ℚ) := by
    push_cast
    calc (count7 H M : ℚ)
        = ((Q7 H M 0 : ℚ)) ^ 2
          + 2 * ∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q7 H M n : ℚ)) ^ 2 := h1
      _ ≤ 256 * ((H : ℚ) * (M : ℚ)) ^ 3 + 2 * (1408 * ((H : ℚ) * (M : ℚ)) ^ 3) := by
          linarith [h0, h3]
      _ ≤ 5250 * ((H : ℚ) * (M : ℚ)) ^ 3 := by
          have hnn : (0 : ℚ) ≤ ((H : ℚ) * (M : ℚ)) ^ 3 := by positivity
          linarith
  have hmono : hmCount7 H M ≤ count7 H M := hmCount7_le_count7 H M
  have hfin' : (hmCount7 H M : ℚ) ≤ ((5250 * (H * M) ^ 3 : ℕ) : ℚ) := by
    have hc : (hmCount7 H M : ℚ) ≤ (count7 H M : ℚ) := by exact_mod_cast hmono
    linarith
  exact_mod_cast hfin'

/-- `H = 0` 的平凡情形：盒子为空。 -/
theorem hmCount7_zero_left (M : ℕ) : hmCount7 0 M = 0 := by
  classical
  have hbox : hBox7 0 = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨h, hh⟩
    have h0 := (mem_hBox7.mp hh) 0
    have hmem : h 0 ∈ Finset.Icc (-(0 : ℤ)) (0 : ℤ) := by
      rw [Finset.mem_Icc]
      exact ⟨h0.2.1, h0.2.2⟩
    rw [Finset.mem_Icc] at hmem
    exact h0.1 (by omega : h 0 = 0)
  rw [hmCount7, hbox]
  simp

/-- **Lemma 7（Jameson，本项目版本，`H ≤ M` 无下界）**：`H ≤ M` 时
`#{(h,m) : hᵢ ∈ [−H,H]\{0}, mᵢ ∈ [0,M], Σ hᵢmᵢ = 0} ≤ 5250·(HM)³`。 -/
theorem hmCount7_le' (H M : ℕ) (hHM : H ≤ M) :
    hmCount7 H M ≤ 5250 * (H * M) ^ 3 := by
  rcases Nat.eq_zero_or_pos H with hH0 | hHpos
  · subst hH0
    rw [hmCount7_zero_left]
    simp
  · exact hmCount7_le H M hHpos hHM

end Waring
