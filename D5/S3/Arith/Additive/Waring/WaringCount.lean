/- GID: D5/S3/Arith/Additive/Waring/WaringCount
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringCount.lean#L1-L732
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringCircle

/-!
# Lemma 8 的组合核心：从平方和到 `Σ hᵢmᵢ = 0`

`WaringCircle.integral_normSq_pow_four` 把 `k = 2` 的八次矩化成了计数

```text
sqEqCount N = #{(p, q) : (Fin 4 → Fin (N+1))² | Σ pᵢ² = Σ qᵢ²}.
```

本文件做 Jameson Lemma 8 的第一步：换变量

```text
hᵢ = pᵢ − qᵢ   (ℤ, |hᵢ| ≤ N)
mᵢ = pᵢ + qᵢ   (ℕ, 0 ≤ mᵢ ≤ 2N)
```

因为 `pᵢ² − qᵢ² = hᵢmᵢ`，方程 `Σ pᵢ² = Σ qᵢ²` 变成 `Σ hᵢmᵢ = 0`，而且
`(p, q) ↦ (h, m)` 是单射（`p = (m+h)/2`，`q = (m−h)/2`）。于是

```lean
theorem sqEqCount_le_hmCount (N : ℕ) : sqEqCount N ≤ hmCount N
```

文件末尾给出 Lemma 7b 的第一块：二元线性方程的解数界（Jameson Lemma 2）。
-/

open Finset

namespace Waring

/-- 八元组「平方和相等」的计数（与 `integral_normSq_pow_four` 的右边一致）。 -/
noncomputable def sqEqCount (N : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)))).filter
    (fun pq => (∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2) = (∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2))).card

/-- 矩等式与 `sqEqCount` 的对接。 -/
theorem integral_normSq_pow_four_eq (N : ℕ) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (theta N α)) ^ 4) = (sqEqCount N : ℝ) := by
  rw [integral_normSq_pow_four]
  rfl

/-- `hᵢ` 的取值范围 `[−N, N]`。 -/
noncomputable def hBox (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) (N : ℤ))

/-- `mᵢ` 的取值范围 `[0, 2N]`。 -/
noncomputable def mBox (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (0 : ℤ) (2 * (N : ℤ)))

/-- `(h, m)` 形式的计数：`Σ hᵢmᵢ = 0`。 -/
noncomputable def hmCount (N : ℕ) : ℕ :=
  (((hBox N).product (mBox N)).filter
    (fun hm => (∑ i : Fin 4, hm.1 i * hm.2 i) = 0)).card

/-- `(p, q) ↦ (p − q, p + q)`。 -/
def toHM (N : ℕ) (pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1))) :
    (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
  (fun i => (pq.1 i : ℤ) - (pq.2 i : ℤ), fun i => (pq.1 i : ℤ) + (pq.2 i : ℤ))

/-- **换变量**：平方和相等的计数不超过 `(h, m)` 的计数。 -/
theorem sqEqCount_le_hmCount (N : ℕ) : sqEqCount N ≤ hmCount N := by
  classical
  refine Finset.card_le_card_of_injOn (toHM N) ?_ ?_
  · -- 像落在 `(h, m)` 的计数集合里
    intro pq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hpq
    obtain ⟨-, hpq⟩ := hpq
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have h1 : (fun i => (pq.1 i : ℤ) - (pq.2 i : ℤ)) ∈ hBox N := by
        rw [hBox, Fintype.mem_piFinset]
        intro i
        have h1' : (0 : ℤ) ≤ (pq.1 i : ℤ) := Int.natCast_nonneg _
        have h2' : (pq.2 i : ℤ) ≤ (N : ℤ) := by
          have := (pq.2 i).isLt
          exact_mod_cast (Nat.lt_succ_iff.mp this)
        have h3' : (0 : ℤ) ≤ (pq.2 i : ℤ) := Int.natCast_nonneg _
        have h4' : (pq.1 i : ℤ) ≤ (N : ℤ) := by
          have := (pq.1 i).isLt
          exact_mod_cast (Nat.lt_succ_iff.mp this)
        rw [Finset.mem_Icc]
        constructor <;> linarith
      have h2 : (fun i => (pq.1 i : ℤ) + (pq.2 i : ℤ)) ∈ mBox N := by
        rw [mBox, Fintype.mem_piFinset]
        intro i
        have h1' : (0 : ℤ) ≤ (pq.1 i : ℤ) := Int.natCast_nonneg _
        have h2' : (pq.1 i : ℤ) ≤ (N : ℤ) := by
          have := (pq.1 i).isLt
          exact_mod_cast (Nat.lt_succ_iff.mp this)
        have h3' : (0 : ℤ) ≤ (pq.2 i : ℤ) := Int.natCast_nonneg _
        have h4' : (pq.2 i : ℤ) ≤ (N : ℤ) := by
          have := (pq.2 i).isLt
          exact_mod_cast (Nat.lt_succ_iff.mp this)
        rw [Finset.mem_Icc]
        constructor <;> linarith
      exact Finset.mem_product.mpr ⟨h1, h2⟩
    · have hsq : ∀ i : Fin 4, ((pq.1 i : ℤ) - (pq.2 i : ℤ)) * ((pq.1 i : ℤ) + (pq.2 i : ℤ))
          = (pq.1 i : ℤ) ^ 2 - (pq.2 i : ℤ) ^ 2 := by
        intro i; ring
      show (∑ i : Fin 4, ((pq.1 i : ℤ) - (pq.2 i : ℤ)) * ((pq.1 i : ℤ) + (pq.2 i : ℤ))) = 0
      rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_sub_distrib]
      have hcast : ((∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2 : ℕ) : ℤ)
          = ∑ i : Fin 4, (pq.1 i : ℤ) ^ 2 := by push_cast; ring
      have hcast2 : ((∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2 : ℕ) : ℤ)
          = ∑ i : Fin 4, (pq.2 i : ℤ) ^ 2 := by push_cast; ring
      rw [← hcast, ← hcast2, hpq]
      ring
  · -- 单射性
    intro pq _ pq' _ heq
    simp only [toHM, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hp : pq.1 = pq'.1 := by
      funext i
      have h1i := congrFun h1 i
      have h2i := congrFun h2 i
      have h : (pq.1 i : ℤ) = (pq'.1 i : ℤ) := by linarith
      omega
    have hq : pq.2 = pq'.2 := by
      funext i
      have h1i := congrFun h1 i
      have h2i := congrFun h2 i
      have h : (pq.2 i : ℤ) = (pq'.2 i : ℤ) := by linarith
      omega
    exact Prod.ext hp hq

/-! ## Lemma 2：二元线性方程的解数 -/

/-- **Lemma 2**（Jameson）：固定 `b ≠ 0` 时，`a m₁ + b m₂ = n` 在盒子
`[-M, M]²` 中的解数不超过 `2M + 1`。 -/
theorem pair_solution_le {a b : ℤ} (hb : b ≠ 0) (M : ℕ) (n : ℤ) :
    (((Finset.Icc (-(M : ℤ)) (M : ℤ)).product
        (Finset.Icc (-(M : ℤ)) (M : ℤ))).filter
      (fun mm : ℤ × ℤ => a * mm.1 + b * mm.2 = n)).card ≤ 2 * M + 1 := by
  classical
  set S : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(M : ℤ)) (M : ℤ)).product (Finset.Icc (-(M : ℤ)) (M : ℤ)) with hS
  set sol : Finset (ℤ × ℤ) :=
    S.filter (fun mm : ℤ × ℤ => a * mm.1 + b * mm.2 = n) with hsol
  have hsub : sol ⊆ S := Finset.filter_subset _ _
  have hinj : Set.InjOn Prod.fst (sol : Set (ℤ × ℤ)) := by
    intro x hx y hy hxy
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    have hxeq : a * x1 + b * x2 = n := (Finset.mem_filter.mp hx).2
    have hyeq : a * y1 + b * y2 = n := (Finset.mem_filter.mp hy).2
    have h1 : x1 = y1 := hxy
    have h2 : x2 = y2 := by
      rw [h1] at hxeq
      have : b * x2 = b * y2 := by linarith
      exact mul_left_cancel₀ hb this
    rw [h1, h2]
  have hmaps : Set.MapsTo Prod.fst (sol : Set (ℤ × ℤ)) ↑(Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
    intro x hx
    obtain ⟨x1, x2⟩ := x
    have hxS : (x1, x2) ∈ S := hsub hx
    exact (Finset.mem_product.mp hxS).1
  have hcard := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
  rw [hsol]
  refine le_trans hcard ?_
  rw [Int.card_Icc]
  have h1 : (M : ℤ) + 1 - (-(M : ℤ)) = 2 * (M : ℤ) + 1 := by ring
  rw [h1]
  omega

/-! ## 二元部分和 `Q`：Lemma 3 的载体 -/

/-- `Fin 2 → ℤ` 的盒子 `[lo, hi]²`。 -/
noncomputable def box2 (lo hi : ℤ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 2 => Finset.Icc lo hi)

/-- 二元部分和：`h₁m₁ + h₂m₂ = n` 在 `[−H,H]² × [0,M]²` 中的解数。 -/
noncomputable def Q (H M : ℕ) (n : ℤ) : ℕ :=
  (((box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ))).filter
    (fun x : (Fin 2 → ℤ) × (Fin 2 → ℤ) => x.1 0 * x.2 0 + x.1 1 * x.2 1 = n)).card

/-- `Q` 的平凡界：解数不超过盒子的总大小。 -/
theorem Q_le_card (H M : ℕ) (n : ℤ) :
    Q H M n ≤ (2 * H + 1) ^ 2 * (M + 1) ^ 2 := by
  classical
  unfold Q
  refine le_trans (Finset.card_filter_le _ _) ?_
  have hcard : ((box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ))).card
      = (box2 (-(H : ℤ)) (H : ℤ)).card * (box2 (0 : ℤ) (M : ℤ)).card :=
    Finset.card_product _ _
  rw [hcard]
  have h1 : (box2 (-(H : ℤ)) (H : ℤ)).card = (2 * H + 1) ^ 2 := by
    rw [box2, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Int.card_Icc]
    have : (H : ℤ) + 1 - (-(H : ℤ)) = 2 * (H : ℤ) + 1 := by ring
    rw [this]
    omega
  have h2 : (box2 (0 : ℤ) (M : ℤ)).card = (M + 1) ^ 2 := by
    rw [box2, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Int.card_Icc]
    have : (M : ℤ) + 1 - 0 = (M : ℤ) + 1 := by ring
    rw [this]
    omega
  rw [h1, h2]

/-- 取反 `h` 分量。 -/
def negFst : (Fin 2 → ℤ) × (Fin 2 → ℤ) → (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  fun x => (-x.1, x.2)

/-- **`Q` 的对称性**：`Q(−n) = Q(n)`（把 `h` 换成 `−h`）。 -/
theorem Q_neg (H M : ℕ) (n : ℤ) : Q H M (-n) = Q H M n := by
  classical
  unfold Q
  set B : Finset (Fin 2 → ℤ) := box2 (-(H : ℤ)) (H : ℤ) with hB
  set C : Finset (Fin 2 → ℤ) := box2 (0 : ℤ) (M : ℤ) with hC
  have hBneg : ∀ x ∈ B, -x ∈ B := by
    intro x hx
    rw [hB, box2, Fintype.mem_piFinset] at hx
    rw [hB, box2, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi := hx i
    rw [Finset.mem_Icc] at hi
    constructor <;> simp only [Pi.neg_apply] <;> linarith
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
    simp only [negFst, Prod.fst, Prod.snd, Pi.neg_apply] at hxeq ⊢
    linarith
  refine Finset.card_bij (fun x _ => negFst x) hmap ?_ ?_
  · -- 单射
    intro x _ y _ hxy
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
  · -- 满射
    intro y hy
    obtain ⟨y1, y2⟩ := y
    rw [Finset.mem_filter] at hy
    obtain ⟨hyS, hyeq⟩ := hy
    have hy1 : y1 ∈ B := ((Finset.mem_product).mp hyS).1
    have hy2 : y2 ∈ C := ((Finset.mem_product).mp hyS).2
    refine ⟨(-y1, y2), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨hBneg y1 hy1, hy2⟩, ?_⟩
      simp only [Prod.fst, Prod.snd, Pi.neg_apply] at hyeq ⊢
      linarith
    · simp [negFst]

/-- **`Q` 的支撑**：`|n| > 2HM` 时方程无解。 -/
theorem Q_eq_zero {H M : ℕ} {n : ℤ} (hn : 2 * (H : ℤ) * (M : ℤ) < |n|) : Q H M n = 0 := by
  classical
  unfold Q
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  have hx1 : x.1 ∈ box2 (-(H : ℤ)) (H : ℤ) := ((Finset.mem_product).mp hx).1
  have hx2 : x.2 ∈ box2 (0 : ℤ) (M : ℤ) := ((Finset.mem_product).mp hx).2
  rw [box2, Fintype.mem_piFinset] at hx1 hx2
  have hb1 : |x.1 0| ≤ (H : ℤ) := by
    have := Finset.mem_Icc.mp (hx1 0); rw [abs_le]; exact this
  have hb2 : |x.1 1| ≤ (H : ℤ) := by
    have := Finset.mem_Icc.mp (hx1 1); rw [abs_le]; exact this
  have hb3 : |x.2 0| ≤ (M : ℤ) := by
    have := Finset.mem_Icc.mp (hx2 0)
    rw [abs_of_nonneg this.1]; exact this.2
  have hb4 : |x.2 1| ≤ (M : ℤ) := by
    have := Finset.mem_Icc.mp (hx2 1)
    rw [abs_of_nonneg this.1]; exact this.2
  intro heq
  have hbound : |x.1 0 * x.2 0 + x.1 1 * x.2 1| ≤ 2 * (H : ℤ) * (M : ℤ) := by
    calc |x.1 0 * x.2 0 + x.1 1 * x.2 1|
        ≤ |x.1 0 * x.2 0| + |x.1 1 * x.2 1| := abs_add_le _ _
      _ = |x.1 0| * |x.2 0| + |x.1 1| * |x.2 1| := by rw [abs_mul, abs_mul]
      _ ≤ (H : ℤ) * (M : ℤ) + (H : ℤ) * (M : ℤ) := by
          have h1 := mul_le_mul hb1 hb3 (abs_nonneg _) (by positivity : (0:ℤ) ≤ H)
          have h2 := mul_le_mul hb2 hb4 (abs_nonneg _) (by positivity : (0:ℤ) ≤ H)
          linarith
      _ = 2 * (H : ℤ) * (M : ℤ) := by ring
  rw [heq] at hbound
  linarith

/-! ## Fubini 分解：`hmCount = Σ_n Q(n)·Q(−n)` -/

/-- 部分和的「和函数」。 -/
def Aval (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : ℤ := p.1 0 * p.2 0 + p.1 1 * p.2 1

/-- 盒子 `[−N,N]² × [0,2N]²`。 -/
noncomputable def Pbox (N : ℕ) : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (box2 (-(N : ℤ)) (N : ℤ)).product (box2 (0 : ℤ) ((2 * N : ℕ) : ℤ))

/-- `Q` 就是盒子里的水平层。 -/
theorem Q_eq_Pbox (N : ℕ) (n : ℤ) :
    Q N (2 * N) n = ((Pbox N).filter (fun p => Aval p = n)).card := rfl

/-- **Fubini 形式**的 `(h,m)` 计数：`A(p) + A(q) = 0`。 -/
noncomputable def hmCount2 (N : ℕ) : ℕ :=
  (((Pbox N).product (Pbox N)).filter (fun pq => Aval pq.1 + Aval pq.2 = 0)).card

/-- `Aval` 的界：`|Aval p| ≤ 4N²`。 -/
theorem Aval_bound {N : ℕ} {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)} (hp : p ∈ Pbox N) :
    |Aval p| ≤ 4 * (N : ℤ) ^ 2 := by
  have hp1 : p.1 ∈ box2 (-(N : ℤ)) (N : ℤ) := ((Finset.mem_product).mp hp).1
  have hp2 : p.2 ∈ box2 (0 : ℤ) ((2 * N : ℕ) : ℤ) := ((Finset.mem_product).mp hp).2
  rw [box2, Fintype.mem_piFinset] at hp1 hp2
  have hb1 : |p.1 0| ≤ (N : ℤ) := by
    have := Finset.mem_Icc.mp (hp1 0); rw [abs_le]; exact this
  have hb2 : |p.1 1| ≤ (N : ℤ) := by
    have := Finset.mem_Icc.mp (hp1 1); rw [abs_le]; exact this
  have hb3 : |p.2 0| ≤ (2 * N : ℕ) := by
    have := Finset.mem_Icc.mp (hp2 0)
    rw [abs_of_nonneg this.1]; exact_mod_cast this.2
  have hb4 : |p.2 1| ≤ (2 * N : ℕ) := by
    have := Finset.mem_Icc.mp (hp2 1)
    rw [abs_of_nonneg this.1]; exact_mod_cast this.2
  have hb3' : |p.2 0| ≤ 2 * (N : ℤ) := by push_cast at hb3 ⊢; linarith
  have hb4' : |p.2 1| ≤ 2 * (N : ℤ) := by push_cast at hb4 ⊢; linarith
  unfold Aval
  calc |p.1 0 * p.2 0 + p.1 1 * p.2 1|
      ≤ |p.1 0 * p.2 0| + |p.1 1 * p.2 1| := abs_add_le _ _
    _ = |p.1 0| * |p.2 0| + |p.1 1| * |p.2 1| := by rw [abs_mul, abs_mul]
    _ ≤ (N : ℤ) * (2 * (N : ℤ)) + (N : ℤ) * (2 * (N : ℤ)) := by
        have h1 := mul_le_mul hb1 hb3' (abs_nonneg _) (by positivity : (0:ℤ) ≤ N)
        have h2 := mul_le_mul hb2 hb4' (abs_nonneg _) (by positivity : (0:ℤ) ≤ N)
        linarith
    _ = 4 * (N : ℤ) ^ 2 := by ring

/-- **Fubini 分解**：`hmCount2 N = Σ_n Q(n)·Q(−n)`。 -/
theorem hmCount2_eq_sum (N : ℕ) :
    hmCount2 N = ∑ n ∈ Finset.Icc (-(4 * (N : ℤ) ^ 2)) (4 * (N : ℤ) ^ 2),
      Q N (2 * N) n * Q N (2 * N) (-n) := by
  classical
  -- 第一步：内层化为 `Q(−A p)`
  have hstep1 : hmCount2 N = ∑ p ∈ Pbox N, Q N (2 * N) (-(Aval p)) := by
    rw [hmCount2, Finset.card_filter]
    rw [show (∑ i ∈ (Pbox N).product (Pbox N),
        (if Aval i.1 + Aval i.2 = 0 then (1 : ℕ) else 0))
        = ∑ p ∈ Pbox N, ∑ q ∈ Pbox N,
            (if Aval p + Aval q = 0 then (1 : ℕ) else 0) from
      Finset.sum_product (Pbox N) (Pbox N)
        (fun i => if Aval i.1 + Aval i.2 = 0 then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl ?_
    intro p _
    have hc : (Pbox N).filter (fun q => Aval p + Aval q = 0)
        = (Pbox N).filter (fun q => Aval q = -(Aval p)) := by
      apply Finset.filter_congr
      intro q _
      constructor <;> intro h <;> linarith
    rw [← Finset.card_filter, hc, ← Q_eq_Pbox]
  rw [hstep1]
  -- 第二步：把 `Q(−A p)` 按 `n = A p` 展开
  have hpoint : ∀ p ∈ Pbox N, Q N (2 * N) (-(Aval p))
      = ∑ n ∈ Finset.Icc (-(4 * (N : ℤ) ^ 2)) (4 * (N : ℤ) ^ 2),
          (if Aval p = n then Q N (2 * N) (-n) else 0) := by
    intro p hp
    rw [Finset.sum_ite_eq]
    rw [if_pos]
    · rw [Finset.mem_Icc]
      have h := Aval_bound hp
      rw [abs_le] at h
      exact h
  rw [Finset.sum_congr rfl (fun p hp => hpoint p hp)]
  rw [Finset.sum_comm]
  -- 内层：`Σ_{p ∈ P} (if A p = n then Q(−n) else 0) = Q(n)·Q(−n)`
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [← Q_eq_Pbox]
  push_cast
  ring

/-- 用 `Q_neg` 把 `Q(−n)` 换成 `Q(n)`：`hmCount2 = Σ_n Q(n)²`。 -/
theorem hmCount2_eq_sum_sq (N : ℕ) :
    hmCount2 N = ∑ n ∈ Finset.Icc (-(4 * (N : ℤ) ^ 2)) (4 * (N : ℤ) ^ 2),
      Q N (2 * N) n ^ 2 := by
  rw [hmCount2_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [Q_neg]
  ring

/-! ## 与 `hmCount` 的对接：拆 `Fin 4` -/

/-- 把 `Fin 4 → ℤ` 拆成两半。 -/
def split4 (h : Fin 4 → ℤ) : (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  (fun i => h ⟨i.val, by omega⟩, fun i => h ⟨i.val + 2, by omega⟩)

/-- `split4` 是单射。 -/
theorem split4_injective : Function.Injective split4 := by
  intro h h' hh
  have h1 := congrFun (congrArg Prod.fst hh)
  have h2 := congrFun (congrArg Prod.snd hh)
  funext j
  rcases Nat.lt_or_ge j.val 2 with hj | hj
  · have hh1 := h1 ⟨j.val, hj⟩
    simp only [split4] at hh1
    convert hh1 using 2 <;> exact Fin.ext rfl
  · have hh2 := h2 ⟨j.val - 2, by omega⟩
    simp only [split4] at hh2
    convert hh2 using 2 <;> (exact Fin.ext (by simp; omega))

/-- `Fin 4` 上的求和展开成四个坐标之和。 -/
theorem sum_fin4 (f : Fin 4 → ℤ) :
    (∑ j : Fin 4, f j) = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ]
  ring

/-- 拆开后前两个坐标就是 `0, 1`。 -/
theorem split4_fst_val (h : Fin 4 → ℤ) :
    (split4 h).1 0 = h 0 ∧ (split4 h).1 1 = h 1 := by
  constructor <;> rfl

/-- 拆开后后两个坐标就是 `2, 3`。 -/
theorem split4_snd_val (h : Fin 4 → ℤ) :
    (split4 h).2 0 = h 2 ∧ (split4 h).2 1 = h 3 := by
  constructor <;> rfl

/-- **对接**：`hmCount ≤ hmCount2`。 -/
theorem hmCount_le_hmCount2 (N : ℕ) : hmCount N ≤ hmCount2 N := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun hm : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      (((split4 hm.1).1, (split4 hm.2).1), ((split4 hm.1).2, (split4 hm.2).2))) ?_ ?_
  · -- 像落在 `hmCount2` 的集合里
    intro hm hhm
    rw [Finset.mem_coe, Finset.mem_filter] at hhm
    obtain ⟨hhmS, hhm0⟩ := hhm
    have hh1 : hm.1 ∈ hBox N := ((Finset.mem_product).mp hhmS).1
    have hh2 : hm.2 ∈ mBox N := ((Finset.mem_product).mp hhmS).2
    rw [hBox, Fintype.mem_piFinset] at hh1
    rw [mBox, Fintype.mem_piFinset] at hh2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · -- `(hA, mA) ∈ Pbox N`
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh1 ⟨i.val, by omega⟩
        simpa [split4] using this
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh2 ⟨i.val, by omega⟩
        simpa [split4] using this
    · -- `(hB, mB) ∈ Pbox N`
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh1 ⟨i.val + 2, by omega⟩
        simpa [split4] using this
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh2 ⟨i.val + 2, by omega⟩
        simpa [split4] using this
    · -- `Aval` 条件
      obtain ⟨e1, e2⟩ := split4_fst_val hm.1
      obtain ⟨e3, e4⟩ := split4_fst_val hm.2
      obtain ⟨e5, e6⟩ := split4_snd_val hm.1
      obtain ⟨e7, e8⟩ := split4_snd_val hm.2
      simp only [Aval, e1, e2, e3, e4, e5, e6, e7, e8]
      have hsum := hhm0
      rw [sum_fin4] at hsum
      linarith
  · -- 单射性
    intro x _ y _ hxy
    obtain ⟨h1, m1⟩ := x
    obtain ⟨h2, m2⟩ := y
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨⟨hh1, hm1⟩, hh2, hm2⟩ := hxy
    have hsp1 : split4 h1 = split4 h2 := Prod.ext hh1 hh2
    have hsp2 : split4 m1 = split4 m2 := Prod.ext hm1 hm2
    rw [split4_injective hsp1, split4_injective hsp2]

/-- **汇总**：`sqEqCount ≤ Σ_n Q(n)²`（`k = 2` 的 Theorem 1 的组合核心）。 -/
theorem sqEqCount_le_sum_Q_sq (N : ℕ) :
    sqEqCount N ≤ ∑ n ∈ Finset.Icc (-(4 * (N : ℤ) ^ 2)) (4 * (N : ℤ) ^ 2),
      Q N (2 * N) n ^ 2 :=
  calc sqEqCount N ≤ hmCount N := sqEqCount_le_hmCount N
    _ ≤ hmCount2 N := hmCount_le_hmCount2 N
    _ = _ := hmCount2_eq_sum_sq N

/-! ## `σ₋₁`：Lemma 3 与 Lemma 6 的载体 -/

/-- `σ₋₁(n) = Σ_{d | n} 1/d`。 -/
noncomputable def sigmaMinusOne (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, (1 : ℚ) / (d : ℚ)

/-- `σ₋₁(1) = 1`。 -/
theorem sigmaMinusOne_one : sigmaMinusOne 1 = 1 := by
  unfold sigmaMinusOne
  simp

/-- 每一项都 `≤ 1`，所以 `σ₋₁(n) ≤ d(n)`（约数个数）。 -/
theorem sigmaMinusOne_le_card (n : ℕ) : sigmaMinusOne n ≤ (n.divisors.card : ℚ) := by
  unfold sigmaMinusOne
  calc ∑ d ∈ n.divisors, (1 : ℚ) / (d : ℚ)
      ≤ ∑ _d ∈ n.divisors, (1 : ℚ) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hd1 : (1 : ℚ) ≤ (d : ℚ) := by
          have : 0 < d := Nat.pos_of_mem_divisors hd
          exact_mod_cast this
        have hd0 : (0 : ℚ) < (d : ℚ) := by linarith
        rw [div_le_one hd0]
        exact hd1
    _ = (n.divisors.card : ℚ) := by simp

/-- `σ₋₁(n) > 0`（`n ≥ 1`）。 -/
theorem sigmaMinusOne_pos {n : ℕ} (hn : n ≠ 0) : 0 < sigmaMinusOne n := by
  unfold sigmaMinusOne
  have hmem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn
  have hnonneg : ∀ d ∈ n.divisors, (0 : ℚ) ≤ (1 : ℚ) / (d : ℚ) := by
    intro d hd
    have : (0 : ℚ) < (d : ℚ) := by
      have hpos : 0 < d := Nat.pos_of_mem_divisors hd
      exact_mod_cast hpos
    positivity
  exact Finset.sum_pos' hnonneg ⟨1, hmem, by norm_num⟩

/-- `σ₋₁(n) ≤ n`（`n ≥ 1`）。 -/
theorem sigmaMinusOne_le_self {n : ℕ} (hn : n ≠ 0) : sigmaMinusOne n ≤ (n : ℚ) := by
  refine le_trans (sigmaMinusOne_le_card n) ?_
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    refine Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, ?_⟩
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)
  have hcard : n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
  have hIcc : (Finset.Icc 1 n).card = n := by
    have := Nat.card_Icc 1 n
    omega
  rw [hIcc] at hcard
  exact_mod_cast hcard

/-- `Σ_{d=1}^{x} 1/d² ≤ 2 - 1/x`（归纳：`1/(x+1)² ≤ 1/x − 1/(x+1)`）。 -/
theorem sum_inv_sq_le (x : ℕ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 x, (1 : ℚ) / (d : ℚ) ^ 2) ≤ 2 - 1 / (x : ℚ) := by
  induction x with
  | zero => omega
  | succ x ih =>
    rcases Nat.eq_zero_or_pos x with hx0 | hxpos
    · subst hx0
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ x + 1)]
      have hih := ih (by omega : 1 ≤ x)
      have hx' : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hxpos
      have hkey : (1 : ℚ) / ((x : ℚ) + 1) ^ 2 ≤ 1 / (x : ℚ) - 1 / ((x : ℚ) + 1) := by
        have h1 : (x : ℚ) ≠ 0 := hx'.ne'
        have h2 : (x : ℚ) + 1 ≠ 0 := by positivity
        field_simp
        nlinarith
      have hcast : ((x + 1 : ℕ) : ℚ) = (x : ℚ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- `σ₋₁(n)` 写成 `Icc 1 n` 上的 filter 求和。 -/
theorem sigmaMinusOne_eq_sum_Icc {n : ℕ} (hn : n ≠ 0) :
    sigmaMinusOne n = ∑ d ∈ Finset.Icc 1 n, (if d ∣ n then (1 : ℚ) / (d : ℚ) else 0) := by
  unfold sigmaMinusOne
  have hdiv : n.divisors = (Finset.Icc 1 n).filter (fun d => d ∣ n) := by
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, -⟩
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hnpos, Nat.le_of_dvd hnpos hdvd⟩, hdvd⟩
    · rintro ⟨⟨-, -⟩, hdvd⟩
      exact ⟨hdvd, hn⟩
  rw [hdiv, Finset.sum_filter]

/-- `Σ_{d=1}^{x} 1/d² ≤ 2`。 -/
theorem sum_inv_sq_le_two (x : ℕ) :
    (∑ d ∈ Finset.Icc 1 x, (1 : ℚ) / (d : ℚ) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · simp [hx]
  · have h := sum_inv_sq_le x hx
    have hpos : (0 : ℚ) ≤ 1 / (x : ℚ) := by positivity
    linarith

/-- `[1,x]` 中 `d` 的倍数恰有 `x / d` 个。 -/
theorem card_multiples (x d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card = x / d := by
  classical
  set S := (Finset.Icc 1 x).filter (fun n => d ∣ n) with hS
  have hinj : Set.InjOn (fun n => n / d) (S : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    change n₁ / d = n₂ / d at heq
    rw [hS, Finset.mem_coe, Finset.mem_filter] at hn₁ hn₂
    obtain ⟨-, hd₁⟩ := hn₁
    obtain ⟨-, hd₂⟩ := hn₂
    rw [← Nat.div_mul_cancel hd₁, ← Nat.div_mul_cancel hd₂, heq]
  have himg : S.image (fun n => n / d) = Finset.Icc 1 (x / d) := by
    ext m
    rw [Finset.mem_image]
    simp only [hS, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨n, ⟨⟨hn1, hnx⟩, hdvd⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd
      · exact Nat.div_le_div_right hnx
    · rintro ⟨hm1, hmx⟩
      refine ⟨d * m, ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩, ?_⟩
      · calc 1 ≤ d := hd
          _ ≤ d * m := Nat.le_mul_of_pos_right d (by omega : 0 < m)
      · calc d * m ≤ d * (x / d) := Nat.mul_le_mul_left d hmx
          _ ≤ x := Nat.mul_div_le x d
      · exact Nat.mul_div_cancel_left m hd
  rw [← Finset.card_image_of_injOn hinj, himg, Nat.card_Icc]
  exact Nat.add_sub_cancel _ _

/-- **交换求和**：`Σ_{n≤x} σ₋₁(n) = Σ_{d≤x} (1/d)·#{n≤x : d∣n}`。 -/
theorem sum_sigmaMinusOne_eq (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, sigmaMinusOne n)
      = ∑ d ∈ Finset.Icc 1 x, (1 : ℚ) / (d : ℚ)
          * (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℚ) := by
  classical
  have h1 : ∀ n ∈ Finset.Icc 1 x, sigmaMinusOne n
      = ∑ d ∈ Finset.Icc 1 x, (if d ∣ n then (1 : ℚ) / (d : ℚ) else 0) := by
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [sigmaMinusOne_eq_sum_Icc hn0]
    refine Finset.sum_subset ?_ ?_
    · intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (Finset.mem_Icc.mp hn).2⟩
    · intro d hdx hdn
      rw [Finset.mem_Icc] at hdx
      have hnlt : n < d := by
        by_contra hle
        exact hdn (Finset.mem_Icc.mpr ⟨hdx.1, by omega⟩)
      rw [if_neg]
      intro hdvd
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  rw [Finset.sum_congr rfl (fun n hn => h1 n hn)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **`Σ_{n≤x} σ₋₁(n) ≤ 2x`**（交叉项估计）。 -/
theorem sum_sigmaMinusOne_le (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, sigmaMinusOne n) ≤ 2 * (x : ℚ) := by
  classical
  rw [sum_sigmaMinusOne_eq]
  have h1 : ∀ d ∈ Finset.Icc 1 x,
      (1 : ℚ) / (d : ℚ) * (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℚ)
        ≤ (1 : ℚ) / (d : ℚ) * ((x : ℚ) / (d : ℚ)) := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    rw [card_multiples x d hd0]
    have hle : (((x / d : ℕ) : ℚ)) ≤ (x : ℚ) / (d : ℚ) := Nat.cast_div_le
    have hnonneg : (0 : ℚ) ≤ 1 / (d : ℚ) := by positivity
    exact mul_le_mul_of_nonneg_left hle hnonneg
  calc (∑ d ∈ Finset.Icc 1 x,
        (1 : ℚ) / (d : ℚ) * (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℚ))
      ≤ ∑ d ∈ Finset.Icc 1 x, (1 : ℚ) / (d : ℚ) * ((x : ℚ) / (d : ℚ)) :=
        Finset.sum_le_sum h1
    _ = (x : ℚ) * ∑ d ∈ Finset.Icc 1 x, (1 : ℚ) / (d : ℚ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro d _
        field_simp
    _ ≤ (x : ℚ) * 2 := by
        have h := sum_inv_sq_le_two x
        have hx : (0 : ℚ) ≤ (x : ℚ) := by positivity
        exact mul_le_mul_of_nonneg_left h hx
    _ = 2 * (x : ℚ) := by ring

/-- `σ₋₁(n)²` 展开成 `n.divisors` 上的双重和（Lemma 6 平方版的入口）。 -/
theorem sigmaMinusOne_sq_eq (n : ℕ) :
    sigmaMinusOne n ^ 2
      = ∑ a ∈ n.divisors, ∑ b ∈ n.divisors, (1 : ℚ) / ((a : ℚ) * (b : ℚ)) := by
  unfold sigmaMinusOne
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  field_simp

/-- `[1,x]` 中同时被 `a` 与 `b` 整除的数恰有 `x / lcm(a,b)` 个。 -/
theorem card_multiples_two (x a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((Finset.Icc 1 x).filter (fun n => a ∣ n ∧ b ∣ n)).card = x / Nat.lcm a b := by
  have hcongr : (Finset.Icc 1 x).filter (fun n => a ∣ n ∧ b ∣ n)
      = (Finset.Icc 1 x).filter (fun n => Nat.lcm a b ∣ n) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · rintro ⟨h1, h2⟩
      exact Nat.lcm_dvd h1 h2
    · intro h
      exact ⟨Nat.dvd_trans (Nat.dvd_lcm_left a b) h, Nat.dvd_trans (Nat.dvd_lcm_right a b) h⟩
  rw [hcongr]
  exact card_multiples x (Nat.lcm a b) (Nat.lcm_pos ha hb)

/-- `max a b ≤ lcm a b`（`a, b ≥ 1`）——用于把 `1/lcm` 换成 `1/max`。 -/
theorem max_le_lcm {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : max a b ≤ Nat.lcm a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact Nat.le_of_dvd (Nat.lcm_pos ha hb) (Nat.dvd_lcm_right a b)
  · rw [max_eq_left h]
    exact Nat.le_of_dvd (Nat.lcm_pos ha hb) (Nat.dvd_lcm_left a b)

/-- `1/lcm(a,b) ≤ 1/max(a,b)`（`a, b ≥ 1`）。 -/
theorem inv_lcm_le_inv_max {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (1 : ℚ) / (Nat.lcm a b : ℚ) ≤ 1 / (max a b : ℚ) := by
  have h1 : (0 : ℚ) < (max a b : ℚ) := by
    have hpos : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
    exact_mod_cast hpos
  have h3 : (max a b : ℚ) ≤ (Nat.lcm a b : ℚ) := by
    exact_mod_cast max_le_lcm ha hb
  exact one_div_le_one_div_of_le h1 h3

end Waring
