/- GID: D5/S3/Arith/Additive/Waring/WaringCount
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringCount.lean#L1-L732
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.SuccPred

open Finset

namespace Waring

/-- `hᵢ` 的取值范围 `[−N, N]`。 -/
noncomputable def hBox (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) (N : ℤ))

/-- `mᵢ` 的取值范围 `[0, 2N]`。 -/
noncomputable def mBox (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (0 : ℤ) (2 * (N : ℤ)))

/-- `(p, q) ↦ (p − q, p + q)`。 -/
def toHM (N : ℕ) (pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1))) :
    (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
  (fun i => (pq.1 i : ℤ) - (pq.2 i : ℤ), fun i => (pq.1 i : ℤ) + (pq.2 i : ℤ))

/-- `Fin 2 → ℤ` 的盒子 `[lo, hi]²`。 -/
noncomputable def box2 (lo hi : ℤ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 2 => Finset.Icc lo hi)

/-- 二元部分和：`h₁m₁ + h₂m₂ = n` 在 `[−H,H]² × [0,M]²` 中的解数。 -/
noncomputable def Q (H M : ℕ) (n : ℤ) : ℕ :=
  (((box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ))).filter
    (fun x : (Fin 2 → ℤ) × (Fin 2 → ℤ) => x.1 0 * x.2 0 + x.1 1 * x.2 1 = n)).card

/-- 取反 `h` 分量。 -/
def negFst : (Fin 2 → ℤ) × (Fin 2 → ℤ) → (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  fun x => (-x.1, x.2)

/-- 部分和的「和函数」。 -/
def Aval (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : ℤ := p.1 0 * p.2 0 + p.1 1 * p.2 1

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

/-- `σ₋₁(n) = Σ_{d | n} 1/d`。 -/
noncomputable def sigmaMinusOne (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, (1 : ℚ) / (d : ℚ)

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
theorem card_multiples (x d : ℕ) :
    ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card = x / d := by
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := Finset.Icc_succ_left_eq_Ioc 0 x
  rw [hIcc]
  exact Nat.Ioc_filter_dvd_card_eq_div x d

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
    intro d _
    rw [card_multiples x d]
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
theorem card_multiples_two (x a b : ℕ) :
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
  exact card_multiples x (Nat.lcm a b)

/-- `max a b ≤ lcm a b`（`a, b ≥ 1`）——用于把 `1/lcm` 换成 `1/max`。 -/
theorem max_le_lcm {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : max a b ≤ Nat.lcm a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact Nat.le_of_dvd (Nat.lcm_pos ha hb) (Nat.dvd_lcm_right a b)
  · rw [max_eq_left h]
    exact Nat.le_of_dvd (Nat.lcm_pos ha hb) (Nat.dvd_lcm_left a b)

end Waring
