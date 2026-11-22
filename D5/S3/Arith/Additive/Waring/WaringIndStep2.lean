/- GID: D5/S3/Arith/Additive/Waring/WaringIndStep2
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringIndStep2.lean#L1004-L1776
   Modified for this repository. Local imports use their D5 module paths.
   This file contains one segment of a split upstream module.
   Inactive commented proof drafts are omitted.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringIndStep2Counting

open Finset intervalIntegral

namespace Waring

/-- 由 `a d ≠ 0` 与系数界得 `1 ≤ c`。 -/
theorem one_le_c {a : ℕ → ℤ} {d c N : ℕ} (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) : 1 ≤ c := by
  have h := ha d le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at h
  have h1 : (1 : ℤ) ≤ |a d| := abs_pos.mpr had
  have h2 : (1 : ℤ) ≤ (c : ℤ) := le_trans h1 h
  exact_mod_cast h2

/-- `1 ≤ coeffConst c d`（`c ≥ 1`，`d ≥ 1`）。 -/
theorem coeffConst_pos {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) : 1 ≤ coeffConst c d := by
  unfold coeffConst
  have h0 : (0 : ℕ) ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  have h00 : (0 : ℕ) ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have hinner : (1 : ℕ) ≤ ∑ j ∈ Finset.range (d + 1), Nat.choose j 0 := by
    have hle : Nat.choose 0 0 ≤ ∑ j ∈ Finset.range (d + 1), Nat.choose j 0 :=
      Finset.single_le_sum (f := fun j => Nat.choose j 0) (fun i _ => by positivity) h00
    simpa using hle
  have houter : (1 : ℕ) ≤ ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), Nat.choose j r := by
    have hle : (∑ j ∈ Finset.range (d + 1), Nat.choose j 0)
        ≤ ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), Nat.choose j r :=
      Finset.single_le_sum (f := fun r => ∑ j ∈ Finset.range (d + 1), Nat.choose j r)
        (fun i _ => by positivity) h0
    exact le_trans hinner hle
  calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ c * ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), Nat.choose j r :=
        Nat.mul_le_mul hc houter

/-- `M ≤ Kf c d N`（`1 ≤ c`、`d ≥ 3`、`N ≥ 1`、`M ≤ N`）。 -/
theorem le_Kf {c d N M : ℕ} (hd : 3 ≤ d) (hc : 1 ≤ c) (hN : 1 ≤ N) (hM : M ≤ N) :
    M ≤ Kf c d N := by
  have hC : 1 ≤ coeffConst c d := coeffConst_pos hc (by omega)
  have hCc : 1 ≤ (d + 1) * coeffConst c d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNle : N ≤ N ^ (d - 1) := by
    have h1 : N ^ 1 ≤ N ^ (d - 1) := pow_le_pow_right₀ hN (by omega)
    simpa using h1
  have hcoef : 8 ≤ 2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) := by
    have h1 : 4 ≤ 4 * 8 ^ (d - 3) := by have := one_le_s d; omega
    nlinarith
  unfold Kf
  calc M ≤ N := hM
    _ ≤ N ^ (d - 1) := hNle
    _ ≤ 8 * N ^ (d - 1) := by omega
    _ ≤ (2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d)) * N ^ (d - 1) :=
        Nat.mul_le_mul_right _ hcoef
    _ = 2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) * N ^ (d - 1) := by ring

/-- `QSf a d M h = QSet (polyEval a d) M h (4·8^{d−3})`（缩短记号，控制 `whnf` 开销）。 -/
noncomputable def QSf (a : ℕ → ℤ) (d M : ℕ) (h : ℤ) : Finset ℤ :=
  QSet (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3))

set_option maxHeartbeats 800000 in
/-- 4 层 `QSet` 求和放大到 `K` 盒子（逐层 `Q ↦ Q/h`，**不展开 `QSet`/`Finset.pi`**）。 -/
theorem sum_four_Q_le_MBox {d : ℕ} (hd : 3 ≤ d) (c N M : ℕ) (hNM : M ≤ N)
    (a : ℕ → ℤ) (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j))
    {h1 h2 h3 h4 : ℤ} (hb1 : |h1| ≤ (M : ℤ)) (hb2 : |h2| ≤ (M : ℤ))
    (hb3 : |h3| ≤ (M : ℤ)) (hb4 : |h4| ≤ (M : ℤ))
    (hn1 : h1 ≠ 0) (hn2 : h2 ≠ 0) (hn3 : h3 ≠ 0) (hn4 : h4 ≠ 0) :
    (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      ≤ ∑ m1 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          ∑ m2 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          ∑ m3 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          ∑ m4 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0) := by
  classical
  have hd1 : 1 ≤ d := by omega
  set KB : Finset ℤ := Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ) with hKB
  -- 除法还原：`h * (Q / h) = Q`（`Q ∈ QSet` 时 `h ∣ Q`）
  have hdiv : ∀ (h Q : ℤ), Q ∈ QSf a d M h → h * (Q / h) = Q := by
    intro h Q hQ
    have hd' := QSet_dvd hQ
    calc h * (Q / h) = Q / h * h := by ring
      _ = Q := Int.ediv_mul_cancel hd'
  -- `Q ↦ Q/h` 在 `QSet` 上单射
  have hinj : ∀ (h : ℤ), h ≠ 0 → Set.InjOn (fun Q : ℤ => Q / h) (↑(QSf a d M h) : Set ℤ) := by
    intro h _ Q hQ Q' hQ' heq
    simp only at heq
    calc Q = h * (Q / h) := (hdiv h Q hQ).symm
      _ = h * (Q' / h) := by rw [heq]
      _ = Q' := hdiv h Q' hQ'
  -- 像落在 `K` 盒子
  have hmem : ∀ (h : ℤ), h ≠ 0 → |h| ≤ (M : ℤ) → ∀ Q ∈ QSf a d M h, Q / h ∈ KB := by
    intro h hh0 hhb Q hQ
    rw [hKB, Finset.mem_Icc]
    have hNabs : |h| ≤ (N : ℤ) := le_trans hhb (by exact_mod_cast hNM)
    have hb := QSet_div_abs_le (a := a) (d := d) (c := c) (N := N) (M := M) (h := h)
      (s := 4 * 8 ^ (d - 3)) (Q := Q) hd1 ha hNabs hNM hh0 hQ
    rw [abs_le] at hb
    exact hb
  -- 单层：`∑_{Q ∈ QSet h} F (Q/h) ≤ ∑_{m ∈ KB} F m`
  have step : ∀ (h : ℤ), h ≠ 0 → |h| ≤ (M : ℤ) → ∀ (F : ℤ → ℝ), (∀ Q, 0 ≤ F Q) →
      (∑ Q ∈ QSf a d M h, F (Q / h)) ≤ ∑ m ∈ KB, F m := by
    intro h hh0 hhb F hF
    rw [← Finset.sum_image (f := F) (g := fun Q : ℤ => Q / h) (s := QSf a d M h) (hinj h hh0)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨Q, hQ, rfl⟩ := hm
      exact hmem h hh0 hhb Q hQ
    · intro m _ _; exact hF m
  calc (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 hQ1 => Finset.sum_congr rfl (fun Q2 _ =>
          Finset.sum_congr rfl (fun Q3 _ => Finset.sum_congr rfl (fun Q4 _ => ?_))))
        rw [hdiv h1 Q1 hQ1]
    _ = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + h2 * (Q2 / h2) + Q3 + Q4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 _ => Finset.sum_congr rfl (fun Q2 hQ2 =>
          Finset.sum_congr rfl (fun Q3 _ => Finset.sum_congr rfl (fun Q4 _ => ?_))))
        rw [hdiv h2 Q2 hQ2]
    _ = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + h2 * (Q2 / h2) + h3 * (Q3 / h3) + Q4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 _ => Finset.sum_congr rfl (fun Q2 _ =>
          Finset.sum_congr rfl (fun Q3 hQ3 => Finset.sum_congr rfl (fun Q4 _ => ?_))))
        rw [hdiv h3 Q3 hQ3]
    _ = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + h2 * (Q2 / h2) + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 _ => Finset.sum_congr rfl (fun Q2 _ =>
          Finset.sum_congr rfl (fun Q3 _ => Finset.sum_congr rfl (fun Q4 hQ4 => ?_))))
        rw [hdiv h4 Q4 hQ4]
    _ ≤ (∑ m1 ∈ KB, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * m1 + h2 * (Q2 / h2) + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) :=
        step h1 hn1 hb1 (fun m1 => ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3,
          ∑ Q4 ∈ QSf a d M h4,
          (if h1 * m1 + h2 * (Q2 / h2) + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
            then (1 : ℝ) else 0)) (fun _ => by positivity)
    _ ≤ (∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * m1 + h2 * m2 + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum (fun m1 _ => ?_)
        exact step h2 hn2 hb2 (fun m2 => ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
          (if h1 * m1 + h2 * m2 + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
            then (1 : ℝ) else 0)) (fun _ => by positivity)
    _ ≤ (∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum (fun m1 _ => Finset.sum_le_sum (fun m2 _ => ?_))
        exact step h3 hn3 hb3 (fun m3 => ∑ Q4 ∈ QSf a d M h4,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * (Q4 / h4) = 0
            then (1 : ℝ) else 0)) (fun _ => by positivity)
    _ ≤ (∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
        (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum (fun m1 _ => Finset.sum_le_sum (fun m2 _ =>
          Finset.sum_le_sum (fun m3 _ => ?_)))
        exact step h4 hn4 hb4 (fun m4 => (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0
          then (1 : ℝ) else 0)) (fun _ => by positivity)

set_option maxHeartbeats 1600000 in
/-- **(9c)**：满足 `Q₁+…+Q₄ = 0` 的 `(h,Q)` 四元组计数 ≤ `16·5250·(M·Kf)³`。 -/
theorem count_le {d : ℕ} (hd : 3 ≤ d) (c N M : ℕ) (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hNM : M ≤ N)
    (a : ℕ → ℤ) (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) :
    (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
  classical
  have hc : 1 ≤ c := one_le_c had ha
  have hMK : M ≤ Kf c d N := le_Kf hd hc hN hNM
  set S8 : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0 with hS8
  set KB : Finset ℤ := Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ) with hKB
  -- 第 1 步：4 层 `Q` → 4 层 `m`（逐层 `Q ↦ Q/h`，见 `sum_four_Q_le_MBox`）
  have hstep1 : (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
        ∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
          (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      ≤ ∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
          ∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum (fun h1 hh1 => Finset.sum_le_sum (fun h2 hh2 =>
      Finset.sum_le_sum (fun h3 hh3 => Finset.sum_le_sum (fun h4 hh4 => ?_))))
    obtain ⟨hn1, hI1⟩ := Finset.mem_erase.mp hh1
    obtain ⟨hlo1, hhi1⟩ := Finset.mem_Icc.mp hI1
    obtain ⟨hn2, hI2⟩ := Finset.mem_erase.mp hh2
    obtain ⟨hlo2, hhi2⟩ := Finset.mem_Icc.mp hI2
    obtain ⟨hn3, hI3⟩ := Finset.mem_erase.mp hh3
    obtain ⟨hlo3, hhi3⟩ := Finset.mem_Icc.mp hI3
    obtain ⟨hn4, hI4⟩ := Finset.mem_erase.mp hh4
    obtain ⟨hlo4, hhi4⟩ := Finset.mem_Icc.mp hI4
    have hb1 : |h1| ≤ (M : ℤ) := abs_le.mpr ⟨hlo1, hhi1⟩
    have hb2 : |h2| ≤ (M : ℤ) := abs_le.mpr ⟨hlo2, hhi2⟩
    have hb3 : |h3| ≤ (M : ℤ) := abs_le.mpr ⟨hlo3, hhi3⟩
    have hb4 : |h4| ≤ (M : ℤ) := abs_le.mpr ⟨hlo4, hhi4⟩
    exact sum_four_Q_le_MBox hd c N M hNM a ha hb1 hb2 hb3 hb4 hn1 hn2 hn3 hn4
  refine le_trans hstep1 ?_
  -- 第 2 步：折叠成 `hBox7 M × (KB)⁴` 上的两层求和
  have hstep2 : (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
        ∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0))
      = ∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
          (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0) := by
    rw [show (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
        ∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0))
        = ∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
          ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
            (if h1 * (m 0) + h2 * (m 1) + h3 * (m 2) + h4 * (m 3) = 0 then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl (fun h1 _ => Finset.sum_congr rfl (fun h2 _ =>
        Finset.sum_congr rfl (fun h3 _ => Finset.sum_congr rfl (fun h4 _ => ?_))))
      have key := sum_piFinset_fin4 (S := KB) (F := fun m : Fin 4 → ℤ =>
        (if h1 * (m 0) + h2 * (m 1) + h3 * (m 2) + h4 * (m 3) = 0 then (1 : ℝ) else 0))
      simp only [Fin.isValue, ↓reduceIte] at key
      exact key.symm]
    rw [show hBox7 M = Fintype.piFinset (fun _ : Fin 4 => S8) from rfl]
    have key2 := sum_piFinset_fin4 (S := S8) (F := fun h : Fin 4 → ℤ =>
      ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0))
    simp only [Fin.isValue, ↓reduceIte] at key2
    exact key2.symm
  rw [hstep2]
  -- 第 3 步：两层求和 → `card`（先在 `ℕ` 上做，再提升到 `ℝ`）
  have hstep3nat : (∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℕ) else 0))
      = ((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB)).filter
          (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card := by
    rw [show (∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℕ) else 0))
        = ∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
          (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
            (if p.1 0 * p.2 0 + p.1 1 * p.2 1 + p.1 2 * p.2 2 + p.1 3 * p.2 3 = 0
              then (1 : ℕ) else 0)) (h, m) from rfl]
    rw [← Finset.sum_product (s := hBox7 M) (t := Fintype.piFinset (fun _ : Fin 4 => KB))
      (f := fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
        (if p.1 0 * p.2 0 + p.1 1 * p.2 1 + p.1 2 * p.2 2 + p.1 3 * p.2 3 = 0
          then (1 : ℕ) else 0))]
    have hcf := Finset.card_filter
      (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)
      (hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB))
    have h1 : (∑ x ∈ hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2 + x.1 3 * x.2 3 = 0
          then (1 : ℕ) else 0))
        = ∑ x ∈ hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB),
          (if ∑ i : Fin 4, x.1 i * x.2 i = 0 then (1 : ℕ) else 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      congr 1
      rw [Fin.sum_univ_four]
    rw [h1, ← hcf]
  have hstep3 : (∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0))
      = (((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB)).filter
          (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card : ℝ) := by
    have h := hstep3nat
    exact_mod_cast h
  rw [hstep3]
  -- 第 4 步（9b）+ 第 5 步（Lemma 7）
  have hA : (((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB)).filter
        (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card : ℝ)
      ≤ 16 * (hmCount7 M (Kf c d N) : ℝ) := by
    rw [hKB]
    have h := card_sym_shrink M (Kf c d N)
    exact_mod_cast h
  have hB : (hmCount7 M (Kf c d N) : ℝ) ≤ ((5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hmCount7_le' M (Kf c d N) hMK
  have hfin : (16 * (hmCount7 M (Kf c d N) : ℝ) : ℝ)
      ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
    nlinarith
  exact le_trans hA hfin

/-- 归纳步的显式常数 `R_d(c)`（只依赖 `c`，不依赖 `N`/`M`）。 -/
noncomputable def Rd (d : ℕ) (R₀ : ℕ → ℝ) (c : ℕ) : ℝ :=
  let m := 8 ^ (d - 2)
  let Ck : ℝ := ((2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) : ℕ) : ℝ)
  let Rmax : ℝ := max (R₀ (coeffConst c d)) 1
  2 ^ (4 * (m - 1)) * 8 *
    (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)

set_option maxHeartbeats 2000000 in
/-- **加强版归纳步**：`MeanValueBoundS (d−1) → MeanValueBoundS d`（`d ≥ 3`）。 -/
theorem meanValueBoundS_succ {d : ℕ} (hd : 3 ≤ d) (h : MeanValueBoundS (d - 1)) :
    MeanValueBoundS d := by
  obtain ⟨R₀, hR₀pos, hR₀b⟩ := h
  have hMV : MVSBound (d - 1) R₀ := hR₀b
  refine ⟨fun c => Rd d R₀ c, ?hpos, ?hbound⟩
  · -- `R_d(c) > 0`
    intro c
    have h1 : (0 : ℝ) < max (R₀ (coeffConst c d)) 1 :=
      lt_of_lt_of_le (hR₀pos _) (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ ((2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) : ℕ) : ℝ) := by
      positivity
    show (0 : ℝ) < Rd d R₀ c
    simp only [Rd]
    apply mul_pos
    · exact mul_pos (by positivity) (by norm_num)
    · apply add_pos_of_pos_of_nonneg (by positivity)
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (pow_nonneg (le_of_lt h1) 4)) (by norm_num)) (by norm_num)) (pow_nonneg h2 3)
  · -- 主不等式
    intro c N M hN hM1 hMN a had ha
    have hc : 1 ≤ c := one_le_c had ha
    have hMK : M ≤ Kf c d N := le_Kf hd hc hN hMN
    set m : ℕ := 8 ^ (d - 2) with hm
    set Ck : ℝ := ((2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) : ℕ) : ℝ) with hCk
    set Rmax : ℝ := max (R₀ (coeffConst c d)) 1 with hRmax
    have hRmax0 : 0 < Rmax := by
      rw [hRmax]; exact lt_of_lt_of_le (hR₀pos _) (le_max_left _ _)
    have hmax0 : (0 : ℝ) ≤ max (R₀ (coeffConst c d)) 1 := by
      rw [← hRmax]; exact le_of_lt hRmax0
    have hCk0 : 0 ≤ Ck := by rw [hCk]; positivity
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_pow _ _ (by norm_num)
    -- `Kf = Ck · N^{d−1}`
    have hKf : ((Kf c d N : ℕ) : ℝ) = Ck * (N : ℝ) ^ (d - 1) := by
      rw [hCk]; simp only [Kf]; push_cast; ring
    -- 指数恒等式
    have hmge : d - 1 ≤ m := by
      have h1 : d - 1 < 2 ^ (d - 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (d - 1) ≤ 8 ^ (d - 2) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      rw [hm]; omega
    have hexp1 : 4 * (m - 1) + 4 * (m - (d - 1)) + 3 * d = 8 * m - d := by omega
    have h4md : 4 * m ≤ 8 * m - d := by omega
    -- 计数界（9c）
    have hcount := count_le hd c N M hN hM1 hMN a had ha
    have hcount' : (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
        ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
        ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
        ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
          (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
        ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
      simpa only [QSf] using hcount
    have hfour := four_sum_le_count hd (R₀ := R₀) hMV c N M hN hM1 hMN a had ha
    -- `Count ≤ 16·5250·Ck³·N^{3d}`
    have hCnt : (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ)
        ≤ 16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d) := by
      have hM3 : (M : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hMN' 3
      have hKf3 : ((Kf c d N : ℕ) : ℝ) ^ 3 = Ck ^ 3 * (N : ℝ) ^ (3 * (d - 1)) := by
        rw [hKf, mul_pow, ← pow_mul, Nat.mul_comm]
      have hKeq : (3 : ℕ) * (d - 1) + 3 = 3 * d := by omega
      have hcast : ((5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ)
          = 5250 * ((M : ℝ) ^ 3 * ((Kf c d N : ℕ) : ℝ) ^ 3) := by push_cast; ring
      have hNexp : (N : ℝ) ^ (3 * (d - 1)) * (N : ℝ) ^ 3 = (N : ℝ) ^ (3 * d) := by
        rw [← pow_add, hKeq]
      have hN3 : (0 : ℝ) ≤ (N : ℝ) ^ (3 * (d - 1)) := by positivity
      have hCk30 : (0 : ℝ) ≤ Ck ^ 3 := pow_nonneg hCk0 3
      have hprod : (M : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1))
          ≤ (N : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1)) :=
        mul_le_mul_of_nonneg_right hM3 hN3
      rw [hcast, hKf3]
      have heq1 : 16 * (5250 * ((M : ℝ) ^ 3 * (Ck ^ 3 * (N : ℝ) ^ (3 * (d - 1)))))
          = 16 * 5250 * Ck ^ 3 * ((M : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1))) := by ring
      have heq2 : 16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d)
          = 16 * 5250 * Ck ^ 3 * ((N : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1))) := by
        rw [show (N : ℝ) ^ (3 * d) = (N : ℝ) ^ (3 + 3 * (d - 1)) by congr 1; omega,
          pow_add]
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_left hprod (by nlinarith [hCk30])
    -- `∫ SigTerm^4` 的界
    have hint4 : (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
        ≤ Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1)))
          * (16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d)) := by
      refine le_trans hfour ?_
      have hR4 : (0 : ℝ) ≤ (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (m - (d - 1))) ^ 4 :=
        pow_nonneg (mul_nonneg hmax0 (by positivity)) 4
      refine le_trans (mul_le_mul_of_nonneg_left hcount' hR4) ?_
      have h1 : (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (m - (d - 1))) ^ 4
          = Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1))) := by
        rw [← hRmax, mul_pow, ← pow_mul, Nat.mul_comm]
      rw [h1]
      exact mul_le_mul_of_nonneg_left hCnt
        (mul_nonneg (pow_nonneg (le_of_lt hRmax0) 4) (by positivity))
    -- 合并到 `N^{8m−d}`
    have hNfin : (N : ℝ) ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - (d - 1)))
          * (N : ℝ) ^ (3 * d) = (N : ℝ) ^ (8 * m - d) := by
      rw [← pow_add, ← pow_add, hexp1]
    have hfit : ((M : ℝ) + 1) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
        ≤ (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
          * (N : ℝ) ^ (8 * m - d) := by
      have hM1 : (M : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
      have hP1 : ((M : ℝ) + 1) ^ (4 * m) ≤ 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d) := by
        calc ((M : ℝ) + 1) ^ (4 * m) ≤ (2 * (N : ℝ)) ^ (4 * m) :=
              pow_le_pow_left₀ (by positivity) hM1 _
          _ = 2 ^ (4 * m) * (N : ℝ) ^ (4 * m) := by rw [mul_pow]
          _ ≤ 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 h4md) (by positivity)
      have hP2 : (2 * (M : ℝ)) ^ (4 * (m - 1))
            * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
          ≤ (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3) * (N : ℝ) ^ (8 * m - d) := by
        have hp : (2 * (M : ℝ)) ^ (4 * (m - 1))
            ≤ 2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)) := by
          have h : 2 * (M : ℝ) ≤ 2 * (N : ℝ) := by linarith
          calc (2 * (M : ℝ)) ^ (4 * (m - 1)) ≤ (2 * (N : ℝ)) ^ (4 * (m - 1)) :=
                pow_le_pow_left₀ (by positivity) h _
            _ = 2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)) := by rw [mul_pow]
        have hint0 : (0 : ℝ) ≤ ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4 :=
          intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
        calc (2 * (M : ℝ)) ^ (4 * (m - 1))
              * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
            ≤ (2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)))
              * (Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1)))
                * (16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d))) :=
                mul_le_mul hp hint4 hint0 (by positivity)
          _ = (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
                * ((N : ℝ) ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - (d - 1)))
                  * (N : ℝ) ^ (3 * d)) := by ring
          _ = (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
                * (N : ℝ) ^ (8 * m - d) := by rw [hNfin]
      have hexpand : (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
            * (N : ℝ) ^ (8 * m - d)
          = 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d)
            + (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
              * (N : ℝ) ^ (8 * m - d) := by ring
      rw [hexpand]
      linarith
    -- 组装
    have hmain : (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ 2 ^ (4 * (m - 1)) * 8 *
            ((2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
              * (N : ℝ) ^ (8 * m - d)) := by
      refine le_trans (integral_bound hd a hM1) ?_
      have hbase : ((M : ℝ) + 1) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
          ≤ (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
            * (N : ℝ) ^ (8 * m - d) := by
        rw [← hm]
        exact hfit
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    refine le_trans hmain (le_of_eq ?_)
    have h8 : 8 ^ (d - 1) = 8 * m := by
      rw [hm, show d - 1 = (d - 2) + 1 by omega, pow_succ]
      ring
    rw [h8]
    simp only [Rd]
    rw [hm]
    ring

/-- 加强版蕴含原版（取 `M = N`）。 -/
theorem MeanValueBound.of_S {d : ℕ} (h : MeanValueBoundS d) : MeanValueBound d := by
  obtain ⟨R, hR, hb⟩ := h
  exact ⟨R, hR, fun c N hN a had ha => hb c N N hN hN le_rfl a had ha⟩

/-- **对一切 `d ≥ 2`，`P(d)` 成立**（基例 `P(2)` + 归纳步）。 -/
theorem meanValueBoundS_all (d : ℕ) (hd : 2 ≤ d) : MeanValueBoundS d := by
  induction d, hd using Nat.le_induction with
  | base => exact meanValueBoundS_two
  | succ m hm ih =>
      exact meanValueBoundS_succ (d := m + 1) (by omega) (by simpa using ih)

/-- **Jameson Theorem 1**（一般 `k`，均值估计）：对一切 `d ≥ 2`。 -/
theorem meanValueBound_all (d : ℕ) (hd : 2 ≤ d) : MeanValueBound d :=
  MeanValueBound.of_S (meanValueBoundS_all d hd)

end Waring
