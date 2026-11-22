/- GID: D5/S3/Arith/Additive/Waring/WaringQuadraticFibers
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringQuadraticFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringQuadratic.lean#L1-L639
   Modified for this repository. Local imports use their D5 module paths.
   This file contains one segment of a split upstream module.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringExpSum
import D5.S3.Arith.Additive.Waring.WaringCount
import D5.S3.Arith.Additive.Waring.WaringLemma3
import D5.S3.Arith.Additive.Waring.WaringSymm

open Finset intervalIntegral

set_option maxHeartbeats 1000000

namespace Waring

/-- `e(Σ x) = ∏ e(x)`。 -/
theorem e_sum (ι : Type) [Fintype ι] (x : ι → ℝ) : e (∑ i, x i) = ∏ i, e (x i) := by
  unfold e
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- `e((Σ x)·α) = ∏ e(x·α)`。 -/
theorem e_sum_mul (ι : Type) [Fintype ι] (x : ι → ℝ) (α : ℝ) :
    e ((∑ i, x i) * α) = ∏ i, e (x i * α) := by
  rw [show (∑ i, x i) * α = ∑ i, x i * α from Finset.sum_mul ..]
  exact e_sum ι (fun i => x i * α)

/-- `α ↦ e(c·α)` 连续。 -/
theorem continuous_e_comp (c : ℝ) : Continuous fun α : ℝ => e (c * α) := by
  unfold e
  fun_prop

/-- 二次形式 `f(n) = a n² + b n`（整系数）。 -/
def qf (a b : ℤ) (n : ℤ) : ℤ := a * n ^ 2 + b * n

/-- 四元组的 `f`-和 `∑_{i<4} f(pᵢ)`。 -/
def qf4 (a b : ℤ) {N : ℕ} (p : Fin 4 → Fin (N + 1)) : ℤ :=
  ∑ i : Fin 4, qf a b ((p i : ℕ) : ℤ)

/-- 一般二次形式的指数和 `∑_{n≤N} e(α f(n))`。 -/
noncomputable def qSum (a b : ℤ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n : Fin (N + 1), e ((qf a b (n : ℤ) : ℝ) * α)

/-- `qSum⁴` 展开成四重和。 -/
theorem qSum_pow_four (a b : ℤ) (N : ℕ) (α : ℝ) :
    qSum a b N α ^ 4 = ∑ p : Fin 4 → Fin (N + 1),
      e (((qf4 a b p) : ℝ) * α) := by
  unfold qSum
  rw [Finset.sum_pow']
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro p _
  simp only [qf4, qf]
  push_cast
  rw [e_sum_mul]

/-- `conj (qSum)⁴` 展开成四重和。 -/
theorem conj_qSum_pow_four (a b : ℤ) (N : ℕ) (α : ℝ) :
    (starRingEnd ℂ) (qSum a b N α) ^ 4 = ∑ p : Fin 4 → Fin (N + 1),
      e (-(((qf4 a b p) : ℝ) * α)) := by
  unfold qSum
  rw [map_sum, Finset.sum_pow']
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro p _
  have step1 : (∏ i : Fin 4,
      (starRingEnd ℂ) (e ((qf a b ((p i : ℕ) : ℤ) : ℝ) * α)))
      = ∏ i : Fin 4, e (((-(qf a b ((p i : ℕ) : ℤ)) : ℤ) : ℝ) * α) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← e_neg]
    congr 1
    push_cast
    ring
  rw [step1, ← e_sum_mul]
  congr 1
  rw [qf4]
  push_cast
  rw [Finset.sum_neg_distrib]
  ring

/-- 八元组「`f`-和相等」的计数。 -/
noncomputable def qEqCount (a b : ℤ) (N : ℕ) : ℕ :=
  ((Finset.univ : Finset
      ((Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)))).filter
    (fun pq => qf4 a b pq.1 = qf4 a b pq.2)).card

/-- **矩 = 计数**（一般二次形式的八次矩）。 -/
theorem integral_normSq_pow_four_q (a b : ℤ) (N : ℕ) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (qSum a b N α)) ^ 4)
      = (qEqCount a b N : ℝ) := by
  have hfun : ∀ α : ℝ, (((Complex.normSq (qSum a b N α)) ^ 4 : ℝ) : ℂ)
      = ((starRingEnd ℂ) (qSum a b N α)) ^ 4 * (qSum a b N α) ^ 4 := by
    intro α
    rw [Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    ring
  have hcomb : ∀ (p q : Fin 4 → Fin (N + 1)) (α : ℝ),
      e (-(((qf4 a b p) : ℝ) * α)) * e (((qf4 a b q) : ℝ) * α)
      = e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α) := by
    intro p q α
    rw [← e_add]
    congr 1
    push_cast
    ring
  have hstep : ∀ pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)),
      (∫ α in (0 : ℝ)..1, e (((↑(qf4 a b pq.2 - qf4 a b pq.1)) : ℝ) * α))
        = (if qf4 a b pq.1 = qf4 a b pq.2 then 1 else 0) := by
    intro pq
    set m : ℤ := qf4 a b pq.2 - qf4 a b pq.1 with hm
    rw [show (((↑(qf4 a b pq.2 - qf4 a b pq.1)) : ℝ)) = (m : ℝ) from by rw [hm]]
    rw [integral_e_mul_int]
    by_cases h : qf4 a b pq.1 = qf4 a b pq.2
    · have hz : m = 0 := by rw [hm, h]; ring
      simp [h, hz]
    · have hz : m ≠ 0 := by
        rw [hm]
        intro hz
        exact h (by linarith)
      simp [h, hz]
  have hcont : ∀ p : Fin 4 → Fin (N + 1),
      Continuous fun α : ℝ => ∑ q : Fin 4 → Fin (N + 1),
        e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α) := by
    intro p
    exact continuous_finsetSum _ (fun q _ => continuous_e_comp _)
  have hswap : (∫ α in (0 : ℝ)..1, ∑ p : (Fin 4 → Fin (N + 1)),
      ∑ q : (Fin 4 → Fin (N + 1)), e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α))
      = ∑ p : (Fin 4 → Fin (N + 1)), ∑ q : (Fin 4 → Fin (N + 1)),
          ∫ α in (0 : ℝ)..1, e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl ?_
      intro p _
      rw [intervalIntegral.integral_finsetSum]
      intro q _
      exact Continuous.intervalIntegrable (continuous_e_comp _) 0 1
    · intro p _
      exact Continuous.intervalIntegrable (hcont p) 0 1
  apply Complex.ofReal_inj.mp
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hfun, conj_qSum_pow_four, qSum_pow_four]
  simp only [Finset.sum_mul_sum]
  simp_rw [hcomb]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hstep (p, q)))]
  rw [← Fintype.sum_prod_type
    (f := fun pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)) =>
      if qf4 a b pq.1 = qf4 a b pq.2 then (1 : ℂ) else 0)]
  rw [Finset.sum_boole]
  norm_cast

/-- `(h,m)` 形式的计数：`∑ᵢ hᵢ(a mᵢ + b) = 0`。 -/
noncomputable def qHMCount (a b : ℤ) (N : ℕ) : ℕ :=
  (((hBox N).product (mBox N)).filter
    (fun hm => (∑ i : Fin 4, hm.1 i * (a * hm.2 i + b)) = 0)).card

/-- `toHM` 的像落在 `hBox × mBox` 里。 -/
theorem toHM_mem_box (N : ℕ) (pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1))) :
    toHM N pq ∈ (hBox N).product (mBox N) := by
  have h1 : (fun i => (pq.1 i : ℤ) - (pq.2 i : ℤ)) ∈ hBox N := by
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

/-- `toHM` 单射。 -/
theorem toHM_inj (N : ℕ) :
    ∀ pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)),
      ∀ pq' : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)),
      toHM N pq = toHM N pq' → pq = pq' := by
  intro pq pq' heq
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

/-- **换变量**：`f`-和相等的计数不超过 `(h,m)` 计数。 -/
theorem qEqCount_le_qHMCount (a b : ℤ) (N : ℕ) : qEqCount a b N ≤ qHMCount a b N := by
  classical
  refine Finset.card_le_card_of_injOn (toHM N) ?_ ?_
  · intro pq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hpq
    obtain ⟨-, hpq⟩ := hpq
    simp only [qf4] at hpq
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨toHM_mem_box N pq, ?_⟩
    have hsq : ∀ i : Fin 4,
        ((pq.1 i : ℤ) - (pq.2 i : ℤ)) * (a * ((pq.1 i : ℤ) + (pq.2 i : ℤ)) + b)
          = qf a b ((pq.1 i : ℕ) : ℤ) - qf a b ((pq.2 i : ℕ) : ℤ) := by
      intro i
      unfold qf
      ring
    show (∑ i : Fin 4, ((pq.1 i : ℤ) - (pq.2 i : ℤ))
      * (a * ((pq.1 i : ℤ) + (pq.2 i : ℤ)) + b)) = 0
    rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_sub_distrib, hpq]
    ring
  · exact fun x _ y _ hxy => toHM_inj N x y hxy

/-- 二元部分和盒子 `[−H,H]² × [0,M]²`。 -/
noncomputable def qPbox2 (H M : ℕ) : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ))

/-- 二元部分和 `h₀(a m₀ + b) + h₁(a m₁ + b)`。 -/
def qAval (a b : ℤ) (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : ℤ :=
  a * (p.1 0 * p.2 0 + p.1 1 * p.2 1) + b * (p.1 0 + p.1 1)

/-- 二元部分和计数。 -/
noncomputable def qQ (a b : ℤ) (H M : ℕ) (n : ℤ) : ℕ :=
  ((qPbox2 H M).filter (fun p => qAval a b p = n)).card

/-- `box2 0 M` 的基数。 -/
theorem box2_zero_card (M : ℕ) : (box2 (0 : ℤ) (M : ℤ)).card = (M + 1) ^ 2 := by
  rw [box2, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Int.card_Icc]
  have h : (M : ℤ) + 1 - 0 = (M : ℤ) + 1 := by ring
  rw [h]
  omega

/-- **对接**：`qHMCount` 不超过 `(Pbox2 × Pbox2)` 中的 `A + A' = 0` 计数。 -/
theorem qHMCount_le_qHMCount2 (a b : ℤ) (N : ℕ) :
    qHMCount a b N ≤
      (((qPbox2 N (2 * N)).product (qPbox2 N (2 * N))).filter
        (fun pq => qAval a b pq.1 + qAval a b pq.2 = 0)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun hm : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      (((split4 hm.1).1, (split4 hm.2).1), ((split4 hm.1).2, (split4 hm.2).2))) ?_ ?_
  · intro hm hhm
    rw [Finset.mem_coe, Finset.mem_filter] at hhm
    obtain ⟨hhmS, hhm0⟩ := hhm
    have hh1 : hm.1 ∈ hBox N := ((Finset.mem_product).mp hhmS).1
    have hh2 : hm.2 ∈ mBox N := ((Finset.mem_product).mp hhmS).2
    rw [hBox, Fintype.mem_piFinset] at hh1
    rw [mBox, Fintype.mem_piFinset] at hh2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh1 ⟨i.val, by omega⟩
        simpa [split4] using this
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh2 ⟨i.val, by omega⟩
        simpa [split4] using this
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh1 ⟨i.val + 2, by omega⟩
        simpa [split4] using this
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh2 ⟨i.val + 2, by omega⟩
        simpa [split4] using this
    · have hsum := hhm0
      rw [sum_fin4] at hsum
      have hgoal : qAval a b ((split4 hm.1).1, (split4 hm.2).1)
          + qAval a b ((split4 hm.1).2, (split4 hm.2).2)
          = hm.1 0 * (a * hm.2 0 + b) + hm.1 1 * (a * hm.2 1 + b)
            + hm.1 2 * (a * hm.2 2 + b) + hm.1 3 * (a * hm.2 3 + b) := by
        obtain ⟨e1, e2⟩ := split4_fst_val hm.1
        obtain ⟨e3, e4⟩ := split4_fst_val hm.2
        obtain ⟨e5, e6⟩ := split4_snd_val hm.1
        obtain ⟨e7, e8⟩ := split4_snd_val hm.2
        simp only [qAval, e1, e2, e3, e4, e5, e6, e7, e8]
        ring
      rw [hgoal, hsum]
  · intro x _ y _ hxy
    obtain ⟨h1, m1⟩ := x
    obtain ⟨h2, m2⟩ := y
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨⟨hh1, hm1⟩, hh2, hm2⟩ := hxy
    have hsp1 : split4 h1 = split4 h2 := Prod.ext hh1 hh2
    have hsp2 : split4 m1 = split4 m2 := Prod.ext hm1 hm2
    rw [split4_injective hsp1, split4_injective hsp2]

/-- **Fubini 展开**：`qHMCount` 不超过 `Σ_n qQ(n)·qQ(−n)`。 -/
theorem qHMCount_le_sum_qQ (a b : ℤ) (N : ℕ) (K : ℤ)
    (hK : ∀ p ∈ qPbox2 N (2 * N), |qAval a b p| ≤ K) :
    qHMCount a b N ≤
      ∑ n ∈ Finset.Icc (-K) K, qQ a b N (2 * N) n * qQ a b N (2 * N) (-n) := by
  classical
  set P : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) := qPbox2 N (2 * N) with hP
  -- 内层：每个 `p` 贡献 `qQ(−A p)`
  have hstep1 : (((P.product P).filter (fun pq => qAval a b pq.1 + qAval a b pq.2 = 0)).card)
      = ∑ p ∈ P, qQ a b N (2 * N) (-(qAval a b p)) := by
    rw [Finset.card_filter]
    rw [show (∑ i ∈ P.product P,
          (if qAval a b i.1 + qAval a b i.2 = 0 then (1 : ℕ) else 0))
        = ∑ p ∈ P, ∑ q ∈ P,
          (if qAval a b p + qAval a b q = 0 then (1 : ℕ) else 0) from
      Finset.sum_product P P (fun i => if qAval a b i.1 + qAval a b i.2 = 0 then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hc : (P.filter (fun q => qAval a b p + qAval a b q = 0))
        = (P.filter (fun q => qAval a b q = -(qAval a b p))) := by
      apply Finset.filter_congr
      intro q _
      constructor <;> intro h <;> linarith
    rw [← Finset.card_filter]
    rw [hc]
    rw [show (P.filter (fun q => qAval a b q = -(qAval a b p)))
        = ((qPbox2 N (2 * N)).filter (fun q => qAval a b q = -(qAval a b p))) from by rw [hP]]
    rw [← qQ]
  -- 外层：按 `n = A p` 展开
  refine le_trans (qHMCount_le_qHMCount2 a b N) ?_
  rw [show (((qPbox2 N (2 * N)).product (qPbox2 N (2 * N))).filter
        (fun pq => qAval a b pq.1 + qAval a b pq.2 = 0)).card
      = ∑ p ∈ P, qQ a b N (2 * N) (-(qAval a b p)) from hstep1]
  have hpoint : ∀ p ∈ P, qQ a b N (2 * N) (-(qAval a b p))
      = ∑ n ∈ Finset.Icc (-K) K,
          (if qAval a b p = n then qQ a b N (2 * N) (-n) else 0) := by
    intro p hp
    rw [Finset.sum_ite_eq]
    rw [if_pos (by
      rw [Finset.mem_Icc]
      have h := hK p hp
      rw [abs_le] at h
      exact h)]
  rw [Finset.sum_congr rfl (fun p hp => hpoint p hp)]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [← Finset.sum_filter]
  have hcard : (P.filter (fun x => qAval a b x = n)).card = qQ a b N (2 * N) n := by
    rw [qQ, ← hP]
  rw [Finset.sum_const, hcard]
  simp

/-- `prim (a·h)` 与 `prim h` 的坐标绝对值相同。 -/
theorem prim_smul_natAbs (a : ℤ) (ha : a ≠ 0) {h : Fin 2 → ℤ} (hh : h ≠ 0) (i : Fin 2) :
    (prim (fun j => a * h j) i).natAbs = (prim h i).natAbs := by
  have hG : Nat.gcd ((a * h 0).natAbs) ((a * h 1).natAbs)
      = a.natAbs * Nat.gcd (h 0).natAbs (h 1).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_left]
  have hdvd : ∀ j : Fin 2, ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h j := by
    intro j
    have h1 := Int.gcd_dvd_left (h 0) (h 1)
    have h2 := Int.gcd_dvd_right (h 0) (h 1)
    rw [Int.gcd_eq_natAbs] at h1 h2
    fin_cases j
    · exact h1
    · exact h2
  have hdvdA : ∀ j : Fin 2,
      ((Nat.gcd ((a * h 0).natAbs) ((a * h 1).natAbs) : ℕ) : ℤ) ∣ a * h j := by
    intro j
    have hgoal : Nat.gcd ((a * h 0).natAbs) ((a * h 1).natAbs) ∣ (a * h j).natAbs := by
      rw [hG, Int.natAbs_mul]
      fin_cases j
      · exact mul_dvd_mul (dvd_refl _) (Nat.gcd_dvd_left _ _)
      · exact mul_dvd_mul (dvd_refl _) (Nat.gcd_dvd_right _ _)
    rw [← Int.natAbs_dvd_natAbs]
    simpa using hgoal
  have hdvdA' : ((a.natAbs * Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ a * h i := by
    rw [← hG]
    exact hdvdA i
  have hprimA : prim (fun j => a * h j) i
      = a * h i / ((a.natAbs * Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) := by
    unfold prim
    rw [hG]
  have hprimB : prim h i = h i / ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) := rfl
  rw [hprimA, hprimB]
  rw [Int.natAbs_ediv_of_dvd hdvdA', Int.natAbs_ediv_of_dvd (hdvd i)]
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  exact Nat.mul_div_mul_left _ _ (Int.natAbs_pos.mpr ha)

/-- 纤维界：`h ≠ 0` 时，`a(h₀m₀+h₁m₁) + b(h₀+h₁) = n` 在 `[0,M]²` 中的
解数不超过 `M/max|prim h| + 1`。 -/
theorem qQ_fiber_le (a b : ℤ) (ha : a ≠ 0) (M : ℕ) (n : ℤ) {h : Fin 2 → ℤ}
    (hh : h ≠ 0) :
    ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
      a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card
      ≤ M / max (prim h 0).natAbs (prim h 1).natAbs + 1 := by
  classical
  have hAne : (fun j => a * h j) ≠ 0 := by
    intro hzero
    apply hh
    funext i
    have hi := congrFun hzero i
    simp only [Pi.zero_apply] at hi
    exact mul_left_cancel₀ ha (by simpa using hi)
  have hfilter : (box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
      a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)
      = (box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        (a * h 0) * m 0 + (a * h 1) * m 1 = n - b * (h 0 + h 1)) := by
    refine Finset.filter_congr (fun m _ => ?_)
    constructor
    · intro hm
      have hring : (a * h 0) * m 0 + (a * h 1) * m 1
          = a * (h 0 * m 0 + h 1 * m 1) := by ring
      linarith
    · intro hm
      have hring : a * (h 0 * m 0 + h 1 * m 1)
          = (a * h 0) * m 0 + (a * h 1) * m 1 := by ring
      linarith
  rw [hfilter]
  refine le_trans (fiber_le_gcd hAne M (n - b * (h 0 + h 1))) ?_
  rw [prim_smul_natAbs a ha hh 0, prim_smul_natAbs a ha hh 1]

/-- **纤维非空 ⟹ `gcd | n`**。 -/
theorem gcond_of_fiber (a b : ℤ) (M : ℕ) (n : ℤ) {h : Fin 2 → ℤ}
    {m : Fin 2 → ℤ} (hm : a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n) :
    gcond n h := by
  unfold gcond
  have hdvd : ∀ j : Fin 2, ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h j := by
    intro j
    have h1 := Int.gcd_dvd_left (h 0) (h 1)
    have h2 := Int.gcd_dvd_right (h 0) (h 1)
    rw [Int.gcd_eq_natAbs] at h1 h2
    fin_cases j
    · exact h1
    · exact h2
  have hdvdsum : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h 0 + h 1 :=
    dvd_add (hdvd 0) (hdvd 1)
  have hdvdprod : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ)
      ∣ h 0 * m 0 + h 1 * m 1 :=
    dvd_add (dvd_mul_of_dvd_left (hdvd 0) (m 0)) (dvd_mul_of_dvd_left (hdvd 1) (m 1))
  rw [← hm]
  exact dvd_add (dvd_mul_of_dvd_right hdvdprod a) (dvd_mul_of_dvd_right hdvdsum b)

/-- `qQ` 按 `h` 拆成纤维的卡片和。 -/
theorem qQ_eq_sum_fiber (a b : ℤ) (H M : ℕ) (n : ℤ) :
    qQ a b H M n = ∑ h ∈ box2 (-(H : ℤ)) (H : ℤ),
      ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card := by
  classical
  rw [qQ, Finset.card_filter, qPbox2]
  rw [show (∑ i ∈ (box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ)),
        (if qAval a b i = n then (1 : ℕ) else 0))
      = ∑ h ∈ box2 (-(H : ℤ)) (H : ℤ), ∑ m ∈ box2 (0 : ℤ) (M : ℤ),
        (if qAval a b (h, m) = n then (1 : ℕ) else 0) from
    Finset.sum_product _ _ _]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rfl

/-- **Lemma 3（一般二次形式版）**：`qQ(H,M;n) ≤ 4H(H+1) + 8HM·σ₋₁(|n|)`（`n ≠ 0`）。 -/
theorem qQ_le_sigma (a b : ℤ) (ha : a ≠ 0) (H M : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (qQ a b H M n : ℚ) ≤ 4 * (H : ℚ) * ((H : ℚ) + 1)
      + 8 * (H : ℚ) * (M : ℚ) * sigmaMinusOne n.natAbs := by
  classical
  set B : Finset (Fin 2 → ℤ) := box2 (-(H : ℤ)) (H : ℤ) with hB
  set D : Finset (Fin 2 → ℤ) := box2 (0 : ℤ) (M : ℤ) with hD
  set F : (Fin 2 → ℤ) → ℕ := fun h => (D.filter (fun m : Fin 2 → ℤ =>
      a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card with hF
  set Sf : Finset (Fin 2 → ℤ) := B.filter (fun h : Fin 2 → ℤ => h ≠ 0 ∧ gcond n h) with hSf
  have hQ : qQ a b H M n = ∑ h ∈ B, F h := qQ_eq_sum_fiber a b H M n
  -- 去掉 h = 0
  have hzero : F 0 = 0 := by
    rw [hF]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _ hm
    apply hn
    have h' : a * (((0 : Fin 2 → ℤ) 0) * m 0 + ((0 : Fin 2 → ℤ) 1) * m 1)
        + b * ((0 : Fin 2 → ℤ) 0 + (0 : Fin 2 → ℤ) 1) = n := hm
    simpa using h'.symm
  have h1 : (∑ h ∈ B, F h) = ∑ h ∈ B.filter (fun h : Fin 2 → ℤ => h ≠ 0), F h := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro h hB hnotmem
    by_cases h0 : h = 0
    · rw [h0]
      exact hzero
    · exact absurd (by rw [Finset.mem_filter]; exact ⟨hB, h0⟩) hnotmem
  -- 去掉 gcd ∤ n 的 h
  have h2 : (∑ h ∈ B.filter (fun h : Fin 2 → ℤ => h ≠ 0), F h) = ∑ h ∈ Sf, F h := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro h hh
      rw [hSf, Finset.mem_filter] at hh
      rw [Finset.mem_filter]
      exact ⟨hh.1, hh.2.1⟩
    · intro h hh hnotmem
      rw [Finset.mem_filter] at hh
      obtain ⟨hB, hne⟩ := hh
      have hc : ¬ gcond n h := by
        intro hc'
        exact hnotmem (by rw [hSf, Finset.mem_filter]; exact ⟨hB, hne, hc'⟩)
      rw [hF]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _ hm
      exact hc (gcond_of_fiber a b M n hm)
  -- 逐项界
  have h3 : ((∑ h ∈ Sf, F h : ℕ) : ℚ) ≤ ∑ h ∈ Sf,
      ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1) := by
    push_cast
    refine Finset.sum_le_sum (fun h hh => ?_)
    rw [hSf, Finset.mem_filter] at hh
    obtain ⟨-, hne, -⟩ := hh
    have hb := qQ_fiber_le a b ha M n hne
    have hFF : F h = ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card := by
      rw [hF, hD]
    rw [hFF]
    have hcast : (((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card : ℚ) ≤
        ((M / max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) + 1 := by
      exact_mod_cast hb
    have hdiv : ((M / max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) ≤
        (M : ℚ) / ((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) := Nat.cast_div_le
    have hdiv' : ((M / max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) ≤
        (M : ℚ) / max ((prim h 0).natAbs : ℚ) ((prim h 1).natAbs : ℚ) := by
      rw [← Nat.cast_max]
      exact hdiv
    linarith [hcast, hdiv']
  -- 拆分求和
  have h4 : (∑ h ∈ Sf, ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1))
      = (M : ℚ) * (∑ h ∈ Sf,
          (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
        + (∑ h ∈ Sf, (1 : ℚ)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [mul_one_div]
  have h5 : (∑ h ∈ Sf, (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
      ≤ 8 * (H : ℚ) * sigmaMinusOne n.natAbs := by
    rw [hSf, hB]
    exact sum_inv_prim_le hn H
  have h6 : (∑ h ∈ Sf, (1 : ℚ)) ≤ 4 * (H : ℚ) * ((H : ℚ) + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : Sf.card ≤ 4 * H * (H + 1) := by
      have hsub : Sf ⊆ B.filter (fun h : Fin 2 → ℤ => h ≠ 0) := by
        intro h hh
        rw [hSf, Finset.mem_filter] at hh
        exact Finset.mem_filter.mpr ⟨hh.1, hh.2.1⟩
      have hc1 : Sf.card ≤ (B.filter (fun h : Fin 2 → ℤ => h ≠ 0)).card :=
        Finset.card_le_card hsub
      rw [hB, card_box2_ne_zero H] at hc1
      refine le_trans hc1 ?_
      have hsq : (2 * H + 1) ^ 2 = 4 * H * (H + 1) + 1 := by ring
      rw [hsq, Nat.add_sub_cancel]
    exact_mod_cast hcard
  calc (qQ a b H M n : ℚ) = ((∑ h ∈ Sf, F h : ℕ) : ℚ) := by rw [hQ, h1, h2]
    _ ≤ ∑ h ∈ Sf, ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1) := h3
    _ = (M : ℚ) * (∑ h ∈ Sf,
          (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
        + (∑ h ∈ Sf, (1 : ℚ)) := h4
    _ ≤ (M : ℚ) * (8 * (H : ℚ) * sigmaMinusOne n.natAbs)
        + 4 * (H : ℚ) * ((H : ℚ) + 1) := by
        have hM : (0 : ℚ) ≤ (M : ℚ) := by positivity
        have hMA : (M : ℚ) * (∑ h ∈ Sf,
            (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
            ≤ (M : ℚ) * (8 * (H : ℚ) * sigmaMinusOne n.natAbs) :=
          mul_le_mul_of_nonneg_left h5 hM
        linarith [hMA, h6]
    _ = 4 * (H : ℚ) * ((H : ℚ) + 1)
        + 8 * (H : ℚ) * (M : ℚ) * sigmaMinusOne n.natAbs := by ring

end Waring
