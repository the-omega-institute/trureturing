/- GID: D5/S3/Arith/Additive/Waring/WaringQuadratic
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringQuadratic.lean#L640-L1084
   Modified for this repository. Local imports use their D5 module paths.
   This file contains one segment of a split upstream module.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringQuadraticFibers

open Finset intervalIntegral

set_option maxHeartbeats 1000000

namespace Waring

/-! ## 第五部分：`qQ` 的对称性与零点界 -/

/-- 部分和的界常数 `K = 4N²|a| + 2N|b|`。 -/
def qK (a b : ℤ) (N : ℕ) : ℤ :=
  4 * (N : ℤ) ^ 2 * (a.natAbs : ℤ) + 2 * (N : ℤ) * (b.natAbs : ℤ)

/-- `qK` 非负。 -/
theorem qK_nonneg (a b : ℤ) (N : ℕ) : 0 ≤ qK a b N := by
  unfold qK
  positivity

/-- **部分和的范围**：`|qAval p| ≤ qK a b N`。 -/
theorem qAval_bound (a b : ℤ) (N : ℕ) {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hp : p ∈ qPbox2 N (2 * N)) : |qAval a b p| ≤ qK a b N := by
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
  have haa : |a| = (a.natAbs : ℤ) := Int.abs_eq_natAbs a
  have hbb : |b| = (b.natAbs : ℤ) := Int.abs_eq_natAbs b
  unfold qAval qK
  calc |a * (p.1 0 * p.2 0 + p.1 1 * p.2 1) + b * (p.1 0 + p.1 1)|
      ≤ |a * (p.1 0 * p.2 0 + p.1 1 * p.2 1)| + |b * (p.1 0 + p.1 1)| := abs_add_le _ _
    _ = |a| * |p.1 0 * p.2 0 + p.1 1 * p.2 1| + |b| * |p.1 0 + p.1 1| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * (|p.1 0| * |p.2 0| + |p.1 1| * |p.2 1|) + |b| * (|p.1 0| + |p.1 1|) := by
        have e1 : |p.1 0 * p.2 0 + p.1 1 * p.2 1| ≤ |p.1 0| * |p.2 0| + |p.1 1| * |p.2 1| := by
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul, abs_mul]
        have e2 : |p.1 0 + p.1 1| ≤ |p.1 0| + |p.1 1| := abs_add_le _ _
        have h1 := mul_le_mul_of_nonneg_left e1 (abs_nonneg a)
        have h2 := mul_le_mul_of_nonneg_left e2 (abs_nonneg b)
        linarith
    _ ≤ |a| * ((N : ℤ) * (2 * (N : ℤ)) + (N : ℤ) * (2 * (N : ℤ)))
          + |b| * ((N : ℤ) + (N : ℤ)) := by
        have h1 : |p.1 0| * |p.2 0| + |p.1 1| * |p.2 1|
            ≤ (N : ℤ) * (2 * (N : ℤ)) + (N : ℤ) * (2 * (N : ℤ)) := by
          have e1 := mul_le_mul hb1 hb3' (abs_nonneg _) (by positivity : (0:ℤ) ≤ N)
          have e2 := mul_le_mul hb2 hb4' (abs_nonneg _) (by positivity : (0:ℤ) ≤ N)
          linarith
        have h2 : |p.1 0| + |p.1 1| ≤ (N : ℤ) + (N : ℤ) := by linarith
        have e1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
        have e2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
        linarith
    _ = 4 * (N : ℤ) ^ 2 * (a.natAbs : ℤ) + 2 * (N : ℤ) * (b.natAbs : ℤ) := by
        rw [haa, hbb]
        ring

/-- **`qQ` 的对称性**：`qQ(−n) = qQ(n)`。 -/
theorem qQ_neg (a b : ℤ) (H M : ℕ) (n : ℤ) : qQ a b H M (-n) = qQ a b H M n := by
  classical
  unfold qQ
  have hboxmem : ∀ p ∈ qPbox2 H M, (-p.1, p.2) ∈ qPbox2 H M := by
    intro p hp
    refine Finset.mem_product.mpr ⟨?_, (Finset.mem_product.mp hp).2⟩
    have hp1 : ∀ i, p.1 i ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
      have h := (Finset.mem_product.mp hp).1
      rw [box2, Fintype.mem_piFinset] at h
      exact h
    rw [box2, Fintype.mem_piFinset]
    intro i
    have hi := hp1 i
    rw [Finset.mem_Icc] at hi ⊢
    simp only [Pi.neg_apply]
    constructor <;> linarith [hi.1, hi.2]
  have hneg : ∀ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), qAval a b (-p.1, p.2) = -qAval a b p := by
    intro p
    unfold qAval
    simp only [Pi.neg_apply]
    ring
  refine Finset.card_bij (fun p _ => (-p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hboxmem p hp.1, by rw [hneg, hp.2]; ring⟩
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    exact Prod.ext (neg_inj.mp h1) h2
  · intro q hq
    rw [Finset.mem_filter] at hq
    refine ⟨(-q.1, q.2), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hboxmem q hq.1, by rw [hneg, hq.2]⟩
    · simp
/-- **零点的一致界**：`qQ(0) ≤ (M+1)² + 4H(H+1)(M+1)`。 -/
theorem qQ_zero_le (a b : ℤ) (ha : a ≠ 0) (H M : ℕ) :
    qQ a b H M 0 ≤ (M + 1) ^ 2 + 4 * H * (H + 1) * (M + 1) := by
  classical
  rw [qQ_eq_sum_fiber]
  set B : Finset (Fin 2 → ℤ) := box2 (-(H : ℤ)) (H : ℤ) with hB
  set F : (Fin 2 → ℤ) → ℕ := fun h => ((box2 (0 : ℤ) (M : ℤ)).filter
    (fun m : Fin 2 → ℤ => a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = 0)).card with hF
  have h0mem : (0 : Fin 2 → ℤ) ∈ B := by
    rw [hB]
    exact mem_box2_of_abs_le (fun i => by simp)
  have hF0 : F 0 ≤ (M + 1) ^ 2 := by
    have hsub : (box2 (0 : ℤ) (M : ℤ)).filter
        (fun m : Fin 2 → ℤ => a * ((0 : Fin 2 → ℤ) 0 * m 0 + (0 : Fin 2 → ℤ) 1 * m 1)
          + b * ((0 : Fin 2 → ℤ) 0 + (0 : Fin 2 → ℤ) 1) = 0)
        ⊆ box2 (0 : ℤ) (M : ℤ) := Finset.filter_subset _ _
    have h1 : F 0 ≤ (box2 (0 : ℤ) (M : ℤ)).card := by
      rw [hF]
      exact Finset.card_le_card hsub
    rw [box2_zero_card] at h1
    exact h1
  have hpos : ∀ h : Fin 2 → ℤ, h ≠ 0 →
      1 ≤ max (prim h 0).natAbs (prim h 1).natAbs := by
    intro h hh
    have hpne : prim h ≠ 0 := by
      intro hp0
      apply hh
      funext i
      rw [h_eq_gcd_mul_prim h i, congrFun hp0 i]
      simp
    obtain ⟨i, hi⟩ : ∃ i, prim h i ≠ 0 := by
      by_contra hall
      apply hpne
      funext i
      by_contra hc
      exact hall ⟨i, hc⟩
    have h1 : 1 ≤ (prim h i).natAbs := Int.natAbs_pos.mpr hi
    fin_cases i
    · exact le_trans h1 (le_max_left _ _)
    · exact le_trans h1 (le_max_right _ _)
  have hFne : ∀ h ∈ B.erase (0 : Fin 2 → ℤ), F h ≤ M + 1 := by
    intro h hh
    rw [Finset.mem_erase] at hh
    obtain ⟨hne, hB⟩ := hh
    have hb := qQ_fiber_le a b ha M 0 hne
    have hFF : F h = ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = 0)).card := by
      rw [hF]
    rw [hFF]
    refine le_trans hb ?_
    have hp := hpos h hne
    have hd : M / max (prim h 0).natAbs (prim h 1).natAbs ≤ M := Nat.div_le_self M _
    omega
  have hsplit : (∑ h ∈ B, F h) = F 0 + ∑ h ∈ B.erase (0 : Fin 2 → ℤ), F h := by
    rw [add_comm]
    exact (Finset.sum_erase_add B F h0mem).symm
  rw [hsplit]
  have hcard : (B.erase (0 : Fin 2 → ℤ)).card = 4 * H * (H + 1) := by
    rw [Finset.card_erase_of_mem h0mem, hB, card_box2]
    have hsq : (2 * H + 1) ^ 2 = 4 * H * (H + 1) + 1 := by ring
    rw [hsq, Nat.add_sub_cancel]
  have hsum : (∑ h ∈ B.erase (0 : Fin 2 → ℤ), F h) ≤ (B.erase (0 : Fin 2 → ℤ)).card * (M + 1) := by
    calc (∑ h ∈ B.erase (0 : Fin 2 → ℤ), F h) ≤ (B.erase (0 : Fin 2 → ℤ)).card • (M + 1) :=
          Finset.sum_le_card_nsmul _ _ _ hFne
      _ = (B.erase (0 : Fin 2 → ℤ)).card * (M + 1) := by simp
  rw [hcard] at hsum
  linarith

/-! ## 第六部分：汇总 —— 八次矩的 `N⁶` 界 -/

/-- 对称区间的求和公式（`ℚ` 值）。 -/
theorem sum_Icc_symm_rat (K : ℤ) (hK : 0 ≤ K) (f : ℤ → ℚ) (hf : ∀ n, f (-n) = f n) :
    (∑ n ∈ Finset.Icc (-K) K, f n) = f 0 + 2 * ∑ n ∈ Finset.Icc (1 : ℤ) K, f n := by
  have hU1 : Finset.Icc (-K) (-1 : ℤ) ∪ Finset.Icc (0 : ℤ) K = Finset.Icc (-K) K := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd1 : Disjoint (Finset.Icc (-K) (-1 : ℤ)) (Finset.Icc (0 : ℤ) K) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have hU2 : ({0} : Finset ℤ) ∪ Finset.Icc (1 : ℤ) K = Finset.Icc (0 : ℤ) K := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hd2 : Disjoint ({0} : Finset ℤ) (Finset.Icc (1 : ℤ) K) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc] at hy
    omega
  have hneg : (∑ n ∈ Finset.Icc (-K) (-1 : ℤ), f n) = ∑ n ∈ Finset.Icc (1 : ℤ) K, f n := by
    have h1 : (∑ n ∈ Finset.Icc (-K) (-1 : ℤ), f n)
        = ∑ n ∈ Finset.Icc (1 : ℤ) K, f (-n) := by
      refine Finset.sum_bij (fun n _ => -n) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro n1 hn1 n2 hn2 heq
        simp only [Finset.mem_Icc] at hn1 hn2
        omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        exact ⟨-m, by simp only [Finset.mem_Icc]; omega, by simp⟩
      · intro n _
        simp
    rw [h1]
    exact Finset.sum_congr rfl (fun n _ => hf n)
  rw [← hU1, Finset.sum_union hd1, ← hU2, Finset.sum_union hd2,
    Finset.sum_singleton, hneg]
  ring

/-- `σ₋₁(0) = 0`。 -/
theorem sigmaMinusOne_zero : sigmaMinusOne 0 = 0 := by
  unfold sigmaMinusOne
  simp

/-- `Σ_{|n|≤K} σ₋₁(|n|) ≤ 4K`。 -/
theorem sum_sigmaMinusOne_Icc (K : ℤ) (hK : 0 ≤ K) :
    (∑ n ∈ Finset.Icc (-K) K, sigmaMinusOne n.natAbs) ≤ 4 * (K : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, K = (k : ℤ) := ⟨K.toNat, (Int.toNat_of_nonneg hK).symm⟩
  rw [sum_Icc_symm_rat (k : ℤ) (by positivity)
    (fun n => sigmaMinusOne n.natAbs) (fun n => by rw [Int.natAbs_neg])]
  rw [Int.natAbs_zero, sigmaMinusOne_zero]
  rw [sum_int_Icc_eq_sum_nat_Icc k (fun m => sigmaMinusOne m)]
  have h := sum_sigmaMinusOne_le k
  push_cast
  linarith

/-- `Σ_{|n|≤K} σ₋₁(|n|)² ≤ 12K`。 -/
theorem sum_sigmaMinusOne_sq_Icc (K : ℤ) (hK : 0 ≤ K) :
    (∑ n ∈ Finset.Icc (-K) K, sigmaMinusOne n.natAbs ^ 2) ≤ 12 * (K : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, K = (k : ℤ) := ⟨K.toNat, (Int.toNat_of_nonneg hK).symm⟩
  rw [sum_Icc_symm_rat (k : ℤ) (by positivity)
    (fun n => sigmaMinusOne n.natAbs ^ 2) (fun n => by rw [Int.natAbs_neg])]
  rw [Int.natAbs_zero, sigmaMinusOne_zero]
  rw [sum_int_Icc_eq_sum_nat_Icc k (fun m => sigmaMinusOne m ^ 2)]
  have h := sum_sigmaMinusOne_sq_le k
  push_cast
  linarith

/-- **主计数界**：`qHMCount ≤ Σ_n qQ(n)²`。 -/
theorem qHMCount_le_sum_sq (a b : ℤ) (N : ℕ) :
    qHMCount a b N ≤ ∑ n ∈ Finset.Icc (-(qK a b N)) (qK a b N),
      qQ a b N (2 * N) n ^ 2 := by
  refine le_trans (qHMCount_le_sum_qQ a b N (qK a b N) (fun p hp => qAval_bound a b N hp)) ?_
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [qQ_neg, sq]

/-- `Σ_n qQ(n)²` 的 `N⁶` 界。 -/
theorem sum_qQ_sq_le (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ((∑ n ∈ Finset.Icc (-(qK a b N)) (qK a b N), qQ a b N (2 * N) n ^ 2 : ℕ) : ℚ)
      ≤ 1000000 * ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℚ) * (N : ℚ) ^ 6 := by
  classical
  have hNq : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  set c : ℚ := ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℚ) with hc
  have hc1 : (1 : ℚ) ≤ c := by
    rw [hc]
    have : (1 : ℕ) ≤ 2 * a.natAbs + b.natAbs + 1 := by omega
    exact_mod_cast this
  have hcnn : (0 : ℚ) ≤ c := le_trans zero_le_one hc1
  set A : ℚ := 4 * (N : ℚ) * ((N : ℚ) + 1) with hA
  set B : ℚ := 16 * (N : ℚ) ^ 2 with hB
  set Kz : ℤ := qK a b N with hKz
  have hKz0 : 0 ≤ Kz := by rw [hKz]; exact qK_nonneg a b N
  have hAnn : (0 : ℚ) ≤ A := by rw [hA]; positivity
  have hBnn : (0 : ℚ) ≤ B := by rw [hB]; positivity
  -- 1) cast 与分拆
  have hcast : ((∑ n ∈ Finset.Icc (-Kz) Kz, qQ a b N (2 * N) n ^ 2 : ℕ) : ℚ)
      = ∑ n ∈ Finset.Icc (-Kz) Kz, (qQ a b N (2 * N) n : ℚ) ^ 2 := by
    push_cast
    ring
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-Kz) Kz := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hsplit : (∑ n ∈ Finset.Icc (-Kz) Kz, (qQ a b N (2 * N) n : ℚ) ^ 2)
      = (qQ a b N (2 * N) 0 : ℚ) ^ 2
        + ∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2 := by
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ h0mem).symm
  -- 2) n = 0 项
  have hQ0 : (qQ a b N (2 * N) 0 : ℚ) ^ 2 ≤ 1089 * (N : ℚ) ^ 6 := by
    have h1 : qQ a b N (2 * N) 0 ≤ (2 * N + 1) ^ 2 + 4 * N * (N + 1) * (2 * N + 1) :=
      qQ_zero_le a b ha N (2 * N)
    have h2 : (2 * N + 1) ^ 2 + 4 * N * (N + 1) * (2 * N + 1) ≤ 33 * N ^ 3 := by
      have h3 : (2 * (N : ℚ) + 1) ^ 2 + 4 * (N : ℚ) * ((N : ℚ) + 1) * (2 * (N : ℚ) + 1)
          ≤ 33 * (N : ℚ) ^ 3 := by
        nlinarith [hNq]
      exact_mod_cast h3
    have h4 : (qQ a b N (2 * N) 0 : ℚ) ≤ 33 * (N : ℚ) ^ 3 := by
      have h5 : qQ a b N (2 * N) 0 ≤ 33 * N ^ 3 := le_trans h1 h2
      exact_mod_cast h5
    calc (qQ a b N (2 * N) 0 : ℚ) ^ 2 ≤ (33 * (N : ℚ) ^ 3) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h4 2
      _ = 1089 * (N : ℚ) ^ 6 := by ring
  -- 3) 其余项 ≤ Σ (A + Bσ)²
  have hrest : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2)
      ≤ ∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
    have h1 : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2)
        ≤ ∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_erase] at hn
      obtain ⟨hn0, -⟩ := hn
      have hq := qQ_le_sigma a b ha N (2 * N) hn0
      have hAs : 4 * (N : ℚ) * ((N : ℚ) + 1) = A := by rw [hA]
      have hBs : 8 * (N : ℚ) * ((2 * N : ℕ) : ℚ) = B := by
        rw [hB]
        push_cast
        ring
      rw [hAs, hBs] at hq
      exact pow_le_pow_left₀ (by positivity) hq 2
    have h2 : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (A + B * sigmaMinusOne n.natAbs) ^ 2)
        ≤ ∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset (0 : ℤ) (Finset.Icc (-Kz) Kz)) (fun n _ _ => by positivity)
    linarith [h1, h2]
  -- 4) 展开 Σ (A + Bσ)²
  have hexp : (∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2)
      = ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2
        + 2 * A * B * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs)
        + B ^ 2 * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2) := by
    have hpt : ∀ n : ℤ, (A + B * sigmaMinusOne n.natAbs) ^ 2
        = A ^ 2 + 2 * A * B * sigmaMinusOne n.natAbs
          + B ^ 2 * sigmaMinusOne n.natAbs ^ 2 := fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hpt n)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcK : ((Finset.Icc (-Kz) Kz).card : ℚ) = ((2 * Kz + 1 : ℤ) : ℚ) := by
      rw [Int.card_Icc]
      have h1 : Kz + 1 - (-Kz) = 2 * Kz + 1 := by ring
      rw [h1]
      have h2 : ((2 * Kz + 1).toNat : ℤ) = 2 * Kz + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h2
    have e1 : (∑ n ∈ Finset.Icc (-Kz) Kz, A ^ 2) = ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcK]
    have e2 : (∑ n ∈ Finset.Icc (-Kz) Kz, 2 * A * B * sigmaMinusOne n.natAbs)
        = 2 * A * B * ∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs := by
      rw [Finset.mul_sum]
    have e3 : (∑ n ∈ Finset.Icc (-Kz) Kz, B ^ 2 * sigmaMinusOne n.natAbs ^ 2)
        = B ^ 2 * ∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2 := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3]
  -- 5) 关键放缩
  have hcabs : c = 2 * |(a : ℚ)| + |(b : ℚ)| + 1 := by
    rw [hc]
    push_cast
    simp
  have hKz_ub : (Kz : ℚ) ≤ 2 * (N : ℚ) ^ 2 * c := by
    have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    have ha0 : (0 : ℤ) ≤ (a.natAbs : ℤ) := Int.natCast_nonneg _
    have hb0 : (0 : ℤ) ≤ (b.natAbs : ℤ) := Int.natCast_nonneg _
    have hNle : (N : ℤ) ≤ (N : ℤ) ^ 2 := by nlinarith [hN1]
    have hKz_int : Kz ≤ 2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) := by
      rw [hKz]
      unfold qK
      have hstep : 2 * (N : ℤ) * (b.natAbs : ℤ) ≤ 2 * (N : ℤ) ^ 2 * (b.natAbs : ℤ) := by
        nlinarith [mul_le_mul_of_nonneg_left hNle hb0]
      linarith
    have h1 : (Kz : ℚ) ≤ ((2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) : ℤ) : ℚ) := by
      exact_mod_cast hKz_int
    have h2 : ((2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) : ℤ) : ℚ)
        ≤ 2 * (N : ℚ) ^ 2 * c := by
      have hcast1 : ((2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) : ℤ) : ℚ)
          = 2 * (N : ℚ) ^ 2 * (2 * |(a : ℚ)| + |(b : ℚ)|) := by
        push_cast
        simp
      rw [hcast1, hcabs]
      have hN2 : (0 : ℚ) ≤ (N : ℚ) ^ 2 := by positivity
      have hle : (2 * |(a : ℚ)| + |(b : ℚ)|)
          ≤ 2 * |(a : ℚ)| + |(b : ℚ)| + 1 := by linarith
      nlinarith [hle, hN2]
    linarith [h1, h2]
  have hK1 : ((2 * Kz + 1 : ℤ) : ℚ) ≤ 5 * (N : ℚ) ^ 2 * c := by
    have h1 : ((2 * Kz + 1 : ℤ) : ℚ) = 2 * (Kz : ℚ) + 1 := by push_cast; ring
    rw [h1]
    have hN2 : (1 : ℚ) ≤ (N : ℚ) ^ 2 := by nlinarith [hNq]
    nlinarith [hKz_ub, hN2, hcnn]
  have hA_ub : A ≤ 8 * (N : ℚ) ^ 2 := by
    rw [hA]
    nlinarith [hNq]
  have hA2 : A ^ 2 ≤ 64 * (N : ℚ) ^ 4 := by
    calc A ^ 2 ≤ (8 * (N : ℚ) ^ 2) ^ 2 := pow_le_pow_left₀ hAnn hA_ub 2
      _ = 64 * (N : ℚ) ^ 4 := by ring
  have hAB : A * B ≤ 128 * (N : ℚ) ^ 4 := by
    rw [hB]
    have h2 : A ≤ 8 * (N : ℚ) ^ 2 := hA_ub
    nlinarith [hAnn, hNq]
  have hB2 : B ^ 2 = 256 * (N : ℚ) ^ 4 := by
    rw [hB]
    ring
  -- 6) 主放缩
  have hmain : (∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2)
      ≤ 25000 * c * (N : ℚ) ^ 6 := by
    rw [hexp]
    have hs1 := sum_sigmaMinusOne_Icc Kz hKz0
    have hs2 := sum_sigmaMinusOne_sq_Icc Kz hKz0
    have e1 : 2 * A * B * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs)
        ≤ 2 * A * B * (4 * (Kz : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs1
      positivity
    have e2 : B ^ 2 * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2)
        ≤ B ^ 2 * (12 * (Kz : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs2
      positivity
    have hkey : ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 + 2 * A * B * (4 * (Kz : ℚ))
        + B ^ 2 * (12 * (Kz : ℚ)) ≤ 25000 * c * (N : ℚ) ^ 6 := by
      have hAB2 : A * B ≤ 128 * (N : ℚ) ^ 4 := hAB
      have hKzq : (Kz : ℚ) ≤ 2 * (N : ℚ) ^ 2 * c := hKz_ub
      have h1 : ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 ≤ (5 * (N : ℚ) ^ 2 * c) * (64 * (N : ℚ) ^ 4) := by
        apply mul_le_mul hK1 hA2 (by positivity) (by positivity)
      have h2 : 2 * A * B * (4 * (Kz : ℚ)) ≤ 8 * (128 * (N : ℚ) ^ 4) * (2 * (N : ℚ) ^ 2 * c) := by
        have hAB' : 2 * A * B * 4 ≤ 8 * (128 * (N : ℚ) ^ 4) := by
          nlinarith [hAB2]
        have h := mul_le_mul hAB' hKzq (by positivity) (by positivity)
        nlinarith [h]
      have h3 : B ^ 2 * (12 * (Kz : ℚ)) ≤ (256 * (N : ℚ) ^ 4) * (12 * (2 * (N : ℚ) ^ 2 * c)) := by
        rw [hB2]
        apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
        nlinarith [hKzq]
      have hN6 : (0 : ℚ) ≤ (N : ℚ) ^ 6 := by positivity
      nlinarith [h1, h2, h3, hcnn, hNq, hN6]
    nlinarith [e1, e2, hkey]
  -- 7) 汇总
  rw [hcast, hsplit]
  nlinarith [hQ0, hrest, hmain, hc1, hcnn, hNq]

/-- **Theorem 1（`k = 2`，一般二次形式）**：`qEqCount ≤ C·N⁶`。 -/
theorem qEqCount_le (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    qEqCount a b N ≤ 1000000 * (2 * a.natAbs + b.natAbs + 1) * N ^ 6 := by
  refine le_trans (le_trans (qEqCount_le_qHMCount a b N) (qHMCount_le_sum_sq a b N)) ?_
  have h := sum_qQ_sq_le a b ha N hN
  have h2 : ((1000000 * (2 * a.natAbs + b.natAbs + 1) * N ^ 6 : ℕ) : ℚ)
      = 1000000 * ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℚ) * (N : ℚ) ^ 6 := by
    push_cast
    ring
  rw [← h2] at h
  exact_mod_cast h

/-- **Theorem 1（`k = 2`，一般二次形式）的积分形式**：
`∫₀¹ |∑_{n≤N} e(α(a n² + b n))|⁸ dα ≤ 10⁶·(2|a|+|b|+1)·N⁶`。 -/
theorem integral_normSq_pow_four_le_q (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (qSum a b N α)) ^ 4)
      ≤ 1000000 * ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℝ) * (N : ℝ) ^ 6 := by
  rw [integral_normSq_pow_four_q]
  have h := qEqCount_le a b ha N hN
  have h' : (qEqCount a b N : ℝ) ≤ ((1000000 * (2 * a.natAbs + b.natAbs + 1) * N ^ 6 : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h' ⊢
  exact h'

end Waring