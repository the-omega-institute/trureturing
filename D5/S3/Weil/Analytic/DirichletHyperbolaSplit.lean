/- GID: D5/S3/Weil/Analytic/DirichletHyperbolaSplit
   generality: I
   mirror-B: none(waiver:mobius-log-fourth-support)
   mirror-E: none(waiver:mobius-log-fourth)
   anchors: []
   utility: none
   digest: A finite Dirichlet convolution splits at an arbitrary positive cutoff. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! A finite Dirichlet hyperbola split at an arbitrary integer cutoff. -/

set_option autoImplicit false

open Finset

namespace ArithmeticFunction

theorem sum_convolution_split_at {R : Type*} [CommRing R]
    (f g : ArithmeticFunction R) (N Y : ℕ) (hY : Y ≤ N) :
    (∑ n ∈ Ioc 0 N, (f * g) n) =
      (∑ d ∈ Ioc 0 Y, f d * ∑ m ∈ Ioc 0 (N / d), g m) +
      (∑ m ∈ Ioc 0 (N / (Y + 1)), g m *
        ((∑ d ∈ Ioc 0 (N / m), f d) - ∑ d ∈ Ioc 0 Y, f d)) := by
  let head : ArithmeticFunction R :=
    ⟨fun n => if n ≤ Y then f n else 0, by simp⟩
  let tail : ArithmeticFunction R :=
    ⟨fun n => if ¬n ≤ Y then f n else 0, by simp⟩
  have hhead (n : ℕ) : head n = if n ≤ Y then f n else 0 := rfl
  have htail (n : ℕ) : tail n = if ¬n ≤ Y then f n else 0 := rfl
  have hf : head + tail = f := by
    ext n
    rw [add_apply, hhead, htail]
    by_cases hn : n ≤ Y <;> simp [hn]
  have hsmall :
      (∑ n ∈ Ioc 0 N, (head * g) n) =
        ∑ d ∈ Ioc 0 Y, f d * ∑ m ∈ Ioc 0 (N / d), g m := by
    rw [sum_Ioc_mul_eq_sum_sum]
    simp_rw [hhead, ite_mul, zero_mul, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [mem_filter, mem_Ioc]
    omega
  have hlarge :
      (∑ n ∈ Ioc 0 N, (tail * g) n) =
        ∑ m ∈ Ioc 0 (N / (Y + 1)), g m *
          ((∑ d ∈ Ioc 0 (N / m), f d) - ∑ d ∈ Ioc 0 Y, f d) := by
    rw [mul_comm tail g, sum_Ioc_mul_eq_sum_sum]
    have hsubset : Ioc 0 (N / (Y + 1)) ⊆ Ioc 0 N :=
      fun m hm => mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1,
        (mem_Ioc.mp hm).2.trans (Nat.div_le_self _ _)⟩
    have cutoff {m : ℕ} (hm : 0 < m) : Y + 1 ≤ N / m ↔ m ≤ N / (Y + 1) := by
      rw [Nat.le_div_iff_mul_le hm, Nat.le_div_iff_mul_le (Nat.succ_pos Y), mul_comm]
    calc
      _ = ∑ m ∈ Ioc 0 (N / (Y + 1)), g m * ∑ d ∈ Ioc 0 (N / m), tail d := by
        symm
        apply Finset.sum_subset hsubset
        intro m hm hn
        have hd : N / m ≤ Y := by
          have hm₀ := (mem_Ioc.mp hm).1
          have hnot : ¬m ≤ N / (Y + 1) := fun h => hn (mem_Ioc.mpr ⟨hm₀, h⟩)
          have hnot' : ¬Y + 1 ≤ N / m := fun h => hnot ((cutoff hm₀).mp h)
          omega
        have hz : (∑ d ∈ Ioc 0 (N / m), tail d) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd'
          rw [htail, ite_eq_right (not_not.mpr ((mem_Ioc.mp hd').2.trans hd))]
        rw [hz, mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        have hYm : Y ≤ N / m :=
          (Nat.le_succ Y).trans ((cutoff (mem_Ioc.mp hm).1).mpr (mem_Ioc.mp hm).2)
        congr 1
        simp_rw [htail]
        rw [← Finset.sum_filter]
        have hfilter : (Ioc 0 (N / m)).filter (fun d => ¬d ≤ Y) = Ioc Y (N / m) := by
          ext d
          simp only [mem_filter, mem_Ioc]
          omega
        rw [hfilter, ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le Y) hYm,
          Finset.sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
        exact (add_sub_cancel_left _ _).symm
  calc
    _ = ∑ n ∈ Ioc 0 N, ((head * g) n + (tail * g) n) := by
      rw [← hf, add_mul]
      simp only [add_apply]
    _ = _ := by rw [Finset.sum_add_distrib, hsmall, hlarge]

end ArithmeticFunction
