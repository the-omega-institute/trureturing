/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A symmetric translation-invariant kernel has the exact prefix rectangle identity. -/

import Mathlib

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section

def kernelRectSum (K : ℕ → ℕ → ℝ) (m n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 n, K i j

def kernelSquareSum (K : ℕ → ℕ → ℝ) (m : ℕ) : ℝ := kernelRectSum K m m

private lemma sum_bij_shift {f : ℕ → ℝ} {m r : ℕ} :
    (∑ x ∈ Finset.Ioc m (m + r), f x) =
      ∑ y ∈ Finset.Icc 1 r, f (m + y) := by
  have hshift := Finset.sum_Ico_add f 1 (r + 1) m
  rw [Nat.add_comm 1 m, show (r + 1) + m = (m + r) + 1 by omega,
    Finset.Ico_add_one_add_one_eq_Ioc, Finset.Ico_add_one_right_eq_Icc] at hshift
  exact hshift.symm

private lemma sum_partition {f : ℕ → ℕ → ℝ} {m r : ℕ} :
    (∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 (m + r), f i j) =
      (∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 m, f i j) +
      ∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Ioc m (m + r), f i j := by
  have hsplit (i : ℕ) :
      (∑ j ∈ Finset.Icc 1 (m + r), f i j) =
        (∑ j ∈ Finset.Icc 1 m, f i j) + ∑ j ∈ Finset.Ioc m (m + r), f i j := by
    simpa only [← Finset.Icc_add_one_left_eq_Ioc, zero_add] using
      (Finset.sum_Ioc_consecutive (f i) (Nat.zero_le m) (Nat.le_add_right m r)).symm
  simp_rw [hsplit, Finset.sum_add_distrib]

private lemma square_partition {K : ℕ → ℕ → ℝ} (hsym : ∀ d e, K d e = K e d)
    (htrans : ∀ d e t, K (d + t) (e + t) = K d e) (m r : ℕ) :
    kernelSquareSum K (m + r) = kernelSquareSum K m + kernelSquareSum K r +
      2 * (∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Ioc m (m + r), K i j) := by
  classical
  unfold kernelSquareSum kernelRectSum
  rw [show Finset.Icc 1 (m + r) = Finset.Icc 1 m ∪ Finset.Ioc m (m + r) by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega]
  have hd : Disjoint (Finset.Icc 1 m) (Finset.Ioc m (m + r)) :=
    Finset.disjoint_left.2 (by simp; omega)
  simp_rw [Finset.sum_union hd]
  · rw [Finset.sum_add_distrib]
    simp only [Finset.sum_add_distrib]
    have htop :
        (∑ i ∈ Finset.Ioc m (m + r), ∑ j ∈ Finset.Ioc m (m + r), K i j) =
          kernelSquareSum K r := by
      unfold kernelSquareSum kernelRectSum
      rw [sum_bij_shift (f := fun i => ∑ j ∈ Finset.Ioc m (m + r), K i j)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [sum_bij_shift (f := fun j => K (m + i) j)]
      apply Finset.sum_congr rfl
      intro j hj
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htrans i j m
    rw [htop]
    have hcross :
        (∑ i ∈ Finset.Ioc m (m + r), ∑ j ∈ Finset.Icc 1 m, K i j) =
          ∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Ioc m (m + r), K i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hsym _ _
    rw [hcross]
    simp only [kernelSquareSum, kernelRectSum]
    ring

private lemma rect_partition {K : ℕ → ℕ → ℝ} (m r : ℕ) :
    kernelRectSum K m (m + r) = kernelSquareSum K m +
      ∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Ioc m (m + r), K i j := by
  exact sum_partition (f := K)

theorem prefix_identity (K : ℕ → ℕ → ℝ)
    (hsym : ∀ d e, K d e = K e d)
    (htrans : ∀ d e t, K (d + t) (e + t) = K d e) (m n : ℕ) :
    kernelRectSum K m n = (kernelSquareSum K m + kernelSquareSum K n - kernelSquareSum K (Nat.dist m n)) / 2 := by
  classical
  rcases le_total m n with hmn | hnm
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
    simp only [Nat.dist_eq_sub_of_le (Nat.le_add_right m r), Nat.add_sub_cancel_left]
    have hp := rect_partition (K := K) m r
    have hs := square_partition hsym htrans m r
    linarith
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
    simp only [Nat.dist_eq_sub_of_le_right (Nat.le_add_right n r), Nat.add_sub_cancel_left]
    have hp := rect_partition (K := K) n r
    have hs := square_partition hsym htrans n r
    have ht : kernelRectSum K (n + r) n = kernelRectSum K n (n + r) := by
      unfold kernelRectSum
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hsym _ _
    rw [ht]
    linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
