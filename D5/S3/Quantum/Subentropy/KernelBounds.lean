/- GID: D5/S3/Quantum/Subentropy/KernelBounds
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/KernelBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Basic]
   utility: none
   digest: Uniform integrable bounds for the determinant subentropy kernel. -/

import D5.S3.Quantum.Subentropy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The classical determinant kernel is bounded by a common inverse-square envelope. -/
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators
namespace D5.S3.Quantum.Subentropy.KernelBounds
open _root_.D5.S3.Quantum.Subentropy.Basic

private theorem reciprocal_product_tangent {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    1 - ∑ i, (b i - a i) / a i ≤ ∏ i, a i / b i := by
  have hlog : ∑ i, Real.log (b i / a i) ≤ ∑ i, (b i - a i) / a i := by
    apply Finset.sum_le_sum
    intro i _
    convert Real.log_le_sub_one_of_pos (div_pos (hb i) (ha i)) using 1 <;>
      field_simp [(ha i).ne'] <;> ring
  have hexp := Real.add_one_le_exp (-∑ i, Real.log (b i / a i))
  have heq : Real.exp (-∑ i, Real.log (b i / a i)) = ∏ i, a i / b i := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.exp_neg, Real.exp_log (div_pos (hb i) (ha i)), inv_div]
  rw [heq] at hexp
  linarith

private theorem one_add_sum_le_product {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hai := ha i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hs := Finset.sum_nonneg has
    have h := mul_le_mul_of_nonneg_left (ih has) (by linarith : 0 ≤ 1 + a i)
    nlinarith

/-- Every classical probability vector has a nonnegative kernel with the sharp
vertex envelope, including vectors containing zero coordinates. -/
theorem classical_kernel_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (x : ι) (t : ℝ) (ht : 0 < t) :
    0 ≤ subentropyKernel (diagonal (fun i => (p i : ℂ))) t ∧
      subentropyKernel (diagonal (fun i => (p i : ℂ))) t ≤
        (1 - p x) / (1 + t)^2 := by
  rw [kernel_diagonal p t ht.ne']
  have ht1 : 0 < 1 + t := by linarith
  have hpi : ∀ i, 0 < t + p i := fun i => add_pos_of_pos_of_nonneg ht (hp i)
  constructor
  · have hprod := one_add_sum_le_product Finset.univ (fun i => p i / t)
      (fun i _ => div_nonneg (hp i) ht.le)
    simp only [← Finset.sum_div, hsum] at hprod
    have hfactor : ∀ i, t / (t + p i) = (1 + p i / t)⁻¹ := by
      intro i
      field_simp
      <;> ring
    simp_rw [hfactor]
    rw [Finset.prod_inv_distrib]
    have hpos : 0 < ∏ i, (1 + p i / t) :=
      Finset.prod_pos (fun i _ => by have := hp i; positivity)
    have hbase : (1 + 1 / t)⁻¹ = t / (1 + t) := by field_simp; ring
    have h := one_div_le_one_div_of_le (by positivity : 0 < 1 + 1 / t) hprod
    simp only [one_div] at h
    simp only [one_div] at hbase
    rw [hbase] at h
    linarith
  · let q : ι → ℝ := fun i => if i = x then 1 else 0
    have hq : ∀ i, 0 ≤ q i := by intro i; simp only [q]; split_ifs <;> norm_num
    have hqi : ∀ i, 0 < t + q i := fun i => add_pos_of_pos_of_nonneg ht (hq i)
    have htan := reciprocal_product_tangent (fun i => t + q i)
      (fun i => t + p i) hqi hpi
    have hvertex : ∏ i, t / (t + q i) = t / (1 + t) := by
      rw [Finset.prod_eq_single x]
      · simp [q, add_comm]
      · intro i _ hi
        simp [q, hi, ht.ne']
      · simp
    have hsumq : ∑ i, (t + p i - (t + q i)) / (t + q i) =
        (1 - p x) / (t * (1 + t)) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
      have he : ∀ i ∈ Finset.univ.erase x,
          (t + p i - (t + q i)) / (t + q i) = p i / t := by
        intro i hi
        have hix : i ≠ x := (Finset.mem_erase.mp hi).1
        simp [q, hix]
      rw [Finset.sum_congr rfl he, ← Finset.sum_div]
      have hsp : ∑ i ∈ Finset.univ.erase x, p i = 1 - p x := by
        have h := Finset.sum_erase_add Finset.univ p (Finset.mem_univ x)
        rw [hsum] at h
        linarith
      rw [hsp]
      simp only [q, if_pos rfl]
      field_simp
      <;> ring
    rw [hsumq] at htan
    have hmul := mul_le_mul_of_nonneg_left htan (div_nonneg ht.le ht1.le)
    have heq : t / (1 + t) * ∏ i, (t + q i) / (t + p i) =
        ∏ i, t / (t + p i) := by
      rw [← hvertex, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      field_simp [(hqi i).ne', (hpi i).ne']
    rw [heq] at hmul
    have halg : t / (1 + t) * (1 - (1 - p x) / (t * (1 + t))) =
        t / (1 + t) - (1 - p x) / (1 + t)^2 := by
      field_simp
      <;> ring
    rw [halg] at hmul
    linarith

end D5.S3.Quantum.Subentropy.KernelBounds
