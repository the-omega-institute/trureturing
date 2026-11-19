/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive signless energy for arbitrary repeated-pair tails. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairSupport
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions

/-! Source: repeated-pair-product-tail, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02, blob
66664013207b88567bf74f1a9a0c6eaf65d07f24. The signless-energy proof below
is a proof representation of the full arbitrary-index lower endpoint.
It retains every tail subset, including the empty-support loop. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairProductTail
open RepeatedPairSupport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weight (k : ι → ℝ) (T : Finset ι) : ℝ := ∏ i ∈ T, k i

private theorem weight_pos (k : ι → ℝ) (hk : ∀ i, 0 < k i) (T : Finset ι) :
    0 < weight k T := by
  exact prod_pos (fun i _ => hk i)

private theorem degree (k : ι → ℝ) (T : Finset ι) :
    (∑ U : Finset ι, if Disjoint T U then weight k U else 0) =
      diagonalFactor k T := by
  have hsub (U : Finset ι) : Disjoint T U ↔ U ⊆ univ \ T := by
    constructor
    · intro h i hi
      exact mem_sdiff.mpr ⟨mem_univ i,fun ht => Finset.disjoint_left.mp h ht hi⟩
    · intro h
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp (h hj)).2 hi
  simp_rw [hsub]
  have hf : (univ : Finset (Finset ι)).filter (fun U => U ⊆ univ \ T) =
      (univ \ T).powerset := by ext U; simp
  rw [← Finset.sum_filter,hf]
  exact (Finset.prod_add_one (univ \ T)).symm

private theorem action (a : ℝ) (k : ι → ℝ) (h : Finset ι → ℝ) (T : Finset ι) :
    ((K a k-1)*ᵥh) T = ((a+1)*diagonalFactor k T-1)*h T+
      a*(∑ U, if Disjoint T U then weight k U*h U else 0) := by
  rw [K,sub_mulVec,add_mulVec,smul_mulVec,one_mulVec]
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mulVec_diagonal]
  simp only [mulVec,dotProduct,disjointKernel,ite_mul,zero_mul,weight]
  ring

private theorem square_sum (k : ι → ℝ) (h : Finset ι → ℝ) :
    (∑ T, ∑ U, if Disjoint T U then weight k T*weight k U*(h T+h U)^2 else 0) =
      2*((∑ T, weight k T*diagonalFactor k T*(h T)^2)+
        ∑ T, weight k T*h T*(∑ U, if Disjoint T U then weight k U*h U else 0)) := by
  have hrow (T : Finset ι) :
      (∑ U, if Disjoint T U then weight k T*weight k U*(h T)^2 else 0) =
        weight k T*diagonalFactor k T*(h T)^2 := by
    have he (U : Finset ι) :
        (if Disjoint T U then weight k T*weight k U*(h T)^2 else 0) =
          (if Disjoint T U then weight k U else 0)*(weight k T*(h T)^2) := by
      split_ifs <;> ring
    simp_rw [he]
    rw [← sum_mul,degree]
    ring
  have hcross (T : Finset ι) :
      (∑ U, if Disjoint T U then weight k T*weight k U*h T*h U else 0) =
        weight k T*h T*(∑ U, if Disjoint T U then weight k U*h U else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro U _
    split_ifs <;> ring
  have hcol :
      (∑ T, ∑ U, if Disjoint T U then weight k T*weight k U*(h U)^2 else 0) =
        ∑ T, weight k T*diagonalFactor k T*(h T)^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro T _
    rw [← hrow T]
    apply sum_congr rfl
    intro U _
    simp only [disjoint_comm]
    split_ifs <;> ring
  have hsplit (T U : Finset ι) :
      (if Disjoint T U then weight k T*weight k U*(h T+h U)^2 else 0) =
        (if Disjoint T U then weight k T*weight k U*(h T)^2 else 0)+
        (if Disjoint T U then weight k T*weight k U*(h U)^2 else 0)+
        2*(if Disjoint T U then weight k T*weight k U*h T*h U else 0) := by
    split_ifs <;> ring
  simp_rw [hsplit,sum_add_distrib,← mul_sum]
  rw [hcol]
  simp_rw [hrow,hcross]
  ring

private theorem square_sum_pos (k : ι → ℝ) (hk : ∀ i, 0 < k i)
    (h : Finset ι → ℝ) (hh : h ≠ 0) :
    0 < ∑ T, ∑ U, if Disjoint T U then weight k T*weight k U*(h T+h U)^2 else 0 := by
  have hn (T U : Finset ι) :
      0 ≤ (if Disjoint T U then weight k T*weight k U*(h T+h U)^2 else 0) := by
    split_ifs
    · exact mul_nonneg (mul_pos (weight_pos k hk T) (weight_pos k hk U)).le (sq_nonneg _)
    · exact le_rfl
  have hrow (T : Finset ι) :
      0 ≤ ∑ U, if Disjoint T U then weight k T*weight k U*(h T+h U)^2 else 0 :=
    sum_nonneg (fun U _ => hn T U)
  by_cases h0 : h ∅ = 0
  · obtain ⟨T,hT⟩ : ∃ T, h T ≠ 0 := Function.ne_iff.mp hh
    apply Finset.sum_pos'
    · exact fun U _ => hrow U
    · refine ⟨T,mem_univ _,?_⟩
      apply Finset.sum_pos'
      · exact fun U _ => hn T U
      · refine ⟨∅,mem_univ _,?_⟩
        simpa [weight,h0] using mul_pos (weight_pos k hk T) (sq_pos_of_ne_zero hT)
  · apply Finset.sum_pos'
    · exact fun U _ => hrow U
    · refine ⟨∅,mem_univ _,?_⟩
      apply Finset.sum_pos'
      · exact fun U _ => hn ∅ U
      · refine ⟨∅,mem_univ _,?_⟩
        simp only [weight,prod_empty,disjoint_empty_left,ite_true,one_mul]
        exact sq_pos_of_ne_zero (by simpa [two_mul] using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) h0)

/-- The full weighted quadratic form of K minus the identity is strictly
positive on every nonzero tail function, for every positive real parameter.
The empty tail, every tail size and every positive real weight remain in scope. -/
theorem lower_energy (a : ℝ) (k : ι → ℝ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (h : Finset ι → ℝ) (hh : h ≠ 0) :
    0 < ∑ T, weight k T*h T*(((K a k-1)*ᵥh) T) := by
  have hs := square_sum_pos k hk h hh
  rw [square_sum] at hs
  have hd (T : Finset ι) : 1 ≤ diagonalFactor k T := by
    unfold diagonalFactor
    induction (univ \ T) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [prod_insert hi]
      nlinarith [hk i]
  have hn : 0 ≤ ∑ T, weight k T*(diagonalFactor k T-1)*(h T)^2 := by
    apply sum_nonneg
    intro T _
    exact mul_nonneg (mul_nonneg (weight_pos k hk T).le (sub_nonneg.mpr (hd T))) (sq_nonneg _)
  have hid :
      (∑ T, weight k T*h T*(((K a k-1)*ᵥh) T)) =
        a*((∑ T, weight k T*diagonalFactor k T*(h T)^2)+
          ∑ T, weight k T*h T*(∑ U, if Disjoint T U then weight k U*h U else 0))+
        ∑ T, weight k T*(diagonalFactor k T-1)*(h T)^2 := by
    rw [mul_add,mul_sum,mul_sum,← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro T _
    rw [action]
    ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg (mul_pos ha (by linarith)) hn

/-- Every full repeated-pair eigenvalue exceeds one; no fixed tail size
or sampled parameter restriction enters this strict lower endpoint. -/
theorem eigenvalue_gt_one (a : ℝ) (k : ι → ℝ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (e : ℝ) (h : Finset ι → ℝ) (hh : h ≠ 0) (he : K a k *ᵥ h = e • h) : 1 < e := by
  have hp := lower_energy a k ha hk h hh
  have hn : 0 < ∑ T, weight k T*(h T)^2 := by
    apply sum_pos'
    · exact fun T _ => mul_nonneg (weight_pos k hk T).le (sq_nonneg _)
    · obtain ⟨T,hT⟩ : ∃ T, h T ≠ 0 := Function.ne_iff.mp hh
      exact ⟨T,mem_univ _,mul_pos (weight_pos k hk T) (sq_pos_of_ne_zero hT)⟩
  have hid : (∑ T, weight k T*h T*(((K a k-1)*ᵥh) T)) =
      (e-1)*(∑ T, weight k T*(h T)^2) := by
    rw [sub_mulVec,he,one_mulVec,mul_sum]
    apply sum_congr rfl
    intro T _
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hid] at hp
  nlinarith

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairProductTail
