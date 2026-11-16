/- GID: D5/S3/Analytic/PowerSeries/ScalarComposition
   generality: G
   mirror-B: D5/B/S3/Analytic/PowerSeries/ScalarComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar power series substitution realizes ordered multilinear composition. -/

import Batteries.Data.List.Scan
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/ado-log-LICENSE.txt.
Authors: Miyahara Kō

Adapted from Komyyy/ado, acac59b08bfc356fdf5f3966ad95ad8edf7a3202,
AdoArchive/Log.lean. Modification notice: this leaf retains only the scalar
realization, its evaluation, and substitution correspondence. The ordered
product step directly instantiates the host List.foldr_hom₂ and
mul_smul_mul_comm; the source list-product lemmas are omitted.
Retirement: replace this leaf and every consumer by direct imports when
this repository's own mathlib pin supplies an equivalent correspondence.
-/

noncomputable section
open Function Set FormalMultilinearSeries PowerSeries Finset
variable {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalRing E]
namespace PowerSeries

noncomputable def toFMS (P : 𝕜⟦X⟧) : FormalMultilinearSeries 𝕜 E E :=
  ofScalars E (coeff · P)

variable (P : 𝕜⟦X⟧)

variable {E} in
@[simp]
lemma toFMS_apply (n : ℕ) (v : Fin n → E) :
    toFMS E P n v = coeff n P • List.prod (List.ofFn v) := by
  simp [toFMS, ofScalars]

lemma toFMS_subst (P Q : 𝕜⟦X⟧) (hP : HasSubst P) :
    toFMS E (subst P Q) = FormalMultilinearSeries.comp (toFMS E Q) (toFMS E P) := by
  have prod_smul {m : ℕ} (f : Fin m → 𝕜) (g : Fin m → E) :
      (List.ofFn (fun i => f i • g i)).prod =
        (List.ofFn f).prod • (List.ofFn g).prod := by
    simpa only [List.ofFn_eq_map, List.prod_eq_foldr, List.foldr_map, one_smul] using
      (List.foldr_hom₂ (List.finRange m) (fun a b => a • b)
        (fun i a => f i * a) (fun i b => g i * b)
        (fun i c => (f i • g i) * c) (1 : 𝕜) (1 : E)
        (fun a b i => mul_smul_mul_comm (f i) a (g i) b))
  ext n v
  conv_lhs =>
    calc
      _ = ∑ᶠ k : ℕ, ∑ i ∈ finsuppAntidiag (range k) n,
          (coeff k Q * ∏ j ∈ range k, coeff (i j) P) • (List.prod (List.ofFn v)) := by
        simp [coeff_subst' hP, coeff_pow, mul_sum, finsum_smul, sum_smul]
      _ = ∑ᶠ k : ℕ, ∑ i ∈ finsuppAntidiag (range k) n with ∀ j ∈ range k, 0 < i j,
          (coeff k Q * ∏ j ∈ range k, coeff (i j) P) • (List.prod (List.ofFn v)) := by
        congr! 2 with k
        symm
        apply sum_eq_of_subset (filter_subset _ _)
        intro i hi₁ hi₂
        rw [mem_filter] at hi₂
        push Not at hi₂
        apply hi₂ at hi₁
        obtain ⟨j, hj, hj₂⟩ := hi₁
        rw [nonpos_iff_eq_zero] at hj₂
        suffices h : coeff (i j) P = 0 by rw [prod_eq_zero hj (by simp [h])]; simp
        simp_rw [hj₂, coeff_zero_eq_constantCoeff_apply, ← isNilpotent_iff_eq_zero, constantCoeff,
          hP]
      _ = ∑ k ≤ n, ∑ i ∈ finsuppAntidiag (range k) n with ∀ j ∈ range k, 0 < i j,
          (coeff k Q * ∏ j ∈ range k, coeff (i j) P) • (List.prod (List.ofFn v)) := by
        apply finsum_eq_finsetSum_of_support_subset
        simp_rw +singlePass [← Set.compl_subset_compl, compl_support, coe_Iic, compl_Iic,
          Finset.mem_range, ← Set.Ioi_def, Set.ofPred_subset_ofPred]
        intro m hm
        convert Finset.sum_empty
        simp_rw [Finset.eq_empty_iff_forall_notMem, mem_filter, and_comm (a := _ ∈ _), not_and,
          mem_finsuppAntidiag, Nat.lt_iff_add_one_le (m := 0), zero_add]
        intro i hi
        simp_rw [← Finset.mem_range] at hi
        apply Finset.sum_le_sum at hi
        grw [sum_const, card_range, smul_eq_mul, mul_one, ← hm] at hi
        simp_rw [Classical.not_and_iff_not_or_not, hi.ne', not_false_iff, true_or]
      _ =
          let (k : ℕ) : Fintype ↥{b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n} :=
            Fintype.ofEquiv _ (finsuppAntidiagEquivSubtype (range k) n)
          ∑ k ≤ n,
            ∑ b ∈ {b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n}.toFinset with
                ∀ j, 0 < b j, (coeff k Q * ∏ j, coeff (b j) P) • (List.prod (List.ofFn v)) := by
        extract_lets
        simp_rw +singlePass [Finset.sum_filter, ← Finset.sum_coe_sort (finsuppAntidiag (range _) n),
          ← Finset.sum_set_coe, ← Finset.sum_filter]
        congr! 1 with k hk
        apply sum_equiv (finsuppAntidiagEquivSubtype (range k) n)
        · simp
        · simp_rw [Finset.finsuppAntidiagEquivSubtype_apply_coe, Finsupp.subtypeDomain_apply,
            ← Finset.prod_coe_sort (range k), forall_true_iff]
      _ =
          let (k : ℕ) : Fintype ↥{b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n} :=
            Fintype.ofEquiv _ (finsuppAntidiagEquivSubtype (range k) n)
          let e (k : ℕ) : ↥{b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n} ≃
              ↥{b : Fin k → ℕ | ∑ i, b i = n} :=
            { toFun x :=
                ⟨fun i ↦ x.1 ⟨i.1, by simp⟩, by
                  simpa [Finsupp.sum_fintype, ← sum_attach (range k),
                    sum_fin_eq_sum_range, - Subtype.coe_prop,
                    show ∀ x : range k, x.1 < k by simp] using x.2⟩
              invFun x :=
                ⟨Finsupp.equivFunOnFinite.symm
                    (fun i ↦ x.1 ⟨i.1, by simpa [- SetLike.coe_mem] using i.2⟩), by
                  simpa [Finsupp.sum_fintype, ← sum_attach (range k),
                    sum_fin_eq_sum_range, - Subtype.coe_prop,
                    show ∀ x : range k, x.1 < k by simp] using x.2⟩ }
          let (k : ℕ) : Fintype ↥{b : Fin k → ℕ | ∑ i, b i = n} :=
            Fintype.ofEquiv _ (e k)
          ∑ k ≤ n,
            ∑ b ∈ {b : Fin k → ℕ | ∑ i, b i = n}.toFinset with
                ∀ j, 0 < b j, (coeff k Q * ∏ j, coeff (b j) P) • (List.prod (List.ofFn v)) := by
        extract_lets _ _ e _
        congr! 1 with k hk
        simp_rw [Finset.sum_filter, ← Finset.sum_set_coe, ← Finset.sum_filter]
        have he i j : (e k i).1 j = i.1 ⟨j.1, by simp⟩ := rfl
        apply sum_equiv (e k)
        · simp [he, Fin.forall_iff]
        · simp [he, prod_fin_eq_prod_range, ← prod_attach (range k),
            show ∀ x : range k, x.1 < k by simp]
      _ = ∑ c : Composition n,
          (coeff c.length Q * ∏ j, coeff (c.blocksFun j) P) • (List.prod (List.ofFn v)) := by
        extract_lets
        symm
        rw [sum_sigma']
        let e : Composition n ≃
            Finset.sigma (Finset.Iic n) (fun k ↦ filter (fun b ↦ ∀ j, 0 < b j)
              {b : Fin k → ℕ | ∑ i, b i = n}.toFinset) :=
          { toFun c := ⟨⟨c.length, c.blocksFun⟩, by simp [Nat.lt_iff_add_one_le]⟩
            invFun x :=
              { blocks := List.ofFn x.1.2
                blocks_pos {j} hj := by
                  have h := x.2
                  rw [mem_sigma, mem_filter] at h
                  rw [List.mem_ofFn] at hj
                  obtain ⟨j, rfl⟩ := hj
                  simp [h]
                blocks_sum := by
                  have h := x.2
                  rw [mem_sigma, mem_filter, mem_toFinset, Set.mem_ofPred] at h
                  simp [List.sum_ofFn, h] }
            left_inv c := by ext : 1; simp
            right_inv x := by
              ext <;> simp [Composition.length, Composition.blocksFun, Fin.heq_fun_iff] }
        simp_rw [← sum_attach (Finset.sigma _ _)]
        apply sum_equiv e
        · simp
        · simp [e]
  conv_rhs =>
    tactic =>
      simp_rw [FormalMultilinearSeries.comp, _root_.sum_apply, compAlongComposition_apply,
        toFMS_apply]
      unfold applyComposition
      simp_rw [toFMS_apply, prod_smul, smul_smul, Fin.prod_ofFn,
        List.ofFn_comp' (g := List.prod), ← List.prod_flatten, ← List.map_ofFn,
        List.ofFn_comp' (g := List.map v), ← List.map_flatten]
  rw [List.ofFn_eq_map]
  congr! with c -
  apply List.ext_getElem
  · simp [List.sum_ofFn]
  · intro j hj₁ hj₂
    ext
    simp_rw [List.getElem_finRange, Fin.val_cast]
    symm
    simp_rw -zeta [List.getElem_flatten]
    extract_lets k₁ hk₁ k₂ hk₂
    subst hk₁ hk₂
    simp_rw [List.getElem_ofFn]
    have hk₁ : k₁ = c.index ⟨j, by simpa using hj₁⟩ := by
      simp_rw [k₁, List.map_ofFn, comp_def, List.length_ofFn]
      rw [Nat.sub_eq_iff_eq_add (by simp [Nat.add_one_le_iff]), List.findIdx_eq (by simp)]
      constructor
      · rw [decide_eq_true_iff, List.getElem_partialSums, Composition.ofFn_blocksFun,
          ← Composition.sizeUpTo]
        apply c.lt_sizeUpTo_index_succ ⟨j, by simpa using hj₁⟩
      · intro j₂ hj₂
        rw [Nat.lt_add_one_iff] at hj₂
        grw [decide_eq_false_iff_not, gt_iff_lt, not_lt, List.getElem_partialSums,
          Composition.ofFn_blocksFun, ← Composition.sizeUpTo, c.monotone_sizeUpTo.imp hj₂]
        apply c.sizeUpTo_index_le ⟨j, by simpa using hj₁⟩
    have hk₂ : k₂ = c.invEmbedding ⟨j, by simpa using hj₁⟩ := by
      simp_rw [k₂, List.length_flatten, List.map_take, List.map_ofFn, comp_def, List.length_ofFn,
        Composition.ofFn_blocksFun]
      rw [← Composition.sizeUpTo]
      simp_rw [Composition.coe_invEmbedding, hk₁]
    simp_rw [c.coe_embedding]
    rw [hk₁, hk₂, ← c.coe_embedding, c.embedding_comp_inv]

end PowerSeries
