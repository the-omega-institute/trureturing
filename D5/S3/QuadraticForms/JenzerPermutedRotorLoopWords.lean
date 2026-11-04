/- GID: D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/JenzerPermutedRotorLoopWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced exterior words cancel odd full-support coefficients. -/

/-
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22564
admission_basis: escape-witness.
escape_witness: ExteriorWord.perm_factor.
Per-declaration proof_shape; names are relative to this module namespace:
ComplementBridge.canonical_complementary_trace: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.scalar_pair_split.
ComplementBridge.canonical_exterior_top: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.scalar_pair_split.
ComplementBridge.complement_ne_self: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.scalar_pair_split.
ComplementBridge.complementary_trace_exterior: proof_shape: bind-only. Consumers: ComplementBridge.canonical_complementary_trace.
ComplementBridge.complementary_trace_word: proof_shape: bind-only. Consumers: ComplementBridge.complementary_trace_exterior.
ComplementBridge.exterior_top_word: proof_shape: bind-only. Consumers: ComplementBridge.canonical_exterior_top, ComplementBridge.complementary_trace_exterior.
Expansion.coeff: proof_shape: definition. Consumers: ExteriorSum.exterior_return_expansion, Expansion.product_expansion, chain_expansion, Expansion.coeff_neg, return_expansion, Expansion.coeff_insert_absent, Expansion.coeff_insert_present, ExteriorSum.plus_expansion.
Expansion.coeff_insert_absent: proof_shape: bind-only. Consumers: Expansion.product_expansion.
Expansion.coeff_insert_present: proof_shape: bind-only. Consumers: Expansion.product_expansion.
Expansion.coeff_neg: proof_shape: bind-only. Consumers: return_expansion.
Expansion.product_expansion: proof_shape: bind-only. Consumers: ExteriorSum.exterior_return_expansion, chain_expansion, return_expansion, ExteriorSum.plus_expansion.
Expansion.selectedWord: proof_shape: definition. Consumers: selected_return_word, ExteriorSum.exterior_return_expansion, Expansion.product_expansion, chain_expansion, Expansion.selectedWord_cons_present, GenericReturn.selected_permuted, selected_finRange, return_expansion, Expansion.selectedWord_cons_absent, ExteriorSum.selected_basis, ExteriorSum.plus_expansion.
Expansion.selectedWord_cons_absent: proof_shape: bind-only. Consumers: Expansion.product_expansion.
Expansion.selectedWord_cons_present: proof_shape: bind-only. Consumers: Expansion.product_expansion.
ExteriorCoefficients.basis_eq_sorted_product: proof_shape: bind-only. Consumers: ExteriorSum.exterior_return_expansion, ExteriorCoefficients.word_eq_basis, ExteriorSum.selected_basis.
ExteriorCoefficients.repeated_word_zero: proof_shape: bind-only. Consumers: ExteriorCoefficients.word_coefficient.
ExteriorCoefficients.word_coefficient: proof_shape: bind-only. Consumers: ComplementBridge.exterior_top_word.
ExteriorCoefficients.word_eq_basis: proof_shape: bind-only. Consumers: ExteriorCoefficients.word_coefficient.
ExteriorSum.exterior_return_expansion: proof_shape: bind-only. Consumers: ExteriorSum.signed_top_sum_zero.
ExteriorSum.plus_expansion: proof_shape: bind-only. Consumers: ExteriorSum.signed_top_sum_zero.
ExteriorSum.selected_basis: proof_shape: bind-only. Consumers: ExteriorSum.plus_expansion.
ExteriorSum.signed_top_sum_zero: proof_shape: content. escape_witness: D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.perm_factor. Consumers: JenzerPermutedRotorLoop.result.
ExteriorWord.balanced_fixed: proof_shape: content. Consumers: ExteriorWord.exterior_balanced_fixed.
ExteriorWord.balanced_odd_coefficient_zero: proof_shape: content. Consumers: ExteriorSum.signed_top_sum_zero.
ExteriorWord.exterior_balanced_fixed: proof_shape: content. Consumers: ExteriorWord.balanced_odd_coefficient_zero.
ExteriorWord.involute_basis: proof_shape: bind-only. Consumers: ExteriorWord.odd_coefficient_zero.
ExteriorWord.involute_multivector: proof_shape: bind-only. Consumers: ExteriorWord.involute_basis.
ExteriorWord.minusWord: proof_shape: definition. Consumers: ExteriorSum.exterior_return_expansion, ExteriorWord.reverse_cancel, ExteriorWord.balanced_fixed, ExteriorSum.signed_top_sum_zero, ExteriorWord.balanced_odd_coefficient_zero.
ExteriorWord.odd_coefficient_zero: proof_shape: bind-only. Consumers: ExteriorWord.balanced_odd_coefficient_zero.
ExteriorWord.pair_central: proof_shape: bind-only. Consumers: ExteriorWord.perm_factor.
ExteriorWord.perm_factor: proof_shape: content. Consumers: ExteriorWord.balanced_fixed.
ExteriorWord.plusWord: proof_shape: definition. Consumers: ExteriorWord.perm_factor, ExteriorWord.reverse_cancel, ExteriorWord.balanced_fixed, ExteriorSum.signed_top_sum_zero, ExteriorWord.balanced_odd_coefficient_zero, ExteriorSum.plus_expansion.
ExteriorWord.plus_minus_cancel: proof_shape: bind-only. Consumers: ExteriorWord.reverse_cancel.
ExteriorWord.reverse_cancel: proof_shape: bind-only. Consumers: ExteriorWord.balanced_fixed.
ExteriorWord.swap_correction: proof_shape: bind-only. Consumers: ExteriorWord.perm_factor.
GenericReturn.selected_permuted: proof_shape: bind-only. Consumers: ExteriorSum.exterior_return_expansion.
Selection.concat_full_iff_complement: proof_shape: bind-only. Consumers: ComplementBridge.complementary_trace_word.
Selection.concat_nodup: proof_shape: bind-only. Consumers: Selection.concat_full_iff_complement.
Selection.concat_support: proof_shape: bind-only. Consumers: Selection.concat_full_iff_complement.
Selection.selected: proof_shape: definition. Consumers: ComplementBridge.exterior_top_word, ComplementBridge.canonical_exterior_top, Selection.concat_support, Selection.concat_full_iff_complement, Selection.selected_support, ComplementBridge.canonical_complementary_trace, Selection.selected_mem, GenericReturn.selected_permuted, Selection.concat_nodup, ComplementBridge.complementary_trace_word, ExteriorSum.selected_basis, ComplementBridge.complementary_trace_exterior, Selection.selected_id_eq_sort.
Selection.selected_id_eq_sort: proof_shape: bind-only. Consumers: ComplementBridge.canonical_exterior_top, ComplementBridge.canonical_complementary_trace, ExteriorSum.selected_basis.
Selection.selected_mem: proof_shape: bind-only. Consumers: Selection.concat_full_iff_complement, Selection.concat_nodup.
Selection.selected_nodup: proof_shape: bind-only. Consumers: GenericReturn.selected_permuted, Selection.concat_nodup.
Selection.selected_support: proof_shape: bind-only. Consumers: Selection.concat_support, Selection.selected_mem.
WordSigns.full_word: proof_shape: bind-only. Consumers: ComplementBridge.complementary_trace_word.
WordSigns.inversions: proof_shape: definition. Consumers: WordSigns.inversions_relative, WordSigns.sign_sorted, selected_return_word, return_word_inversions, WordSigns.sign_swap, GenericReturn.selected_permuted, WordSigns.sign_square, WordSigns.sign, WordSigns.sign_cons, WordSigns.inversions_sorted.
WordSigns.inversions_relative: proof_shape: bind-only. Consumers: return_word_inversions.
WordSigns.inversions_sorted: proof_shape: bind-only. Consumers: WordSigns.sign_sorted.
WordSigns.perm_product: proof_shape: bind-only. Consumers: selected_return_word, GenericReturn.selected_permuted, ExteriorCoefficients.word_eq_basis, WordSigns.full_word.
WordSigns.relativeInversions: proof_shape: definition. Consumers: WordSigns.inversions_relative, return_word_inversions, WordSigns.relative_eq_pair_count.
WordSigns.relative_eq_pair_count: proof_shape: bind-only. Consumers: return_word_inversions.
WordSigns.sign: proof_shape: definition. Consumers: ComplementBridge.exterior_top_word, ComplementBridge.canonical_exterior_top, WordSigns.sign_sorted, selected_return_word, WordSigns.sign_swap, GenericReturn.selected_permuted, ExteriorCoefficients.word_eq_basis, WordSigns.sign_cons_pair, WordSigns.perm_product, WordSigns.sign_square, ComplementBridge.complementary_trace_word, ComplementBridge.complementary_trace_exterior, WordSigns.sign_cons, ExteriorCoefficients.word_coefficient, WordSigns.full_word.
WordSigns.sign_cons: proof_shape: bind-only. Consumers: WordSigns.sign_cons_pair.
WordSigns.sign_cons_pair: proof_shape: bind-only. Consumers: WordSigns.perm_product.
WordSigns.sign_sorted: proof_shape: bind-only. Consumers: selected_return_word, GenericReturn.selected_permuted, ExteriorCoefficients.word_eq_basis, WordSigns.full_word.
WordSigns.sign_square: proof_shape: bind-only. Consumers: WordSigns.perm_product.
WordSigns.sign_swap: proof_shape: bind-only. Consumers: WordSigns.perm_product.
chain_expansion: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.result.
coefficient_complement: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.scalar_pair_split.
return_expansion: proof_shape: content. escape_witness: D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeGrade.reverse_bivector. Consumers: JenzerPermutedRotorLoop.result.
return_word_inversions: proof_shape: bind-only. Consumers: selected_return_word, GenericReturn.selected_permuted.
selected_finRange: proof_shape: bind-only. Consumers: chain_expansion.
selected_return_word: proof_shape: bind-only. Consumers: return_expansion.
subsetProduct_square: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.scalar_subset_square.
The source uses the native grade-zero coefficient and homogeneous bivectors.
The exterior equivalence reads grades and never transports multiplication.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Data.Finset.BooleanAlgebra
import D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra

open D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord

variable {A : Type*} [Ring A] {ι : Type*}

private def plusWord (x : ι → A) (l : List ι) : A := (l.map (fun i => 1 + x i)).prod

private def minusWord (x : ι → A) (l : List ι) : A := (l.map (fun i => 1 - x i)).prod

private lemma pair_central (a b z : A) (ha : a * z = -(z * a))
    (hb : b * z = -(z * b)) : Commute (a * b) z := by
  change (a * b) * z = z * (a * b)
  calc
    (a * b) * z = a * (b * z) := mul_assoc _ _ _
    _ = a * -(z * b) := by rw [hb]
    _ = -(a * z) * b := by simp [mul_assoc]
    _ = z * (a * b) := by rw [ha]; simp [mul_assoc]

private lemma swap_correction (a b : A) (ha : a * a = 0) (hb : b * b = 0)
    (hab : a * b = -(b * a)) :
    (1 + a) * (1 + b) = (1 + 2 * (a * b)) * ((1 + b) * (1 + a)) := by
  have hba : b * a = -(a * b) := by rw [hab]; simp
  have habb : a * (b * b) = 0 := by exact mul_eq_zero_of_right a hb
  have haba : a * (b * a) = 0 := by rw [hba, mul_neg, ← mul_assoc, ha, zero_mul, neg_zero]
  have habba : a * (b * (b * a)) = 0 := by rw [← mul_assoc b b a, hb, zero_mul, mul_zero]
  have haab : a * (a * b) = 0 := by rw [← mul_assoc, ha, zero_mul]
  have habab : a * (b * (a * b)) = 0 := by rw [← mul_assoc b a b, ← mul_assoc a (b*a) b, haba, zero_mul]
  noncomm_ring [hba, ha, hb, habb, haba, habba, haab, habab]

private lemma plus_minus_cancel (a : A) (ha : a * a = 0) : (1 + a) * (1 - a) = 1 := by
  noncomm_ring [ha]

private lemma reverse_cancel (x : ι → A) (hsq : ∀ i, x i * x i = 0) (l : List ι) :
    plusWord x l * minusWord x l.reverse = 1 := by
  induction l with
  | nil => simp [plusWord, minusWord]
  | cons a l ih =>
    simp only [plusWord, minusWord, List.map_cons, List.prod_cons,
      List.reverse_cons, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, List.map_nil, List.prod_nil, mul_one] at *
    calc
      (1 + x a) * (l.map (fun i => 1 + x i)).prod *
          ((l.reverse.map (fun i => 1 - x i)).prod * (1 - x a)) =
          (1 + x a) * ((l.map (fun i => 1 + x i)).prod *
            (l.reverse.map (fun i => 1 - x i)).prod) * (1 - x a) := by simp [mul_assoc]
      _ = 1 := by rw [ih, mul_one, plus_minus_cancel _ (hsq a)]

/-- A permutation changes an exterior word only by an even central factor. -/
private lemma perm_factor (x : ι → A) (hsq : ∀ i, x i * x i = 0)
    (hanti : ∀ i j, x i * x j = -(x j * x i))
    (f : A →+* A) (hf : ∀ i, f (x i) = -x i)
    {l m : List ι} (h : l.Perm m) :
    ∃ z : A, f z = z ∧ (∀ i, Commute z (x i)) ∧
      plusWord x l = z * plusWord x m := by
  induction h with
  | nil => exact ⟨1, map_one _, fun _ => Commute.one_left _, by simp [plusWord]⟩
  | @cons a l m h ih =>
    obtain ⟨z, hz, hc, he⟩ := ih
    refine ⟨z, hz, hc, ?_⟩
    simp only [plusWord, List.map_cons, List.prod_cons] at he ⊢
    rw [he]
    have hcz : Commute z (1 + x a) := (Commute.one_right z).add_right (hc a)
    rw [← mul_assoc, ← hcz.eq, mul_assoc]
  | swap a b l =>
    refine ⟨1 + 2 * (x b * x a), ?_, ?_, ?_⟩
    · simp only [show (2 : A) = 1 + 1 from (one_add_one_eq_two).symm, map_add, map_one, map_mul, hf, neg_mul_neg]
    · intro i
      exact (Commute.one_left _).add_left
        ((Commute.ofNat_left _ _).mul_left (pair_central _ _ _ (hanti b i) (hanti a i)))
    · simp only [plusWord, List.map_cons, List.prod_cons]
      rw [← mul_assoc, swap_correction _ _ (hsq b) (hsq a) (hanti b a)]
      simp [mul_assoc]
  | @trans l m n h₁ h₂ ih₁ ih₂ =>
    obtain ⟨z, hz, hcz, hez⟩ := ih₁
    obtain ⟨w, hw, hcw, hew⟩ := ih₂
    refine ⟨z * w, by simp [hz, hw], fun i => (hcz i).mul_left (hcw i), ?_⟩
    rw [hez, hew, mul_assoc]

private lemma balanced_fixed (x : ι → A) (hsq : ∀ i, x i * x i = 0)
    (hanti : ∀ i j, x i * x j = -(x j * x i))
    (f : A →+* A) (hf : ∀ i, f (x i) = -x i)
    {l m : List ι} (h : l.Perm m) :
    f (plusWord x l * minusWord x m.reverse) =
      plusWord x l * minusWord x m.reverse := by
  obtain ⟨z, hz, hc, he⟩ := perm_factor x hsq hanti f hf h
  have hw : plusWord x l * minusWord x m.reverse = z := by
    rw [he, mul_assoc, reverse_cancel x hsq m, mul_one]
  rw [hw, hz]

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private lemma exterior_balanced_fixed {ι : Type*} (x : ι → V) {l m : List ι} (h : l.Perm m) :
    CliffordAlgebra.involute
      (plusWord (fun i => ExteriorAlgebra.ι ℝ (x i)) l *
        minusWord (fun i => ExteriorAlgebra.ι ℝ (x i)) m.reverse) =
      plusWord (fun i => ExteriorAlgebra.ι ℝ (x i)) l *
        minusWord (fun i => ExteriorAlgebra.ι ℝ (x i)) m.reverse := by
  apply balanced_fixed (fun i => ExteriorAlgebra.ι ℝ (x i))
    (fun i => ExteriorAlgebra.ι_sq_zero (x i))
    (fun i j => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (x i) (x j)))
    CliffordAlgebra.involute.toRingHom (fun i => CliffordAlgebra.involute_ι _) h

private lemma involute_multivector (n : ℕ) (v : Fin n → V) :
    CliffordAlgebra.involute (ExteriorAlgebra.ιMulti ℝ n v) =
      (-1 : ℝ)^n • ExteriorAlgebra.ιMulti ℝ n v := by
  simpa only [ExteriorAlgebra.ιMulti_apply, List.map_ofFn, List.length_ofFn, Function.comp_def, ExteriorAlgebra.ι] using
    (CliffordAlgebra.involute_prod_map_ι (Q := (0 : QuadraticForm ℝ V)) (List.ofFn v))

private lemma involute_basis {I : Type*} [LinearOrder I] (b : Module.Basis I ℝ V) (S : Finset I) :
    CliffordAlgebra.involute (b.ExteriorAlgebra S) =
      (-1 : ℝ)^S.card • b.ExteriorAlgebra S := by
  simp only [ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family]
  exact involute_multivector _ _

private lemma odd_coefficient_zero {I : Type*} [LinearOrder I] (b : Module.Basis I ℝ V)
    (S : Finset I) (ho : Odd S.card) (z : ExteriorAlgebra ℝ V)
    (hz : CliffordAlgebra.involute z = z) : b.ExteriorAlgebra.repr z S = 0 := by
  have he : (b.ExteriorAlgebra.coord S).comp CliffordAlgebra.involute.toLinearMap =
      (-1 : ℝ)^S.card • b.ExteriorAlgebra.coord S := by
    apply b.ExteriorAlgebra.ext
    intro T
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, involute_basis,
      map_smul, LinearMap.smul_apply, Module.Basis.coord_apply]
    by_cases h : S = T
    · subst T; simp
    · simp [h, Ne.symm h]
  have hv := LinearMap.congr_fun he z
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, hz, ho.neg_one_pow, neg_one_smul, LinearMap.neg_apply] at hv
  linarith

private lemma balanced_odd_coefficient_zero {I : Type*} [LinearOrder I] (b : Module.Basis I ℝ V)
    {ι : Type*} (x : ι → V) {l m : List ι} (h : l.Perm m)
    (S : Finset I) (ho : Odd S.card) :
    b.ExteriorAlgebra.repr
      (plusWord (fun i => ExteriorAlgebra.ι ℝ (x i)) l *
        minusWord (fun i => ExteriorAlgebra.ι ℝ (x i)) m.reverse) S = 0 := by
  exact odd_coefficient_zero b S ho _ (exterior_balanced_fixed x h)

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion
open scoped BigOperators
variable {A : Type*} [Ring A] [Algebra ℝ A] {ι : Type*} [DecidableEq ι]

private def coeff (c s : ι → ℝ) (L S : Finset ι) : ℝ :=
  (∏ i ∈ S, s i) * ∏ i ∈ L \ S, c i

private def selectedWord (B : ι → A) (l : List ι) (S : Finset ι) : A :=
  ((l.filter (fun i => i ∈ S)).map B).prod

private lemma coeff_insert_absent (c s : ι → ℝ) (L S : Finset ι) (i : ι)
    (hi : i ∉ L) (hS : S ⊆ L) :
    coeff c s (insert i L) S = c i * coeff c s L S := by
  have hiS : i ∉ S := fun h => hi (hS h)
  have he : insert i L \ S = insert i (L \ S) := by
    exact Finset.insert_sdiff_of_notMem L hiS
  rw [coeff, coeff, he, Finset.prod_insert (by simp [hi])]
  ring

private lemma coeff_insert_present (c s : ι → ℝ) (L S : Finset ι) (i : ι)
    (hi : i ∉ L) (hS : S ⊆ L) :
    coeff c s (insert i L) (insert i S) = s i * coeff c s L S := by
  have hiS : i ∉ S := fun h => hi (hS h)
  have he : insert i L \ insert i S = L \ S := by
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hi]
  rw [coeff, coeff, Finset.prod_insert hiS, he]
  ring

private lemma selectedWord_cons_absent (B : ι → A) (l : List ι) (S : Finset ι)
    (i : ι) (hi : i ∉ S) : selectedWord B (i::l) S = selectedWord B l S := by
  simp [selectedWord, hi]

private lemma selectedWord_cons_present (B : ι → A) (l : List ι) (S : Finset ι)
    (i : ι) (hi : i ∉ l) :
    selectedWord B (i::l) (insert i S) = B i * selectedWord B l S := by
  simp only [selectedWord, List.filter_cons, Finset.mem_insert_self, decide_true, ↓reduceIte,
    List.map_cons, List.prod_cons]
  have hf : l.filter (fun j => j ∈ insert i S) = l.filter (fun j => j ∈ S) := by
    apply List.filter_congr
    intro j hj
    have hjn : j ≠ i := by exact ne_of_mem_of_not_mem hj hi
    simp [hjn]
  rw [hf]

private lemma product_expansion (B : ι → A) (c s : ι → ℝ) (l : List ι) (hn : l.Nodup) :
    (l.map (fun i => algebraMap ℝ A (c i) + s i • B i)).prod =
      ∑ S ∈ l.toFinset.powerset, coeff c s l.toFinset S • selectedWord B l S := by
  induction l with
  | nil => simp [coeff, selectedWord]
  | cons i l ih =>
    have hn' := List.nodup_cons.mp hn
    have hi : i ∉ l.toFinset := by simpa using hn'.1
    rw [List.map_cons, List.prod_cons, ih hn'.2, List.toFinset_cons,
      Finset.sum_powerset_insert hi]
    rw [add_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro S hS
      have hSL := Finset.mem_powerset.mp hS
      rw [coeff_insert_absent c s _ _ i hi hSL,
        selectedWord_cons_absent B l S i (fun h => hi (hSL h)), mul_smul]
      simp only [Algebra.smul_def, map_mul, mul_assoc]
    · apply Finset.sum_congr rfl
      intro S hS
      have hSL := Finset.mem_powerset.mp hS
      rw [coeff_insert_present c s _ _ i hi hSL,
        selectedWord_cons_present B l S i hn'.1]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm]

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion



namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns
variable {ι : Type*} [LinearOrder ι]

private def inversions : List ι → ℕ
  | [] => 0
  | i::l => (l.filter (fun j => j < i)).length + inversions l

private def sign (l : List ι) : ℝ := (-1 : ℝ)^inversions l

private lemma sign_square (l : List ι) : sign l * sign l = 1 := by
  unfold sign
  rw [← mul_pow]
  norm_num

private lemma sign_cons (i : ι) (l : List ι) :
    sign (i::l) = (-1 : ℝ)^(l.filter (fun j => j < i)).length * sign l := by
  simp only [sign, inversions, pow_add]

private lemma sign_swap (a b : ι) (l : List ι) (hab : a ≠ b) :
    sign (b::a::l) = -sign (a::b::l) := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hba : ¬b < a := not_lt_of_ge (le_of_lt h)
    simp [sign, inversions, h, hba, pow_add, pow_succ]
    ring
  · have hba : ¬a < b := not_lt_of_ge (le_of_lt h)
    simp [sign, inversions, h, hba, pow_add, pow_succ]
    ring

private lemma inversions_sorted (l : List ι) (h : l.SortedLT) : inversions l = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hp := List.pairwise_cons.mp h.pairwise
    have hf : l.filter (fun j => j < i) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro j hj
      simpa using (not_lt_of_ge (le_of_lt (hp.1 j hj)))
    rw [inversions, hf, List.length_nil, zero_add]
    exact ih hp.2.sortedLT

private lemma sign_sorted (l : List ι) (h : l.SortedLT) : sign l = 1 := by
  rw [sign, inversions_sorted l h, pow_zero]

private lemma sign_cons_pair {l m : List ι} (h : l.Perm m) (a : ι) :
    sign (a::l) * sign (a::m) = sign l * sign m := by
  have hc := (h.filter (fun i => decide (i < a))).length_eq
  rw [sign_cons, sign_cons, hc]
  have hs : (-1 : ℝ)^(m.filter (fun i => i<a)).length *
      (-1 : ℝ)^(m.filter (fun i => i<a)).length = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1 : ℝ)^(m.filter (fun i => i<a)).length *
        (-1 : ℝ)^(m.filter (fun i => i<a)).length) * (sign l * sign m) := by ring
    _ = _ := by rw [hs, one_mul]

private lemma perm_product {A : Type*} [Ring A] [Algebra ℝ A]
    (B : ι → A) (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    {l m : List ι} (h : l.Perm m) : l.Nodup →
    (l.map B).prod = (sign l * sign m) • (m.map B).prod := by
  induction h with
  | nil => intro hn; simp [sign, inversions]
  | @cons a l m h ih =>
    intro hn
    have ht := (List.nodup_cons.mp hn).2
    simp only [List.map_cons, List.prod_cons]
    rw [ih ht, mul_smul_comm, sign_cons_pair h a]
  | swap a b l =>
    intro hn
    have hab : a ≠ b := by
      intro he
      subst b
      exact (List.nodup_cons.mp hn).1 (by simp)
    have hs : sign (b::a::l) * sign (a::b::l) = -1 := by
      rw [sign_swap a b l hab, neg_mul, sign_square]
    rw [hs, neg_one_smul]
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, ← mul_assoc, hanti b a (Ne.symm hab), neg_mul]
  | @trans l m n h₁ h₂ ih₁ ih₂ =>
    intro hn
    rw [ih₁ hn, ih₂ (h₁.nodup_iff.mp hn), smul_smul]
    have hs : (sign l * sign m) * (sign m * sign n) = sign l * sign n := by
      calc
        _ = sign l * (sign m * sign m) * sign n := by ring
        _ = _ := by rw [sign_square, mul_one]
    rw [hs]

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords
open scoped BigOperators
lemma coefficient_complement {k : ℕ} (θ : Fin k → ℝ) (S : Finset (Fin k)) :
    a θ S * a θ (Finset.univ \ S) = ∏ i, (s θ i * c θ i) := by
  have he : (Finset.univ : Finset (Fin k)) \ (Finset.univ \ S) = S :=
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)
  have hs : (∏ i ∈ S, s θ i) * (∏ i ∈ Finset.univ \ S, s θ i) =
      ∏ i, s θ i := by
    exact Finset.prod_mul_prod_compl S (s θ)
  have hc : (∏ i ∈ S, c θ i) * (∏ i ∈ Finset.univ \ S, c θ i) =
      ∏ i, c θ i := by
    exact Finset.prod_mul_prod_compl S (c θ)
  unfold a
  rw [he, Finset.prod_mul_distrib]
  calc
    _ = ((∏ i ∈ S, s θ i) * ∏ i ∈ Finset.univ \ S, s θ i) *
        ((∏ i ∈ S, c θ i) * ∏ i ∈ Finset.univ \ S, c θ i) := by ring
    _ = _ := by rw [hs,hc]
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients
noncomputable section
open ExteriorAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {I : Type*} [LinearOrder I]

private lemma basis_eq_sorted_product (b : Module.Basis I ℝ V) (S : Finset I) :
    b.ExteriorAlgebra S = ((S.sort (· ≤ ·)).map (fun i => ι ℝ (b i))).prod := by
  rw [ExteriorAlgebra.basis_apply]
  change ExteriorAlgebra.ιMulti ℝ S.card (fun i => b (S.orderEmbOfFin rfl i)) = _
  rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_eq_map]
  change ((List.finRange S.card).map
    ((fun i => ι ℝ (b i)) ∘ S.orderEmbOfFin rfl)).prod = _
  rw [← List.map_map, Finset.listMap_orderEmbOfFin_finRange]


private lemma word_eq_basis (b : Module.Basis I ℝ V) (l : List I) (hn : l.Nodup) :
    (l.map (fun i => ι ℝ (b i))).prod =
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.sign l • b.ExteriorAlgebra l.toFinset := by
  have hp : l.Perm (l.toFinset.sort (· ≤ ·)) := by
    apply (List.perm_ext_iff_of_nodup hn (l.toFinset.sort_nodup _)).mpr
    intro i
    simp
  have hanti : ∀ i j : I, i ≠ j → ι ℝ (b i) * ι ℝ (b j) = -(ι ℝ (b j) * ι ℝ (b i)) := by
    intro i j hij
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b i) (b j))
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.perm_product _ hanti hp hn,
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.sign_sorted _ l.toFinset.sortedLT_sort, mul_one,
    ← basis_eq_sorted_product]

private lemma repeated_word_zero (b : Module.Basis I ℝ V) (l : List I) (hn : ¬l.Nodup) :
    (l.map (fun i => ι ℝ (b i))).prod = 0 := by
  have hi : ¬Function.Injective (fun i : Fin l.length => b (l.get i)) := by
    intro hh
    apply hn
    apply List.nodup_iff_injective_get.mpr
    intro i j hij
    exact hh (congrArg b hij)
  have he := ExteriorAlgebra.ιMulti_eq_zero_of_not_inj (R := ℝ) hi
  rw [ExteriorAlgebra.ιMulti_apply] at he
  change (List.ofFn (fun i : Fin l.length => ι ℝ (b l[(i : ℕ)]))).prod = 0 at he
  have heq : List.ofFn (fun i : Fin l.length => ι ℝ (b l[(i : ℕ)])) =
      l.map (fun i => ι ℝ (b i)) :=
    List.ofFn_getElem_eq_map l (fun i => ι ℝ (b i))
  rw [heq] at he
  exact he

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns
open scoped BigOperators
variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

private def relativeInversions (f : ι → κ) (S : Finset ι) : ℕ :=
  ∑ b ∈ S, (S.filter (fun a => a < b ∧ f b < f a)).card

private lemma inversions_relative (f : ι → κ) (l : List ι) (hn : l.Nodup)
    (hf : (l.map f).SortedLT) : inversions l = relativeInversions f l.toFinset := by
  induction l with
  | nil => simp [inversions, relativeInversions]
  | cons i l ih =>
    have hn' := List.nodup_cons.mp hn
    have hf' := List.sortedLT_cons.mp hf
    have hfi : ∀ j ∈ l, f i < f j := by
      intro j hj
      exact hf'.1 (f j) (List.mem_map.mpr ⟨j,hj,rfl⟩)
    have hi : i ∉ l.toFinset := by simpa using hn'.1
    have htail : ∀ b ∈ l.toFinset,
        ((insert i l.toFinset).filter (fun a => a < b ∧ f b < f a)).card =
        (l.toFinset.filter (fun a => a < b ∧ f b < f a)).card := by
      intro b hb
      rw [Finset.filter_insert]
      have hh := hfi b (by simpa using hb)
      simp [not_lt_of_ge hh.le]
    have hhead : (insert i l.toFinset).filter (fun a => a < i ∧ f i < f a) =
        l.toFinset.filter (fun a => a < i) := by
      ext a
      by_cases ha : a ∈ l
      · have hh := hfi a ha
        simp [ha,hh,ne_of_lt hh]
      · by_cases he : a=i <;> simp [ha,he]
    have hc : (l.filter (fun a => a < i)).length =
        (l.toFinset.filter (fun a => a < i)).card := by
      rw [← List.toFinset_card_of_nodup (hn'.2.filter _), List.toFinset_filter]
      simp
    rw [inversions, List.toFinset_cons, relativeInversions,
      Finset.sum_insert hi, hhead, hc, ih hn'.2 hf'.2]
    congr 1
    apply Finset.sum_congr rfl
    exact fun b hb => (htail b hb).symm

private lemma relative_eq_pair_count (f : ι → κ) (S : Finset ι) :
    relativeInversions f S =
      ((S ×ˢ S).filter (fun ij => ij.1 < ij.2 ∧ f ij.2 < f ij.1)).card := by
  simp only [relativeInversions, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]
  rw [Finset.sum_comm]

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords
private lemma return_word_inversions {k : ℕ} (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.inversions
      (((List.finRange k).map τ).filter (fun i => i ∈ S)) = inversionCount τ S := by
  let l := ((List.finRange k).map τ).filter (fun i => i ∈ S)
  have hn : l.Nodup := ((List.nodup_finRange k).map τ.injective).filter _
  have hs : l.toFinset = S := by
    ext i
    simp [l]
    intro hi
    exact τ.surjective i
  have hf : (l.map τ.symm).SortedLT := by
    have he : l.map τ.symm = (List.finRange k).filter (fun j => τ j ∈ S) := by
      simp [l, List.filter_map, List.map_map, Function.comp_def]
    rw [he]
    exact (List.Pairwise.filter _ (List.sortedLT_finRange k).pairwise).sortedLT
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.inversions_relative τ.symm l hn hf, hs,
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.relative_eq_pair_count]
  rfl
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion
open scoped BigOperators
private lemma coeff_neg {ι : Type*} [DecidableEq ι] (c s : ι → ℝ) (L S : Finset ι) :
    coeff c (fun i => -s i) L S = (-1 : ℝ)^S.card * coeff c s L S := by
  simp only [coeff, Finset.prod_neg]
  ring
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion



namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns
noncomputable section
open scoped BigOperators
variable {A : Type*} [Ring A] [Algebra ℝ A]

private lemma full_word {k : ℕ} (B : Fin k → A)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (l : List (Fin k)) (hn : l.Nodup) (hf : l.toFinset = Finset.univ) :
    (l.map B).prod = sign l • (((Finset.univ : Finset (Fin k)).sort (· ≤ ·)).map B).prod := by
  have hp : l.Perm ((Finset.univ : Finset (Fin k)).sort (· ≤ ·)) := by
    apply (List.perm_ext_iff_of_nodup hn (Finset.sort_nodup _ _)).mpr
    intro i
    have hi : i ∈ l.toFinset := by rw [hf]; exact Finset.mem_univ _
    simpa only [Finset.mem_sort, Finset.mem_univ, iff_true] using (List.mem_toFinset.mp hi)
  rw [perm_product B hanti hp hn, sign_sorted _ Finset.univ.sortedLT_sort, mul_one]

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {I : Type*} [LinearOrder I]
private lemma word_coefficient (b : Module.Basis I ℝ V) (l : List I) (S : Finset I) :
    b.ExteriorAlgebra.repr (l.map (fun i => ExteriorAlgebra.ι ℝ (b i))).prod S =
      if l.Nodup ∧ l.toFinset = S then D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.sign l else 0 := by
  classical
  by_cases hn : l.Nodup
  · rw [word_eq_basis b l hn, map_smul, Finsupp.smul_apply]
    by_cases he : l.toFinset = S
    · subst S
      simp [hn]
    · simp [hn,he,Ne.symm he]
  · rw [repeated_word_zero b l hn]
    simp [hn]
end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection
noncomputable section

private def selected {k : ℕ} (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) : List (Fin k) :=
  ((List.finRange k).map τ).filter (fun i => i ∈ S)

private lemma selected_nodup {k : ℕ} (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    (selected τ S).Nodup :=
  ((List.nodup_finRange k).map τ.injective).filter _

private lemma selected_support {k : ℕ} (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    (selected τ S).toFinset = S := by
  ext i
  simp only [selected, List.mem_toFinset, List.mem_filter, List.mem_map,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hi
    exact ⟨⟨τ.symm i, τ.apply_symm_apply i⟩, hi⟩

private lemma selected_mem {k : ℕ} (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) (i : Fin k) :
    i ∈ selected τ S ↔ i ∈ S := by
  rw [← List.mem_toFinset, selected_support]

private lemma concat_support {k : ℕ} (τ σ : Equiv.Perm (Fin k)) (S T : Finset (Fin k)) :
    (selected τ S ++ selected σ T).toFinset = S ∪ T := by
  rw [List.toFinset_append, selected_support, selected_support]

private lemma concat_nodup {k : ℕ} (τ σ : Equiv.Perm (Fin k)) (S T : Finset (Fin k))
    (hd : Disjoint S T) : (selected τ S ++ selected σ T).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨selected_nodup _ _, selected_nodup _ _, ?_⟩
  intro i hi hj
  exact Finset.disjoint_left.mp hd ((selected_mem τ S i).mp hi) ((selected_mem σ T i).mp hj)

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection



namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection
private lemma concat_full_iff_complement {k : ℕ} (τ σ : Equiv.Perm (Fin k))
    (S T : Finset (Fin k)) :
    ((selected τ S ++ selected σ T).Nodup ∧
      (selected τ S ++ selected σ T).toFinset = Finset.univ) ↔
      T = Finset.univ \ S := by
  constructor
  · rintro ⟨hn, hu⟩
    have hd := (List.nodup_append.mp hn).2.2
    have hu' : S ∪ T = Finset.univ := by simpa only [concat_support] using hu
    ext i
    have hi : i ∈ S ∨ i ∈ T := by
      have hm : i ∈ S ∪ T := by rw [hu']; exact Finset.mem_univ _
      exact Finset.mem_union.mp hm
    have hnot : ¬(i ∈ S ∧ i ∈ T) := by
      rintro ⟨hiS,hiT⟩
      exact hd i ((selected_mem τ S i).mpr hiS) i ((selected_mem σ T i).mpr hiT) rfl
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  · intro he
    subst T
    have hd : Disjoint S (Finset.univ \ S) := by
      exact Finset.disjoint_sdiff
    refine ⟨concat_nodup τ σ _ _ hd, ?_⟩
    rw [concat_support]
    ext i
    simp
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge
noncomputable section
variable {A : Type*} [Ring A] [Algebra ℝ A]

private lemma complementary_trace_word {k : ℕ} (B : Fin k → A)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (t : A →ₗ[ℝ] ℝ) (τ σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    t (((D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected τ S ++
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected σ (Finset.univ \ S)).map B).prod) =
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.sign (D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected τ S ++
        D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected σ (Finset.univ \ S)) *
      t ((((Finset.univ : Finset (Fin k)).sort (· ≤ ·)).map B).prod) := by
  have hh := (D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.concat_full_iff_complement τ σ S
    (Finset.univ \ S)).mpr rfl
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.full_word B hanti _ hh.1 hh.2, map_smul, smul_eq_mul]

private lemma exterior_top_word {k : ℕ}
    (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (τ σ : Equiv.Perm (Fin k)) (S T : Finset (Fin k)) :
    b.ExteriorAlgebra.repr
      (((D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected τ S ++ D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected σ T).map
        (fun i => ExteriorAlgebra.ι ℝ (b i))).prod) Finset.univ =
      if T = Finset.univ \ S then
        D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.sign (D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected τ S ++ D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected σ T)
      else 0 := by
  simp only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients.word_coefficient,
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.concat_full_iff_complement]

private lemma complementary_trace_exterior {k : ℕ} (B : Fin k → A)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (t : A →ₗ[ℝ] ℝ) (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (τ σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    t (((D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected τ S ++
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected σ (Finset.univ \ S)).map B).prod) =
      b.ExteriorAlgebra.repr
        (((D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected τ S ++
          D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected σ (Finset.univ \ S)).map
            (fun i => ExteriorAlgebra.ι ℝ (b i))).prod) Finset.univ *
        t ((((Finset.univ : Finset (Fin k)).sort (· ≤ ·)).map B).prod) := by
  rw [complementary_trace_word B hanti t, exterior_top_word, if_pos rfl]

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection
private lemma selected_id_eq_sort {k : ℕ} (S : Finset (Fin k)) :
    selected (Equiv.refl (Fin k)) S = S.sort (· ≤ ·) := by
  have hs : (selected (Equiv.refl (Fin k)) S).SortedLT := by
    simpa only [selected, Equiv.coe_refl, List.map_id] using
      (List.Pairwise.filter (fun i => decide (i ∈ S)) (List.sortedLT_finRange k).pairwise).sortedLT
  apply hs.eq_of_mem_iff S.sortedLT_sort
  intro i
  simp only [selected_mem, Finset.mem_sort]
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords
noncomputable section
variable {V : Type} [AddCommGroup V] [Module ℝ V]

private lemma selected_finRange {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (S : Finset (Fin k)) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.selectedWord B (List.finRange k) S = subsetProduct B S := by
  simpa only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.selectedWord,
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.subsetProduct,
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected, Equiv.coe_refl, List.map_id] using
    congrArg (fun l : List (Fin k) => (l.map B).prod)
      (D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected_id_eq_sort S)

lemma chain_expansion {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (θ : Fin k → ℝ) :
    chain B θ = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      a θ S • subsetProduct B S := by
  have hu : (List.finRange k).toFinset = (Finset.univ : Finset (Fin k)) := by
    exact List.toFinset_finRange k
  have h := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.product_expansion B (c θ) (s θ) (List.finRange k) (List.nodup_finRange k)
  change ((List.finRange k).map (fun i => algebraMap ℝ _ (c θ i) + s θ i • B i)).prod = _
  simpa only [hu, D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.coeff, a, selected_finRange] using h

lemma subsetProduct_square {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (hB : AnticommutingUnitFamily q k B)
    (S : Finset (Fin k)) :
    subsetProduct B S * subsetProduct B S =
      (-1 : ℝ)^(S.card*(S.card+1)/2) • (1 : CliffordAlgebra q) := by
  have hs : ∀ i, B i * B i = -1 := fun i => by simpa only [pow_two] using hB.2.1 i
  have h := D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport.anticommuting_list_square B hs hB.2.2 (S.sort (· ≤ ·)) (S.sort_nodup _)
  simpa only [subsetProduct, Finset.length_sort, Nat.choose_two_right, Nat.add_sub_cancel,
    mul_comm S.card (S.card+1)] using h

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge
noncomputable section
variable {A : Type*} [Ring A] [Algebra ℝ A]

lemma canonical_complementary_trace {k : ℕ} (B : Fin k → A)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (t : A →ₗ[ℝ] ℝ) (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (S : Finset (Fin k)) :
    t (((S.sort (· ≤ ·)).map B).prod *
      (((Finset.univ \ S).sort (· ≤ ·)).map B).prod) =
      b.ExteriorAlgebra.repr (b.ExteriorAlgebra S *
        b.ExteriorAlgebra (Finset.univ \ S)) Finset.univ *
      t ((((Finset.univ : Finset (Fin k)).sort (· ≤ ·)).map B).prod) := by
  have hh := complementary_trace_exterior B hanti t b
    (Equiv.refl (Fin k)) (Equiv.refl (Fin k)) S
  simpa only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected_id_eq_sort, List.map_append, List.prod_append,
    ← D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients.basis_eq_sorted_product] using hh

lemma canonical_exterior_top {k : ℕ}
    (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (S T : Finset (Fin k)) (hne : T ≠ Finset.univ \ S) :
    b.ExteriorAlgebra.repr (b.ExteriorAlgebra S * b.ExteriorAlgebra T) Finset.univ = 0 := by
  have hh := exterior_top_word b (Equiv.refl (Fin k)) (Equiv.refl (Fin k)) S T
  simpa only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected_id_eq_sort, List.map_append, List.prod_append,
    ← D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients.basis_eq_sorted_product, if_neg hne] using hh

lemma complement_ne_self {k : ℕ} (hk : 1 ≤ k) (S : Finset (Fin k)) :
    S ≠ Finset.univ \ S := by
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  simpa only [Finset.compl_eq_univ_sdiff] using (ne_compl_self (a := S))

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.GenericReturn
noncomputable section
open scoped BigOperators
variable {A : Type*} [Ring A] [Algebra ℝ A]

private lemma selected_permuted {k : ℕ} (B : Fin k → A)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.selectedWord B ((List.finRange k).map τ) S =
      (-1 : ℝ)^D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.inversionCount τ S •
        (((S.sort (· ≤ ·)).map B).prod) := by
  let l := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected τ S
  have hn : l.Nodup := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected_nodup τ S
  have hp : l.Perm (S.sort (· ≤ ·)) := by
    apply (List.perm_ext_iff_of_nodup hn (S.sort_nodup _)).mpr
    intro i
    simp only [l, D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected_mem, Finset.mem_sort]
  have he := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.perm_product B hanti hp hn
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.sign_sorted _ S.sortedLT_sort, mul_one] at he
  simpa only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.selectedWord, D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.WordSigns.sign,
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.return_word_inversions, l, D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected] using he

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.GenericReturn

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords
noncomputable section
variable {V : Type} [AddCommGroup V] [Module ℝ V]

private lemma selected_return_word {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (hB : AnticommutingUnitFamily q k B)
    (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.selectedWord B ((List.finRange k).map τ) S =
      (-1 : ℝ)^inversionCount τ S • subsetProduct B S := by
  simpa only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.subsetProduct] using
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.GenericReturn.selected_permuted B hB.2.2 τ S

lemma return_expansion {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (hB : AnticommutingUnitFamily q k B)
    (θ : Fin k → ℝ) (τ : Equiv.Perm (Fin k)) :
    returnProduct B θ τ =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (((-1 : ℝ)^S.card * (-1 : ℝ)^inversionCount τ S) * a θ S) • subsetProduct B S := by
  let l := (List.finRange k).map τ
  have hn : l.Nodup := (List.nodup_finRange k).map τ.injective
  have hu : l.toFinset = Finset.univ := by
    simpa only [l, List.toFinset_finRange] using (List.toFinset_eq_of_perm _ _ τ.map_finRange_perm)
  have hr : returnProduct B θ τ =
      (l.map (fun i => algebraMap ℝ _ (c θ i) + (-s θ i) • B i)).prod := by
    simp only [returnProduct, l, List.map_map, Function.comp_def,
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeGrade.reverse_rotor q B hB.1 θ, neg_smul, sub_eq_add_neg]
  rw [hr, D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.product_expansion B (c θ) (fun i => -s θ i) l hn, hu]
  apply Finset.sum_congr rfl
  intro S hS
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.coeff_neg, selected_return_word B hB τ,
    smul_smul]
  unfold D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.coeff a
  congr 1
  ring

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorSum
noncomputable section
open scoped BigOperators

private lemma selected_basis {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (S : Finset (Fin k)) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.selectedWord (fun i => ExteriorAlgebra.ι ℝ (b i)) (List.finRange k) S =
      b.ExteriorAlgebra S := by
  have hh := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected_id_eq_sort S
  simp only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Selection.selected, Equiv.coe_refl, List.map_id] at hh
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.selectedWord, hh, ← D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients.basis_eq_sorted_product]

private lemma plus_expansion {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ)) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.plusWord (fun i => ExteriorAlgebra.ι ℝ (b i)) (List.finRange k) =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, b.ExteriorAlgebra S := by
  have hu : (List.finRange k).toFinset = (Finset.univ : Finset (Fin k)) := by
    exact List.toFinset_finRange k
  have hh := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.product_expansion (fun i => ExteriorAlgebra.ι ℝ (b i))
    (fun _ => 1) (fun _ => 1) (List.finRange k) (List.nodup_finRange k)
  simpa only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.plusWord, map_one, one_smul, hu,
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.coeff, Finset.prod_const_one, one_mul, selected_basis] using hh

private lemma exterior_return_expansion {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (τ : Equiv.Perm (Fin k)) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.minusWord (fun i => ExteriorAlgebra.ι ℝ (b i)) ((List.finRange k).map τ) =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        ((-1 : ℝ)^S.card * (-1 : ℝ)^D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.inversionCount τ S) • b.ExteriorAlgebra S := by
  let B := fun i => ExteriorAlgebra.ι ℝ (b i)
  have hu : ((List.finRange k).map τ).toFinset = (Finset.univ : Finset (Fin k)) := by
    simpa only [List.toFinset_finRange] using (List.toFinset_eq_of_perm _ _ τ.map_finRange_perm)
  have ha : ∀ i j, i ≠ j → B i * B j = -(B j * B i) := by
    intro i j hij
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b i) (b j))
  have hh := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.product_expansion B (fun _ => 1) (fun _ => -1)
    ((List.finRange k).map τ) ((List.nodup_finRange k).map τ.injective)
  simp only [hu, D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.Expansion.coeff, Finset.prod_const, one_pow, mul_one,
    map_one, neg_one_smul, ← sub_eq_add_neg] at hh
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.minusWord]
  rw [hh]
  apply Finset.sum_congr rfl
  intro S hS
  rw [D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.GenericReturn.selected_permuted B ha τ S, smul_smul,
    ← D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorCoefficients.basis_eq_sorted_product]

lemma signed_top_sum_zero {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (τ : Equiv.Perm (Fin k)) (ho : Odd k) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
        ((-1 : ℝ)^T.card * (-1 : ℝ)^D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.inversionCount τ T) *
          b.ExteriorAlgebra.repr (b.ExteriorAlgebra S * b.ExteriorAlgebra T) Finset.univ = 0 := by
  have hp : (List.finRange k).Perm (((List.finRange k).map τ).reverse) :=
    τ.map_finRange_perm.symm.trans (List.reverse_perm _).symm
  have hh := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.balanced_odd_coefficient_zero b (fun i => b i) hp
    Finset.univ (by simpa using ho)
  simp only [List.reverse_reverse] at hh
  change b.ExteriorAlgebra.coord Finset.univ
    (D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.plusWord (fun i => ExteriorAlgebra.ι ℝ (b i)) (List.finRange k) *
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorWord.minusWord (fun i => ExteriorAlgebra.ι ℝ (b i)) ((List.finRange k).map τ)) = 0 at hh
  rw [plus_expansion b, exterior_return_expansion b τ] at hh
  simp only [Finset.sum_mul, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    smul_eq_mul, Module.Basis.coord_apply] at hh
  rw [Finset.sum_comm] at hh
  exact hh

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorSum
