/- GID: D5/S3/Quantum/Algebra/GenericLieLengthFiltration
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/GenericLieLengthFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Jia-Capel generic Lie length conjecture formalization. -/
/- admission_basis: escape-witness
   Direct frozen dependencies: none; every D5 proof dependency is in this delivery.
   Module witnesses: word_bracket_mem, card_words_le.
   Heap depth uses Nat.size; coordinate and matrix operations use their Mathlib owners.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16180
   suSet: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,combine,combine_injective,combine_surjective,compactPair,compactPair_span_top,complexification,coordinateLinearMap,extendedPair,extendedPair_span_top,iGen_su,lieLength,lieLength_attained,lieLength_le_of_span,lower_lieLength_of_saturation,lower_log_of_saturation,real_full_span,result,rightSpan_complex_to_real,rightSpan_real_le_su,saturation_count,suCoordinateMap,suCoordinateMap_measurableEmbedding,suLie,suLieAlgebra,suLieRing,suPairMeasure,su_bracket_mem,su_finrank,word_su_mem.
   layer: proof_shape: bind-only; escape_witness: none; consumers: cumulative_eq_rightSpan,layer_eq_exactWordSpan,layer_one,lieLength,lieLength_attained,lieLength_le_of_span.
   lieLength: proof_shape: bind-only; escape_witness: none; consumers: claim,lieLength_attained,lower_lieLength_of_saturation,result.
   suCoordinateMap: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,suPairMeasure.
   suPairMeasure: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,claim,result.
   layer_one: proof_shape: bind-only; escape_witness: none; consumers: layer_eq_exactWordSpan.
   RightWord: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness,card_words_le,combination_mem,cumulative_eq_rightSpan,determinant_ne_zero_implies_span_top,rightWordEval,eval_boundedPolynomial,eval_spanningPolynomial,eval_wordPolynomial,exactWordSpan,generator_bracket_mem,layer_eq_exactWordSpan,rightWordLength,length_pos,mem_words,reindexWord,reindex_eval,reindex_length,rightSpan,rightSpan_bracket_mem,rightSpan_complex_to_real,rightSpan_eq_range,rightSpan_finrank_le,rightSpan_le_scaled,rightSpan_map,rightSpan_mono,rightSpan_real_le_su,rightSpan_reindex_le,spanningPolynomial,wordPolynomial,word_bracket_mem,word_map,word_mem,word_scaled,word_su_mem,words.
   rightWordLength: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness,combination_mem,cumulative_eq_rightSpan,determinant_ne_zero_implies_span_top,eval_boundedPolynomial,eval_spanningPolynomial,exactWordSpan,generator_bracket_mem,layer_eq_exactWordSpan,length_pos,mem_words,reindex_length,rightSpan,rightSpan_bracket_mem,rightSpan_complex_to_real,rightSpan_eq_range,rightSpan_finrank_le,rightSpan_le_scaled,rightSpan_map,rightSpan_mono,rightSpan_real_le_su,rightSpan_reindex_le,spanningPolynomial,word_bracket_mem,word_mem,word_scaled.
   rightWordEval: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness,combination_mem,cumulative_eq_rightSpan,determinant_ne_zero_implies_span_top,eval_boundedPolynomial,eval_spanningPolynomial,eval_wordPolynomial,exactWordSpan,generator_bracket_mem,layer_eq_exactWordSpan,reindex_eval,rightSpan,rightSpan_bracket_mem,rightSpan_complex_to_real,rightSpan_eq_range,rightSpan_finrank_le,rightSpan_le_scaled,rightSpan_map,rightSpan_mono,rightSpan_real_le_su,rightSpan_reindex_le,word_bracket_mem,word_map,word_mem,word_scaled,word_su_mem.
   length_pos: proof_shape: bind-only; escape_witness: none; consumers: cumulative_eq_rightSpan,layer_eq_exactWordSpan,mem_words.
   rightSpan: proof_shape: bind-only; escape_witness: none; consumers: ad_pow_mem,adjusted_units_mem,ae_rightSpan_eq,ae_span_top_of_witness,anchor_units_mem,anchored_units_mem,anchored_units_uniform,combination_mem,compactPair_span_top,cumulative_eq_rightSpan,determinant_ne_zero_implies_span_top,extendedPair_span_top,generator_bracket_mem,lieLength_attained,lieLength_le_of_span,lower_lieLength_of_saturation,lower_log_of_saturation,polynomial_ad_mem,real_full_span,result,rightSpan_bracket_mem,rightSpan_complex_to_real,rightSpan_eq_range,rightSpan_finrank_le,rightSpan_le_scaled,rightSpan_map,rightSpan_mono,rightSpan_reindex_le,saturation_count,selector_mem_eight,traceless_full_span,transfer_mem_eight,word_bracket_mem.
   word_mem: proof_shape: bind-only; escape_witness: none; consumers: B_mem,combination_mem,cumulative_eq_rightSpan,rightSpan_le_scaled,rightSpan_reindex_le,word_bracket_mem.
   rightSpan_mono: proof_shape: bind-only; escape_witness: none; consumers: adjusted_units_mem,anchored_units_mem,anchored_units_uniform,polynomial_ad_mem,rightSpan_bracket_mem.
   generator_bracket_mem: proof_shape: bind-only; escape_witness: none; consumers: ad_pow_mem,word_bracket_mem.
   word_bracket_mem: proof_shape: content; escape_witness: word_bracket_mem; consumers: rightSpan_bracket_mem.
   rightSpan_bracket_mem: proof_shape: content; escape_witness: word_bracket_mem; consumers: adjusted_units_mem,anchored_units_mem.
   ad_pow_mem: proof_shape: bind-only; escape_witness: none; consumers: polynomial_ad_mem.
   polynomial_ad_mem: proof_shape: bind-only; escape_witness: none; consumers: selector_mem_eight.
   skewProjection_apply: proof_shape: bind-only; escape_witness: none; consumers: reconstruction,skewProject_complex_smul,skewProject_su.
   skewProject_of_skew: proof_shape: bind-only; escape_witness: none; consumers: combine_injective,real_span_of_complex_span.
   skewProject_complex_smul: proof_shape: bind-only; escape_witness: none; consumers: combine_injective,real_span_of_complex_span.
   real_span_of_complex_span: proof_shape: bind-only; escape_witness: none; consumers: rightSpan_complex_to_real.
   su_bracket_mem: proof_shape: bind-only; escape_witness: none; consumers: suLie,word_su_mem.
   suLie: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,compactPair_span_top,suLieAlgebra,suLieRing.
   word_su_mem: proof_shape: bind-only; escape_witness: none; consumers: rightSpan_complex_to_real,rightSpan_real_le_su.
   rightSpan_real_le_su: proof_shape: bind-only; escape_witness: none; consumers: real_full_span.
   rightSpan_complex_to_real: proof_shape: bind-only; escape_witness: none; consumers: real_full_span.
   sl_finrank: proof_shape: bind-only; escape_witness: none; consumers: su_finrank.
   skewProject_su: proof_shape: bind-only; escape_witness: none; consumers: combine_surjective.
   reconstruction: proof_shape: bind-only; escape_witness: none; consumers: combine_surjective.
   combine: proof_shape: bind-only; escape_witness: none; consumers: combine_injective,combine_surjective,complexification.
   combine_injective: proof_shape: bind-only; escape_witness: none; consumers: complexification.
   combine_surjective: proof_shape: bind-only; escape_witness: none; consumers: complexification.
   complexification: proof_shape: bind-only; escape_witness: none; consumers: su_finrank.
   su_finrank: proof_shape: bind-only; escape_witness: none; consumers: saturation_count.
   exactWordSpan: proof_shape: bind-only; escape_witness: none; consumers: cumulative_eq_rightSpan,layer_eq_exactWordSpan.
   layer_eq_exactWordSpan: proof_shape: content; escape_witness: layer_eq_exactWordSpan; consumers: cumulative_eq_rightSpan.
   cumulative_eq_rightSpan: proof_shape: content; escape_witness: layer_eq_exactWordSpan; consumers: lieLength_attained,lieLength_le_of_span.
   lieLength_le_of_span: proof_shape: content; escape_witness: layer_eq_exactWordSpan; consumers: result.
   reindexWord: proof_shape: bind-only; escape_witness: none; consumers: reindex_eval,reindex_length,rightSpan_reindex_le.
   reindex_length: proof_shape: bind-only; escape_witness: none; consumers: rightSpan_reindex_le.
   reindex_eval: proof_shape: bind-only; escape_witness: none; consumers: rightSpan_reindex_le.
   rightSpan_reindex_le: proof_shape: bind-only; escape_witness: none; consumers: extendedPair_span_top.
   words: proof_shape: bind-only; escape_witness: none; consumers: card_words_le,mem_words,rightSpan_finrank_le.
   mem_words: proof_shape: content; escape_witness: mem_words; consumers: rightSpan_finrank_le.
   wordBudget: proof_shape: bind-only; escape_witness: none; consumers: budget_eq_sum,budget_pow_bound,card_words_le,lower_log_of_saturation,rightSpan_finrank_le,saturation_count.
   card_words_le: proof_shape: content; escape_witness: card_words_le; consumers: rightSpan_finrank_le.
   budget_eq_sum: proof_shape: bind-only; escape_witness: none; consumers: lower_log_of_saturation,saturation_count.
   rightSpan_finrank_le: proof_shape: content; escape_witness: card_words_le; consumers: saturation_count.
   saturation_count: proof_shape: content; escape_witness: card_words_le; consumers: lower_log_of_saturation.
   budget_pow_bound: proof_shape: content; escape_witness: budget_pow_bound; consumers: lower_log_of_saturation.
   lower_log_of_saturation: proof_shape: content; escape_witness: budget_pow_bound; consumers: lower_lieLength_of_saturation.
   lieLength_attained: proof_shape: content; escape_witness: layer_eq_exactWordSpan; consumers: lower_lieLength_of_saturation.
   lower_lieLength_of_saturation: proof_shape: content; escape_witness: budget_pow_bound; consumers: result.
   upper_log: proof_shape: bind-only; escape_witness: none; consumers: result.
-/


import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Base



namespace D5.S3.Quantum.Algebra.GenericLieLengthFiltration

noncomputable section


open Matrix MeasureTheory


def suSet (n : ℕ) : Submodule ℝ ((Matrix (Fin n) (Fin n) ℂ)) where
  carrier := {X | Xᴴ = -X ∧ Matrix.trace X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    constructor
    · simp [hX.1, hY.1, add_comm]
    · simp [hX.2, hY.2]
  smul_mem' := by
    intro r X hX
    constructor
    · simp [Matrix.conjTranspose_smul, hX.1]
    · simp [hX.2]

def layer {n : ℕ} (S : Finset ((Matrix (Fin n) (Fin n) ℂ))) : ℕ → Submodule ℝ ((Matrix (Fin n) (Fin n) ℂ))
  | 0 => ⊥
  | 1 => Submodule.span ℝ (S : Set ((Matrix (Fin n) (Fin n) ℂ)))
  | k + 2 => Submodule.span ℝ {Z | ∃ X ∈ S, ∃ Y ∈ layer S (k + 1), Z = ⁅X, Y⁆}

def lieLength (n : ℕ) (S : Finset ((Matrix (Fin n) (Fin n) ℂ))) : ℕ :=
  sInf {l | 1 ≤ l ∧ (⨆ k ∈ Finset.Icc 1 l, layer S k) = suSet n}


noncomputable def suCoordinateMap (g n : ℕ)
    (x : Fin g → Fin (Module.finrank ℝ (suSet n)) → ℝ) : Fin g → (Matrix (Fin n) (Fin n) ℂ) :=
  fun j => (((Module.finBasis ℝ (suSet n))).equivFun.symm (x j)).val

noncomputable def suPairMeasure (g n : ℕ) : Measure (Fin g → Fin n → Fin n → ℂ) :=
  Measure.map (show (Fin g → Fin (Module.finrank ℝ (suSet n)) → ℝ) →
    (Fin g → Fin n → Fin n → ℂ) from suCoordinateMap g n) volume

private theorem layer_one {n : ℕ} (S : Finset ((Matrix (Fin n) (Fin n) ℂ))) :
    layer S 1 = Submodule.span ℝ (S : Set ((Matrix (Fin n) (Fin n) ℂ))) := rfl


inductive RightWord (I : Type*)
  | single : I → RightWord I
  | cons : I → RightWord I → RightWord I
  deriving DecidableEq

section
set_option quotPrecheck false in
set_option hygiene false in
local notation "w.length" => rightWordLength w

def rightWordLength {I : Type*} : RightWord I → ℕ
  | .single _ => 1
  | .cons _ w => w.length + 1
end

section
set_option quotPrecheck false in
set_option hygiene false in
local notation "w.eval" => fun s => rightWordEval s w

def rightWordEval {I M : Type*} [LieRing M]
    (S : I → M) : RightWord I → M
  | .single i => S i
  | .cons i w => ⁅S i, w.eval S⁆
end

namespace RightWord

export D5.S3.Quantum.Algebra.GenericLieLengthFiltration (rightWordLength rightWordEval)

@[simp] private theorem length_pos {I : Type*} (w : RightWord I) : 0 < w.rightWordLength := by
  cases w <;> simp [rightWordLength]


end RightWord

variable {I K M : Type*} [CommRing K] [LieRing M] [LieAlgebra K M]

def rightSpan (S : I → M) (L : ℕ) : Submodule K M :=
  Submodule.span K {x | ∃ w : RightWord I, w.rightWordLength ≤ L ∧ w.rightWordEval S = x}

theorem word_mem (S : I → M) (w : RightWord I) (L : ℕ) (h : w.rightWordLength ≤ L) :
    w.rightWordEval S ∈ rightSpan (K := K) S L :=
  Submodule.subset_span ⟨w, h, rfl⟩

theorem rightSpan_mono (S : I → M) {a b : ℕ} (h : a ≤ b) :
    rightSpan (K := K) S a ≤ rightSpan (K := K) S b := by
  unfold rightSpan
  apply Submodule.span_mono
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans h, rfl⟩

private theorem generator_bracket_mem (S : I → M) (i : I) {L : ℕ} {x : M}
    (hx : x ∈ rightSpan (K := K) S L) : ⁅S i, x⁆ ∈ rightSpan (K := K) S (L + 1) := by
  have h : rightSpan (K := K) S L ≤
      (rightSpan (K := K) S (L + 1)).comap (LieAlgebra.ad K M (S i)) := by
    apply Submodule.span_le.mpr
    rintro y ⟨w, hw, rfl⟩
    exact Submodule.subset_span ⟨RightWord.cons i w,
      by simpa only [rightWordLength] using Nat.add_le_add_right hw 1, rfl⟩
  exact h hx

theorem word_bracket_mem (S : I → M) (u v : RightWord I) :
    ⁅u.rightWordEval S, v.rightWordEval S⁆ ∈ rightSpan (K := K) S (u.rightWordLength + v.rightWordLength) := by
  induction u generalizing v with
  | single i =>
    exact word_mem S (.cons i v) _ (by simp [rightWordLength, Nat.add_comm])
  | cons i u ih =>
    change ⁅⁅S i, u.rightWordEval S⁆, v.rightWordEval S⁆ ∈ rightSpan (K := K) S ((u.rightWordLength + 1) + v.rightWordLength)
    rw [lie_lie]
    apply (rightSpan (K := K) S ((u.rightWordLength + 1) + v.rightWordLength)).sub_mem
    · have h := generator_bracket_mem S i (ih v)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · have h := ih (.cons i v)
      simpa [rightWordEval, rightWordLength, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

theorem rightSpan_bracket_mem (S : I → M) {r s : ℕ} {x y : M}
    (hx : x ∈ rightSpan (K := K) S r) (hy : y ∈ rightSpan (K := K) S s) :
    ⁅x, y⁆ ∈ rightSpan (K := K) S (r + s) := by
  change x ∈ Submodule.span K _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    change y ∈ Submodule.span K _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      exact rightSpan_mono S (Nat.add_le_add hu hv) (word_bracket_mem S u v)
    | zero => simpa using (rightSpan (K := K) S (r + s)).zero_mem
    | add x y hx hy ihx ihy => simpa [lie_add] using (rightSpan (K := K) S (r + s)).add_mem ihx ihy
    | smul a x hx ih => simpa [lie_smul] using (rightSpan (K := K) S (r + s)).smul_mem a ih
  | zero => simpa using (rightSpan (K := K) S (r + s)).zero_mem
  | add x y hx hy ihx ihy => simpa [add_lie] using (rightSpan (K := K) S (r + s)).add_mem ihx ihy
  | smul a x hx ih => simpa [smul_lie] using (rightSpan (K := K) S (r + s)).smul_mem a ih

private theorem ad_pow_mem (S : I → M) (i : I) {L : ℕ} {x : M}
    (hx : x ∈ rightSpan (K := K) S L) (k : ℕ) :
    ((LieAlgebra.ad K M (S i)) ^ k) x ∈ rightSpan (K := K) S (L + k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
    simpa [Nat.add_assoc] using generator_bracket_mem S i ih

theorem polynomial_ad_mem (S : I → M) (i : I) {L : ℕ} {x : M}
    (hx : x ∈ rightSpan (K := K) S L) (p : Polynomial K) :
    Polynomial.aeval (LieAlgebra.ad K M (S i)) p x ∈
      rightSpan (K := K) S (L + p.natDegree) := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.algebraMap_end_apply]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact rightSpan_mono S (by have := Finset.mem_range.mp hk; omega) (ad_pow_mem S i hx k)


open Matrix D5.S3.Quantum.Algebra.GenericLieLengthFiltration

attribute [local instance] LieRing.ofAssociativeRing


private theorem skewProjection_apply {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    ((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp
      (skewAdjointPart ℝ)) X = (1 / 2 : ℝ) • (X - Xᴴ) := by
  change (⅟ 2 : ℝ) • (X - star X) = _
  simp only [invOf_eq_inv, one_div, Matrix.star_eq_conjTranspose]

private theorem skewProject_of_skew {n : ℕ} (X : (Matrix (Fin n) (Fin n) ℂ)) (hX : Xᴴ = -X) : ((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) X = X := by
  have hx : X ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) := hX
  exact congrArg Subtype.val
    (DFunLike.congr_fun (skewAdjointPart_comp_subtype_skewAdjoint ℝ) ⟨X, hx⟩)


private theorem skewProject_complex_smul {n : ℕ} (X : (Matrix (Fin n) (Fin n) ℂ)) (hX : Xᴴ = -X) (c : ℂ) :
    ((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) (c • X) = c.re • X := by
  ext i j
  simp [skewProjection_apply, Matrix.conjTranspose_smul, hX, Matrix.smul_apply,
    Matrix.sub_apply, Complex.real_smul, Complex.add_conj]
  apply Complex.ext <;> simp <;> ring

private theorem real_span_of_complex_span {n : ℕ} (S : Set ((Matrix (Fin n) (Fin n) ℂ)))
    (hS : ∀ Y ∈ S, Yᴴ = -Y) (X : (Matrix (Fin n) (Fin n) ℂ)) (hX : Xᴴ = -X)
    (hx : X ∈ Submodule.span ℂ S) : X ∈ Submodule.span ℝ S := by
  have hh : ∀ Z ∈ Submodule.span ℂ S, ∀ c : ℂ,
      ((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) (c • Z) ∈ Submodule.span ℝ S := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Y hY =>
      intro c
      rw [skewProject_complex_smul Y (hS Y hY) c]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hY)
    | zero => intro c; simp
    | add Y Z hY hZ ihY ihZ =>
      intro c
      rw [smul_add, map_add]
      exact Submodule.add_mem _ (ihY c) (ihZ c)
    | smul r Y hY ih =>
      intro c
      simpa only [smul_smul] using ih (c * r)
  have h := hh X hx 1
  simpa [skewProject_of_skew X hX] using h

private theorem su_bracket_mem {n : ℕ} (X Y : (Matrix (Fin n) (Fin n) ℂ)) (hX : X ∈ suSet n) (hY : Y ∈ suSet n) :
    ⁅X, Y⁆ ∈ suSet n := by
  change (⁅X, Y⁆)ᴴ = -⁅X, Y⁆ ∧ Matrix.trace ⁅X, Y⁆ = 0
  constructor
  · simp [Ring.lie_def, hX.1, hY.1, Matrix.conjTranspose_mul]
  · exact LieAlgebra.matrix_trace_commutator_zero (Fin n) ℂ X Y

def suLie (n : ℕ) : LieSubalgebra ℝ ((Matrix (Fin n) (Fin n) ℂ)) where
  __ := suSet n
  lie_mem' := fun hX hY => su_bracket_mem _ _ hX hY

private theorem word_su_mem {I : Type*} {n : ℕ} (S : I → (Matrix (Fin n) (Fin n) ℂ))
    (hS : ∀ i, S i ∈ suSet n) (w : RightWord I) : w.rightWordEval S ∈ suSet n := by
  induction w with
  | single i => exact hS i
  | cons i w ih => exact su_bracket_mem _ _ (hS i) ih

theorem rightSpan_real_le_su {I : Type*} {n : ℕ} (S : I → (Matrix (Fin n) (Fin n) ℂ))
    (hS : ∀ i, S i ∈ suSet n) (L : ℕ) : rightSpan (K := ℝ) S L ≤ suSet n := by
  apply Submodule.span_le.mpr
  rintro X ⟨w, hw, rfl⟩
  exact word_su_mem S hS w

theorem rightSpan_complex_to_real {I : Type*} {n : ℕ} (S : I → (Matrix (Fin n) (Fin n) ℂ))
    (hS : ∀ i, S i ∈ suSet n) (L : ℕ) (X : (Matrix (Fin n) (Fin n) ℂ)) (hX : X ∈ suSet n)
    (hxc : X ∈ rightSpan (K := ℂ) S L) : X ∈ rightSpan (K := ℝ) S L := by
  exact real_span_of_complex_span _
    (by rintro Y ⟨w, hw, rfl⟩; exact (word_su_mem S hS w).1) X hX.1 hxc


open Matrix D5.S3.Quantum.Algebra.GenericLieLengthFiltration Module


private theorem sl_finrank (n : ℕ) (hn : 1 ≤ n) : Module.finrank ℂ (((Matrix.traceLinearMap (Fin n) ℂ ℂ).ker)) = n ^ 2 - 1 := by
  let f := Matrix.traceLinearMap (Fin n) ℂ ℂ
  have hsur : Function.Surjective f := by
    intro c
    let o : Fin n := ⟨0, by omega⟩
    exact ⟨Matrix.single o o c, Matrix.trace_single_eq_same o c⟩
  have hr : Module.finrank ℂ f.range = 1 := by
    rw [LinearMap.range_eq_top.mpr hsur, finrank_top]
    exact Module.finrank_self ℂ
  have hh := f.finrank_range_add_finrank_ker
  rw [hr] at hh
  have hm : Module.finrank ℂ ((Matrix (Fin n) (Fin n) ℂ)) = n * n := by
    simp [Module.finrank_matrix]
  rw [hm] at hh
  change Module.finrank ℂ f.ker = n ^ 2 - 1
  rw [pow_two]
  omega

private theorem skewProject_su {n : ℕ} (X : (Matrix (Fin n) (Fin n) ℂ)) (ht : Matrix.trace X = 0) :
    ((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) X ∈ suSet n := by
  constructor
  · ext i j
    simp [skewProjection_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
    ring
  · simp [skewProjection_apply, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, ht]

private theorem reconstruction {n : ℕ} (X : (Matrix (Fin n) (Fin n) ℂ)) :
    ((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) X + Complex.I • ((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) ((-Complex.I) • X) = X := by
  ext i j
  apply Complex.ext <;>
    simp [skewProjection_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.add_apply, Complex.real_smul] <;> ring

private def combine (n : ℕ) :
    (suSet n × suSet n) →ₗ[ℝ] (Matrix.traceLinearMap (Fin n) ℂ ℂ).ker :=
  LinearMap.codRestrict ((Matrix.traceLinearMap (Fin n) ℂ ℂ).ker.restrictScalars ℝ)
    (((suSet n).subtype.comp (LinearMap.fst ℝ (suSet n) (suSet n))) +
      Complex.I • ((suSet n).subtype.comp (LinearMap.snd ℝ (suSet n) (suSet n))))
    (by
      intro XY
      change Matrix.trace (XY.1.val + Complex.I • XY.2.val) = 0
      simp only [Matrix.trace_add, Matrix.trace_smul, XY.1.property.2,
        XY.2.property.2, smul_zero, add_zero])


private theorem combine_injective (n : ℕ) : Function.Injective (combine n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro XY h
  have hh := congrArg Subtype.val h
  change XY.1.val + Complex.I • XY.2.val = 0 at hh
  have hp := congrArg (((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ))) hh
  simp only [map_add, skewProject_of_skew _ XY.1.property.1,
    skewProject_complex_smul _ XY.2.property.1, Complex.I_re, zero_smul, add_zero, map_zero] at hp
  have hx : XY.1 = 0 := Subtype.ext hp
  have hy : XY.2 = 0 := by
    apply Subtype.ext
    have hh' : Complex.I • XY.2.val = 0 := by simpa [hx] using hh
    exact (smul_eq_zero.mp hh').resolve_left Complex.I_ne_zero
  exact Prod.ext hx hy

private theorem combine_surjective (n : ℕ) : Function.Surjective (combine n) := by
  intro X
  have ht : Matrix.trace X.val = 0 := X.property
  refine ⟨(⟨((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) X.val, skewProject_su _ ht⟩,
    ⟨((skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype.comp (skewAdjointPart ℝ)) ((-Complex.I) • X.val), skewProject_su _ (by simp [ht])⟩), ?_⟩
  apply Subtype.ext
  exact reconstruction X.val

private def complexification (n : ℕ) : (suSet n × suSet n) ≃ₗ[ℝ] ((Matrix.traceLinearMap (Fin n) ℂ ℂ).ker) :=
    LinearEquiv.ofBijective (combine n) ⟨combine_injective n, combine_surjective n⟩

private theorem su_finrank (n : ℕ) (hn : 1 ≤ n) : Module.finrank ℝ (suSet n) = n ^ 2 - 1 := by
  have he := (complexification n).finrank_eq
  rw [Module.finrank_prod] at he
  have hs := Module.finrank_mul_finrank ℝ ℂ (((Matrix.traceLinearMap (Fin n) ℂ ℂ).ker))
  rw [Complex.finrank_real_complex, sl_finrank n hn] at hs
  omega



attribute [local instance] LieRing.ofAssociativeRing

private def exactWordSpan {I K M : Type*} [CommRing K] [LieRing M] [LieAlgebra K M]
    (S : I → M) (k : ℕ) : Submodule K M :=
    Submodule.span K {X | ∃ w : RightWord I, w.rightWordLength = k ∧ w.rightWordEval S = X}

private theorem layer_eq_exactWordSpan {g n : ℕ} (S : Fin g → (Matrix (Fin n) (Fin n) ℂ)) (k : ℕ) :
    layer (Finset.univ.image S) k = exactWordSpan (K := ℝ) S k := by
  induction k using Nat.twoStepInduction with
  | zero =>
    apply le_antisymm
    · exact bot_le
    · apply Submodule.span_le.mpr
      rintro X ⟨w, hw, rfl⟩
      have := w.length_pos
      omega
  | one =>
    rw [layer_one]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro X hX
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hX
      exact Submodule.subset_span ⟨.single i, rfl, rfl⟩
    · apply Submodule.span_le.mpr
      rintro X ⟨w, hw, rfl⟩
      cases w with
      | single i => exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      | cons i w => have := w.length_pos; simp only [rightWordLength] at hw; omega
  | more k ih ih1 =>
    rw [layer, ih1]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro Z ⟨X, hX, Y, hY, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hX
      induction hY using Submodule.span_induction with
      | mem Y hY =>
        obtain ⟨w, hw, rfl⟩ := hY
        exact Submodule.subset_span ⟨.cons i w, by simp [rightWordLength, hw], rfl⟩
      | zero => simp
      | add Y Z hY hZ ihY ihZ =>
        simpa [lie_add] using Submodule.add_mem (exactWordSpan (K := ℝ) S (k + 2)) ihY ihZ
      | smul r Y hY ih =>
        simpa [lie_smul] using Submodule.smul_mem (exactWordSpan (K := ℝ) S (k + 2)) r ih
    · apply Submodule.span_le.mpr
      rintro X ⟨w, hw, rfl⟩
      cases w with
      | single i => simp only [rightWordLength] at hw; omega
      | cons i w =>
        exact Submodule.subset_span ⟨S i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
          w.rightWordEval S, Submodule.subset_span ⟨w, by simpa [rightWordLength] using hw, rfl⟩, rfl⟩

private theorem cumulative_eq_rightSpan {g n : ℕ} (S : Fin g → (Matrix (Fin n) (Fin n) ℂ)) (L : ℕ) :
    (⨆ k ∈ Finset.Icc 1 L, layer (Finset.univ.image S) k) = rightSpan (K := ℝ) S L := by
  simp_rw [layer_eq_exactWordSpan]
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    apply Submodule.span_le.mpr
    rintro X ⟨w, hw, rfl⟩
    exact word_mem S w L (hw.le.trans (Finset.mem_Icc.mp hk).2)
  · apply Submodule.span_le.mpr
    rintro X ⟨w, hw, rfl⟩
    apply Submodule.mem_iSup_of_mem w.rightWordLength
    apply Submodule.mem_iSup_of_mem (Finset.mem_Icc.mpr ⟨w.length_pos, hw⟩)
    exact Submodule.subset_span ⟨w, rfl, rfl⟩

theorem lieLength_le_of_span {g n L : ℕ} (S : Fin g → (Matrix (Fin n) (Fin n) ℂ)) (hL : 1 ≤ L)
    (h : rightSpan (K := ℝ) S L = suSet n) :
    lieLength n (Finset.univ.image S) ≤ L := by
  apply Nat.sInf_le
  exact ⟨hL, by rwa [cumulative_eq_rightSpan]⟩




private def reindexWord {I J : Type*} (f : I → J) : RightWord I → RightWord J
    | .single i => .single (f i)
    | .cons i w => .cons (f i) (reindexWord f w)

private theorem reindex_length {I J : Type*} (f : I → J) (w : RightWord I) :
    (reindexWord f w).rightWordLength = w.rightWordLength := by
  induction w <;> simp_all [reindexWord, rightWordLength]

private theorem reindex_eval {I J M : Type*} [LieRing M] (f : I → J) (S : I → M) (T : J → M)
    (h : ∀ i, T (f i) = S i) (w : RightWord I) : (reindexWord f w).rightWordEval T = w.rightWordEval S := by
  induction w <;> simp_all [reindexWord, rightWordEval]

theorem rightSpan_reindex_le {I J K M : Type*} [CommRing K] [LieRing M] [LieAlgebra K M]
    (f : I → J) (S : I → M) (T : J → M) (h : ∀ i, T (f i) = S i) (L : ℕ) :
    rightSpan (K := K) S L ≤ rightSpan (K := K) T L := by
  apply Submodule.span_le.mpr
  rintro X ⟨w, hw, rfl⟩
  rw [← reindex_eval f S T h w]
  exact word_mem T (reindexWord f w) L (by simpa [reindex_length] using hw)


open Module
attribute [local instance] LieRing.ofAssociativeRing

def words (g : ℕ) : ℕ → Finset (RightWord (Fin g))
    | 0 => ∅
    | L + 1 => Finset.univ.image RightWord.single ∪
        Finset.univ.biUnion (fun i => (words g L).image (RightWord.cons i))

private theorem mem_words (g L : ℕ) (w : RightWord (Fin g)) : w ∈ words g L ↔ w.rightWordLength ≤ L := by
  induction L generalizing w with
  | zero => simp [words, Nat.ne_of_gt w.length_pos]
  | succ L ih =>
    cases w with
    | single i => simp [words, rightWordLength]
    | cons i w =>
      simp only [words, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, RightWord.cons.injEq, Finset.mem_biUnion]
      have hn : ¬ ∃ a, RightWord.single a = RightWord.cons i w := by
        rintro ⟨a, h⟩
        cases h
      rw [or_iff_right hn]
      constructor
      · rintro ⟨j, u, hu, hj, huw⟩
        subst j
        subst u
        simp only [rightWordLength]
        exact Nat.add_le_add_right ((ih w).mp hu) 1
      · intro h
        exact ⟨i, w, (ih w).mpr (by simpa [rightWordLength] using h), rfl, rfl⟩

def wordBudget (g : ℕ) : ℕ → ℕ
    | 0 => 0
    | L + 1 => g + g * wordBudget g L

theorem card_words_le (g L : ℕ) : (words g L).card ≤ wordBudget g L := by
  induction L with
  | zero => simp [words, wordBudget]
  | succ L ih =>
    have h1 := Finset.card_union_le (Finset.univ.image (RightWord.single : Fin g → RightWord (Fin g)))
      (Finset.univ.biUnion (fun i : Fin g => (words g L).image (RightWord.cons i)))
    have h2 := Finset.card_image_le (s := Finset.univ) (f := (RightWord.single : Fin g → RightWord (Fin g)))
    have h3 := Finset.card_biUnion_le (s := Finset.univ)
      (t := fun i : Fin g => (words g L).image (RightWord.cons i))
    have h4 : (∑ i : Fin g, ((words g L).image (RightWord.cons i)).card) ≤ g * wordBudget g L := by
      calc
        _ ≤ ∑ i : Fin g, wordBudget g L := Finset.sum_le_sum (fun i hi =>
          (Finset.card_image_le).trans ih)
        _ = g * wordBudget g L := by simp
    simpa only [words, wordBudget, Finset.card_univ, Fintype.card_fin] using
      h1.trans (Nat.add_le_add h2 (h3.trans h4))

private theorem budget_eq_sum (g L : ℕ) : wordBudget g L = ∑ j ∈ Finset.range L, g ^ (j + 1) := by
  induction L with
  | zero => simp [wordBudget]
  | succ L ih =>
    rw [wordBudget, ih, Finset.mul_sum]
    simp_rw [← pow_succ']
    rw [Finset.sum_range_succ', pow_one]
    omega

private theorem rightSpan_finrank_le {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (S : Fin g → M) (L : ℕ) :
    Module.finrank ℝ (rightSpan (K := ℝ) S L) ≤ wordBudget g L := by
  classical
  have he : rightSpan (K := ℝ) S L = Submodule.span ℝ
      ((words g L).image (fun w => w.rightWordEval S) : Set M) := by
    unfold rightSpan
    apply congrArg (Submodule.span ℝ)
    ext X
    simp only [Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (mem_words g L w).mpr hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (mem_words g L w).mp hw, rfl⟩
  rw [he]
  exact (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (card_words_le g L))

private theorem saturation_count (n g L : ℕ) (hn : 1 ≤ n) (S : Fin g → (Matrix (Fin n) (Fin n) ℂ))
    (h : rightSpan (K := ℝ) S L = suSet n) :
    n ^ 2 - 1 ≤ ∑ j ∈ Finset.range L, g ^ (j + 1) := by
  have hh := rightSpan_finrank_le S L
  rw [h, su_finrank n hn, budget_eq_sum] at hh
  exact hh



attribute [local instance] LieRing.ofAssociativeRing

private theorem budget_pow_bound (g L : ℕ) : wordBudget g L + 1 ≤ (g + 1) ^ L := by
  induction L with
  | zero => simp [wordBudget]
  | succ L ih =>
    have hp : 1 ≤ (g + 1) ^ L := Nat.one_le_pow L (g + 1) (by omega)
    rw [wordBudget, pow_succ']
    nlinarith

private theorem lower_log_of_saturation (n g L : ℕ) (hn : 2 ≤ n) (hg : 2 ≤ g)
    (S : Fin g → (Matrix (Fin n) (Fin n) ℂ)) (h : rightSpan (K := ℝ) S L = suSet n) :
    (1 / Real.log (g + 1)) * Real.log n ≤ (L : ℝ) := by
  have hc := saturation_count n g L (by omega) S h
  rw [← budget_eq_sum] at hc
  have hb := budget_pow_bound g L
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hp : n ≤ (g + 1) ^ L := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hreal : (n : ℝ) ≤ ((g : ℝ) + 1) ^ L := by exact_mod_cast hp
  have hl := Real.log_le_log hn0 hreal
  rw [Real.log_pow] at hl
  have hg1 : (1 : ℝ) < (g : ℝ) + 1 := by exact_mod_cast (show 1 < g + 1 by omega)
  have hglog := Real.log_pos hg1
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (div_le_iff₀ hglog).mpr hl

private theorem lieLength_attained {n g L : ℕ} (S : Fin g → (Matrix (Fin n) (Fin n) ℂ)) (hL : 1 ≤ L)
    (h : rightSpan (K := ℝ) S L = suSet n) :
    1 ≤ lieLength n (Finset.univ.image S) ∧
      rightSpan (K := ℝ) S (lieLength n (Finset.univ.image S)) = suSet n := by
  have hne : {l | 1 ≤ l ∧ (⨆ k ∈ Finset.Icc 1 l, layer (Finset.univ.image S) k) = suSet n}.Nonempty :=
    ⟨L, hL, by rwa [cumulative_eq_rightSpan]⟩
  have hm := Nat.sInf_mem hne
  change 1 ≤ lieLength n (Finset.univ.image S) ∧
    (⨆ k ∈ Finset.Icc 1 (lieLength n (Finset.univ.image S)), layer (Finset.univ.image S) k) = suSet n at hm
  exact ⟨hm.1, (cumulative_eq_rightSpan S _).symm.trans hm.2⟩

theorem lower_lieLength_of_saturation (n g L : ℕ) (hn : 2 ≤ n) (hg : 2 ≤ g)
    (S : Fin g → (Matrix (Fin n) (Fin n) ℂ)) (hL : 1 ≤ L) (h : rightSpan (K := ℝ) S L = suSet n) :
    (1 / Real.log (g + 1)) * Real.log n ≤ (lieLength n (Finset.univ.image S) : ℝ) := by
  exact lower_log_of_saturation n g _ hn hg S (lieLength_attained S hL h).2

theorem upper_log (n : ℕ) :
    (16 * (1 + Nat.log 2 (n + 1)) : ℝ) ≤ (32 / Real.log 2) * Real.log (n + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h1 := Real.natLog_le_logb (n + 1) 2
  rw [Real.logb] at h1
  have hmono : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log hn (by linarith)
  have hlo : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hm : (Nat.log 2 (n + 1) : ℝ) * Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
    apply le_trans ((le_div_iff₀ hlog2).mp ?_) hmono
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h1
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlog2).mpr
  have : 16 * (1 + (Nat.log 2 (n + 1) : ℝ)) * Real.log 2 ≤
      32 * Real.log ((n : ℝ) + 2) := by nlinarith
  simpa only [div_mul_eq_mul_div, Nat.cast_add, Nat.cast_ofNat] using this


end
end D5.S3.Quantum.Algebra.GenericLieLengthFiltration
