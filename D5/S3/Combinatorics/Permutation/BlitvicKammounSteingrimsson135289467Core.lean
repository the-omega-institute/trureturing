/- GID: D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symbolic core for the 135289467 packing count. -/
/-
admission_basis: escape-witness
escape_witness: BKS10List.idxOf_filter_lt_iff
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22588
The source packing count is reused from PackingMaximumRefutation; claim retains the
literal zero-based pattern vector and binomial expression. List.Disjoint is used
for marker exclusion; inverse ranks use List.Nodup.getEquiv and Fin.equivSubtype.
Declaration classifications:
name | proof_shape | consumers | frozen dependencies | escape_witness
BlitvicKammounSteingrimsson135289467.pattern | bind-only | BlitvicKammounSteingrimsson135289467.pattern_inverse, BlitvicKammounSteingrimsson135289467.inverse_pattern, BlitvicKammounSteingrimsson135289467.packing_chain_iff, BlitvicKammounSteingrimsson135289467.packing_one_unique, BlitvicKammounSteingrimsson135289467.patternEquiv, BlitvicKammounSteingrimsson135289467.first_count, BKS10Source.packing_word_iff, BKS10Source.sourceWordEquiv, BKS10Source.count_rawWords, BKS10BaseSymbolic.second_count, result | none | none
BlitvicKammounSteingrimsson135289467.inversePattern | bind-only | BlitvicKammounSteingrimsson135289467.pattern_inverse, BlitvicKammounSteingrimsson135289467.inverse_pattern, BlitvicKammounSteingrimsson135289467.packing_chain_iff, BlitvicKammounSteingrimsson135289467.packing_one_unique, BlitvicKammounSteingrimsson135289467.patternEquiv, BlitvicKammounSteingrimsson135289467.first_count, BKS10Source.chain_strictMono, BKS10Source.packing_word_iff | none | none
BlitvicKammounSteingrimsson135289467.pattern_inverse | bind-only | BlitvicKammounSteingrimsson135289467.packing_chain_iff, BlitvicKammounSteingrimsson135289467.packing_one_unique, BlitvicKammounSteingrimsson135289467.patternEquiv, BlitvicKammounSteingrimsson135289467.first_count | none | none
BlitvicKammounSteingrimsson135289467.inverse_pattern | bind-only | BlitvicKammounSteingrimsson135289467.packing_chain_iff, BlitvicKammounSteingrimsson135289467.patternEquiv, BlitvicKammounSteingrimsson135289467.first_count | none | none
BlitvicKammounSteingrimsson135289467.packing_chain_iff | bind-only | BlitvicKammounSteingrimsson135289467.packing_one_unique, BKS10Source.packing_word_iff | F2,F5 | none
BlitvicKammounSteingrimsson135289467.packing_one_unique | bind-only | BlitvicKammounSteingrimsson135289467.first_count | F2,F5,F7 | none
BlitvicKammounSteingrimsson135289467.patternEquiv | bind-only | BlitvicKammounSteingrimsson135289467.first_count | none | none
BlitvicKammounSteingrimsson135289467.first_count | bind-only | result | F2,F3,F4,F5,F7 | none
BKS10Structure.C | bind-only | BKS10Structure.Q, BKS10Structure.c_shift, BKS10Structure.a_min, BKS10Structure.q_min, BKS10Structure.head_iff, BKS10Structure.q_gluing_iff, BKS10Residual.q_congr, BKS10Source.rawWords, BKS10Source.chain_strictMono, BKS10Source.packing_word_iff, BKS10Source.sourceWordEquiv, BKS10Head.raw_words_as_heads, BKS10BaseSymbolic.base_words | none | none
BKS10Structure.Q | bind-only | BKS10Structure.a_min, BKS10Structure.q_min, BKS10Structure.head_iff, BKS10Structure.q_gluing_iff, BKS10Residual.words, BKS10Residual.shiftedWords, BKS10Residual.words_finite, BKS10Residual.q_congr, BKS10Residual.q_filter_iff, BKS10Residual.shifted_words_image, BKS10Residual.words_as_gluing, BKS10Residual.residual_recurrence, BKS10Head.q_prefix_iff, BKS10Head.raw_words_as_heads, BKS10BaseSymbolic.base_words | none | none
BKS10Structure.QSupport | bind-only | BKS10Structure.q_min, BKS10Structure.q_gluing_iff, BKS10Residual.mem_labels, BKS10Residual.support_split, BKS10Residual.shifted_disjoint, BKS10Residual.labels_glue_perm, BKS10Residual.q_congr, BKS10Residual.q_filter_iff, BKS10Residual.words_as_gluing, BKS10Head.head_disjoint, BKS10Head.full_labels_perm, BKS10Head.q_prefix_iff, BKS10Head.raw_words_as_heads | none | none
BKS10Structure.Head | bind-only | BKS10Structure.head_iff, BKS10Head.prefix_cases, BKS10Head.raw_words_as_heads | none | none
BKS10Structure.c_shift | bind-only | BKS10Structure.q_gluing_iff | none | none
BKS10Structure.a_min | bind-only | BKS10Structure.q_min | none | none
BKS10Structure.q_min | bind-only | BKS10Structure.q_gluing_iff, BKS10Head.raw_words_as_heads | none | none
BKS10Structure.head_iff | bind-only | BKS10Head.raw_words_as_heads | none | none
BKS10Structure.q_gluing_iff | bind-only | BKS10Residual.words_as_gluing | none | none
BKS10Words.word | bind-only | BKS10Words.word_perm, BKS10Words.word_idxOf, BKS10Source.rank_word, BKS10Source.word_rank, BKS10Source.packing_word_iff, BKS10Source.sourceWordEquiv | none | none
BKS10Words.word_perm | bind-only | BKS10Words.word_idxOf, BKS10Source.rank_word, BKS10Source.sourceWordEquiv | none | none
BKS10Words.word_idxOf | bind-only | BKS10Source.rank_word, BKS10Source.packing_word_iff | none | none
BKS10Gluing.keep | bind-only | BKS10Gluing.Shuffle, BKS10Gluing.shuffle_finite, BKS10Gluing.shuffle_card, BKS10Gluing.assemble, BKS10Gluing.assembly_injective, BKS10Gluing.language_card, BKS10Realization.keep_all, BKS10Realization.filter_remainder, BKS10Realization.one_tail, BKS10Realization.two_tail, BKS10Realization.g_to_language, BKS10Realization.language_to_g, BKS10BaseSymbolic.baseAssembly, BKS10BaseSymbolic.baseAssembly_injective, BKS10BaseSymbolic.base_words, BKS10BaseSymbolic.residual_two | none | none
BKS10Gluing.Shuffle | bind-only | BKS10Gluing.shuffle_finite, BKS10Gluing.shuffle_card, BKS10Gluing.assemble, BKS10Gluing.language, BKS10Gluing.assembly_injective, BKS10Gluing.language_card, BKS10Realization.g_to_language, BKS10Realization.language_to_g, BKS10BaseSymbolic.baseAssembly, BKS10BaseSymbolic.baseAssembly_injective, BKS10BaseSymbolic.base_words, BKS10BaseSymbolic.residual_two | none | none
BKS10Gluing.shuffle_finite | bind-only | BKS10Gluing.language_card | none | none
BKS10Gluing.shuffle_card | bind-only | BKS10Gluing.language_card, BKS10BaseSymbolic.residual_two | F6 | none
BKS10Gluing.assemble | bind-only | BKS10Gluing.language, BKS10Gluing.assembly_injective, BKS10Gluing.language_card, BKS10Realization.g_to_language, BKS10Realization.language_to_g | none | none
BKS10Gluing.language | bind-only | BKS10Gluing.language_card, BKS10Realization.g_to_language, BKS10Realization.language_to_g, BKS10Realization.gluing_card | none | none
BKS10Gluing.assembly_injective | bind-only | BKS10Gluing.language_card | none | none
BKS10Gluing.shuffle_square | bind-only | BKS10Gluing.language_card | none | none
BKS10Gluing.language_card | bind-only | BKS10Realization.gluing_card | F6 | none
BKS10Gluing.binomial_factor | bind-only | result | none | none
BKS10List.idxOf_filter_lt_iff | content | BKS10Realization.one_tail, BKS10Realization.two_tail, BKS10Realization.language_to_g, BKS10Residual.q_filter_iff, BKS10BaseSymbolic.base_words | none | BKS10List.idxOf_filter_lt_iff
BKS10List.idxOf_map_injective | bind-only | BKS10Residual.shifted_words_image | F1 | none
BKS10List.first_of_least | bind-only | BKS10List.strip_least | none | none
BKS10List.strip_least | bind-only | BKS10Realization.prefix_cases, BKS10Realization.pair_eq, BKS10Realization.one_tail, BKS10Realization.two_tail, BKS10Head.prefix_cases, BKS10BaseSymbolic.triple_eq, BKS10BaseSymbolic.base_words | none | none
BKS10Realization.marker_constraints | bind-only | BKS10Realization.prefix_cases, BKS10Realization.keep_all, BKS10Realization.two_tail, BKS10Realization.language_to_g, BKS10Realization.gluing_card | none | none
BKS10Realization.G | bind-only | BKS10Realization.prefix_cases, BKS10Realization.g_to_language, BKS10Realization.language_to_g, BKS10Realization.gluing_card, BKS10Residual.words_as_gluing, BKS10Residual.residual_recurrence | none | none
BKS10Realization.prefix_cases | bind-only | BKS10Realization.g_to_language | none | none
BKS10Realization.pair_eq | bind-only | BKS10Realization.one_tail, BKS10Realization.two_tail | none | none
BKS10Realization.keep_all | bind-only | BKS10Realization.filter_remainder, BKS10Realization.one_tail, BKS10Realization.two_tail, BKS10Realization.language_to_g, BKS10BaseSymbolic.base_words | none | none
BKS10Realization.filter_remainder | bind-only | BKS10Realization.g_to_language, BKS10Realization.language_to_g | none | none
BKS10Realization.one_tail | content | BKS10Realization.g_to_language, BKS10BaseSymbolic.base_words | none | none
BKS10Realization.two_tail | content | BKS10Realization.g_to_language | none | none
BKS10Realization.markers | bind-only | BKS10Realization.marked_notmem, BKS10Realization.g_to_language, BKS10Realization.language_to_g, BKS10Residual.support_split, BKS10Residual.labels_glue_perm, BKS10Residual.words_as_gluing | none | none
BKS10Realization.marked_notmem | bind-only | BKS10Realization.g_to_language, BKS10Realization.language_to_g, BKS10Residual.labels_glue_perm, BKS10Residual.words_as_gluing | none | none
BKS10Realization.g_to_language | content | BKS10Realization.gluing_card | none | none
BKS10Realization.language_to_g | content | BKS10Realization.gluing_card | none | none
BKS10Realization.gluing_card | content | BKS10Residual.residual_recurrence | F6 | none
BKS10Residual.labels | bind-only | BKS10Residual.words, BKS10Residual.shiftedWords, BKS10Residual.mem_labels, BKS10Residual.labels_length, BKS10Residual.labels_nodup, BKS10Residual.shifted_disjoint, BKS10Residual.labels_glue_perm, BKS10Residual.words_finite, BKS10Residual.q_filter_iff, BKS10Residual.shifted_words_image, BKS10Residual.words_as_gluing, BKS10Residual.residual_recurrence, BKS10Head.head_disjoint, BKS10Head.full_labels_perm, BKS10Head.raw_words_as_heads, BKS10BaseSymbolic.base_words | none | none
BKS10Residual.words | bind-only | BKS10Residual.words_finite, BKS10Residual.shifted_words_image, BKS10Residual.shifted_words_card, BKS10Residual.words_as_gluing, BKS10Residual.residual_recurrence, BKS10Head.raw_words_as_heads, BKS10Head.raw_words_card, BKS10BaseSymbolic.base_words, BKS10BaseSymbolic.residual_two, BKS10BaseSymbolic.second_count, result | none | none
BKS10Residual.shiftedWords | bind-only | BKS10Residual.shifted_words_image, BKS10Residual.shifted_words_card, BKS10Residual.words_as_gluing, BKS10Residual.residual_recurrence | none | none
BKS10Residual.mem_labels | bind-only | BKS10Residual.shifted_disjoint, BKS10Residual.labels_glue_perm, BKS10Residual.q_filter_iff, BKS10Residual.words_as_gluing, BKS10Head.head_disjoint, BKS10Head.full_labels_perm, BKS10Head.raw_words_as_heads | none | none
BKS10Residual.labels_length | bind-only | BKS10Residual.residual_recurrence | none | none
BKS10Residual.labels_nodup | bind-only | BKS10Residual.labels_glue_perm, BKS10Head.full_labels_perm | none | none
BKS10Residual.support_split | bind-only | BKS10Residual.labels_glue_perm | none | none
BKS10Residual.shifted_disjoint | bind-only | BKS10Residual.labels_glue_perm, BKS10Residual.words_as_gluing, BKS10Residual.residual_recurrence | none | none
BKS10Residual.labels_glue_perm | bind-only | BKS10Residual.words_as_gluing | none | none
BKS10Residual.words_finite | bind-only | BKS10Residual.residual_recurrence, BKS10Head.raw_words_card | none | none
BKS10Residual.q_congr | bind-only | BKS10Residual.q_filter_iff, BKS10Head.q_prefix_iff | none | none
BKS10Residual.q_filter_iff | content | BKS10Residual.words_as_gluing | none | none
BKS10Residual.shifted_words_image | bind-only | BKS10Residual.shifted_words_card, BKS10Residual.residual_recurrence | F1 | none
BKS10Residual.shifted_words_card | bind-only | BKS10Residual.residual_recurrence | F1 | none
BKS10Residual.words_as_gluing | content | BKS10Residual.residual_recurrence | none | none
BKS10Residual.residual_recurrence | content | result | F1,F6 | none
F1=D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.idxOf_map_relation@sha256:5e891f7ccf9d332606ce84dd6f66275885afb3e21efbb91dff37d568de8a34a6; F2=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Packs@sha256:d112cd1535182761aa1994452e746869ff7dc769951a75cc5689d293e5b6a0c6
F3=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.SourcePacking@sha256:63cb260ce4ddaa04f19ce5a8a41d51ad0f18bae5986f2ca34f3100509714c17e; F5=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.windowIndex@sha256:62b5ac78d467b174c8991bdd37a362faa5f9cb4727404339737d76a6937ddaeb
F6=D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.shuffle_count@sha256:4f51163ed6cf5a49beea5be248806044fc9b754635d5f7ab2c697edda88ae394; F7=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.windowIndex._proof_3@sha256:44018f94eeb19704569d74d9f5310be5261e9cc1cc5391de07823b8bd5c0b9e4; F4=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count@sha256:2688014241f92fd81e3f5324d3bb76c60cae1cb28dfcb2ed21d487b71a30103f
-/
import D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscending
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
import Mathlib.Order.SuccPred.Archimedean
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson135289467Core
namespace BlitvicKammounSteingrimsson135289467
open D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
def pattern : Fin 9 → Fin 9 := ![0,2,4,1,7,8,3,5,6]
def inversePattern : Fin 9 → Fin 9 := ![0,3,1,6,2,7,8,4,5]
private theorem pattern_inverse (a : Fin 9) : inversePattern (pattern a) = a := by
  fin_cases a <;> rfl
private theorem inverse_pattern (a : Fin 9) : pattern (inversePattern a) = a := by
  fin_cases a <;> rfl
theorem packing_chain_iff (j : ℕ)
    (w : Fin (9+(j-1)*6) → Fin (9+(j-1)*6)) :
    Packs pattern 3 j w ↔
    ∀ t : Fin j, StrictMono (fun a : Fin 9 =>
      w (windowIndex 9 3 j t (inversePattern a))) := by
  constructor
  · intro h t a b hab
    apply (h t _ _).mpr
    simpa only [inverse_pattern] using hab
  · intro h t a b
    have hh := (h t).lt_iff_lt (a := pattern a) (b := pattern b)
    simpa only [pattern_inverse] using hh
private theorem packing_one_unique (w : Equiv.Perm (Fin 9))
    (h : Packs pattern 3 1 w) : (w : Fin 9 → Fin 9) = pattern := by
  have hm : StrictMono (fun a : Fin 9 => w (inversePattern a)) := by
    simpa [windowIndex] using (packing_chain_iff 1 w).mp h 0
  have he : (fun a : Fin 9 => w (inversePattern a)) = id := by
    exact hm.eq_id
  funext a
  simpa only [pattern_inverse, id_eq] using congrFun he (pattern a)
private def patternEquiv : Equiv.Perm (Fin 9) where
  toFun := pattern
  invFun := inversePattern
  left_inv := pattern_inverse
  right_inv := inverse_pattern
theorem first_count : count (![0,2,4,1,7,8,3,5,6] : Fin 9 → Fin 9) 3 1 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨patternEquiv, ?_⟩, ?_⟩
  · intro t a b
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    simp [windowIndex, patternEquiv, pattern]
  · intro w
    apply Subtype.ext
    apply Equiv.ext
    exact congrFun (packing_one_unique w.val w.property)
end BlitvicKammounSteingrimsson135289467
namespace BKS10Structure
variable {α : Type*} [LinearOrder α]
def C (t : ℕ) (f : ℕ → α) : Prop :=
  f (6*t) < f (6*t+3) ∧ f (6*t+3) < f (6*t+1) ∧
  f (6*t+1) < f (6*t+6) ∧ f (6*t+6) < f (6*t+2) ∧
  f (6*t+2) < f (6*t+7) ∧ f (6*t+7) < f (6*t+8) ∧
  f (6*t+8) < f (6*t+4) ∧ f (6*t+4) < f (6*t+5)
def Q (j : ℕ) (f : ℕ → α) : Prop :=
  (f 8 < f 4 ∧ f 4 < f 5) ∧
  (f 12 < f 8 ∧ f 8 < f 13 ∧ f 13 < f 14 ∧ f 14 < f 10 ∧ f 10 < f 11) ∧
  ∀ t, 2 ≤ t → t < j → C t f
def QSupport (j x : ℕ) : Prop :=
  x = 4 ∨ x = 5 ∨ x = 8 ∨ x = 10 ∨ x = 11 ∨ (12 ≤ x ∧ x ≤ 6*j+2)
def Head (f : ℕ → α) : Prop :=
  f 0 < f 3 ∧ f 3 < f 1 ∧ f 1 < f 6 ∧ f 6 < f 2 ∧
  f 6 < f 9 ∧ f 2 < f 7 ∧ f 9 < f 7
private theorem c_shift (t : ℕ) (f : ℕ → α) :
    C t (fun x => f (x+6)) ↔ C (t+1) f := by
  simp [C, Nat.mul_add, Nat.add_assoc]
private theorem a_min (j : ℕ) (f : ℕ → α) (hq : Q j f)
    (t : ℕ) (ht : 2 ≤ t) (htj : t ≤ j) : f 12 ≤ f (6*t) := by
  have hm : MonotoneOn (fun n : ℕ => f (6*n)) (Set.Icc 2 j) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Icc
    intro n _ hn hsn
    have hs : n+1 ≤ j := hsn.2
    have hnlt : n < j := by omega
    have hc := hq.2.2 n hn.1 hnlt
    change f (6*n) ≤ f (6*(n+1))
    simpa only [Nat.mul_add, Nat.mul_one] using
      (hc.1.trans (hc.2.1.trans hc.2.2.1)).le
  exact hm ⟨le_rfl, ht.trans htj⟩ ⟨ht, htj⟩ ht
theorem q_min (j : ℕ) (hj : 2 ≤ j) (f : ℕ → α) (hq : Q j f)
    (x : ℕ) (hx : QSupport j x) : f 12 ≤ f x := by
  rcases hq with ⟨⟨h84,h45⟩,⟨h128,h813,h1314,h1410,h1011⟩,hc⟩
  rcases hx with rfl|rfl|rfl|rfl|rfl|hx
  all_goals try order
  let t := x/6
  have ht : 2 ≤ t := by dsimp [t] <;> omega
  have htj : t ≤ j := by dsimp [t] <;> omega
  have hm := a_min j f ⟨⟨h84,h45⟩,⟨h128,h813,h1314,h1410,h1011⟩,hc⟩ t ht htj
  by_cases hlast : t = j
  · have htprev : 2 ≤ j-1 ∨ j = 2 := by omega
    rcases htprev with hp | rfl
    · have cp := hc (j-1) hp (by omega)
      have he : 6*(j-1) = 6*j-6 := Nat.mul_sub_one 6 j
      have hn : 6*j-6+6 = 6*j := by omega
      have hn1 : 6*j-6+7 = 6*j+1 := by omega
      have hn2 : 6*j-6+8 = 6*j+2 := by omega
      simp only [C, he, hn, hn1, hn2] at cp
      rcases cp with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
      have hxcase : x = 6*j ∨ x = 6*j+1 ∨ x = 6*j+2 := by dsimp [t] at hlast <;> omega
      rw [hlast] at hm
      rcases hxcase with rfl|rfl|rfl <;> order
    · have hxcase : x = 12 ∨ x = 13 ∨ x = 14 := by omega
      rcases hxcase with rfl|rfl|rfl <;> order
  · have ct := hc t ht (by omega)
    rcases ct with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    have hxcase : x = 6*t ∨ x = 6*t+1 ∨ x = 6*t+2 ∨
      x = 6*t+3 ∨ x = 6*t+4 ∨ x = 6*t+5 := by dsimp [t] <;> omega
    rcases hxcase with he|he|he|he|he|he <;> rw [he] <;> order
theorem head_iff (j : ℕ) (hj : 2 ≤ j) (f : ℕ → α) :
    (∀ t, t < j → C t f) ↔ Head f ∧ f 7 < f 12 ∧ Q j f := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    have h1 := h 1 (by omega)
    norm_num [C] at h0 h1
    rcases h0 with ⟨h03,h31,h16,h62,h27,h78,h84,h45⟩
    rcases h1 with ⟨h69,h97,h712,h128,h813,h1314,h1410,h1011⟩
    refine ⟨⟨h03,h31,h16,h62,h69,h27,h97⟩,h712,
      ⟨h84,h45⟩,⟨h128,h813,h1314,h1410,h1011⟩,?_⟩
    exact fun t _ ht => h t ht
  · rintro ⟨⟨h03,h31,h16,h62,h69,h27,h97⟩,h712,
      ⟨h84,h45⟩,⟨h128,h813,h1314,h1410,h1011⟩,hc⟩ t ht
    by_cases ht0 : t=0
    · subst t
      norm_num [C]
      exact ⟨h03,h31,h16,h62,h27,lt_trans h712 h128,h84,h45⟩
    by_cases ht1 : t=1
    · subst t
      norm_num [C]
      exact ⟨h69,h97,h712,h128,h813,h1314,h1410,h1011⟩
    exact hc t (by omega) ht
private theorem q_gluing_iff (j : ℕ) (hj : 2 ≤ j) (f : ℕ → α) :
    Q (j+1) f ↔
    (f 12 < f 15 ∧ f 15 < f 13 ∧ f 12 < f 8 ∧ f 8 < f 13 ∧
      f 8 < f 4 ∧ f 4 < f 5) ∧
    (∀ x, QSupport j x → f 13 < f (x+6)) ∧ Q j (fun x => f (x+6)) := by
  constructor
  · intro h
    have hc2 := h.2.2 2 (by omega) (by omega)
    norm_num [C] at hc2
    rcases hc2 with ⟨h1215,h1513,h1318,h1814,h1419,h1920,h2016,h1617⟩
    rcases h with ⟨⟨h84,h45⟩,⟨h128,h813,h1314,h1410,h1011⟩,hc⟩
    have hr : Q j (fun x => f (x+6)) := by
      refine ⟨⟨h1410,h1011⟩,⟨h1814,h1419,h1920,h2016,h1617⟩,?_⟩
      intro t ht htj
      exact (c_shift t f).mpr (hc (t+1) (by omega) (by omega))
    refine ⟨⟨h1215,h1513,h128,h813,h84,h45⟩,?_,hr⟩
    intro x hx
    have hm := q_min j hj (fun x => f (x+6)) hr x hx
    exact lt_of_lt_of_le h1318 hm
  · rintro ⟨⟨h1215,h1513,h128,h813,h84,h45⟩,hcross,hr⟩
    have h1314 := hcross 8 (by simp [QSupport])
    have h1318 := hcross 12 (by simp [QSupport] <;> omega)
    rcases hr with ⟨⟨h1410,h1011⟩,⟨h1814,h1419,h1920,h2016,h1617⟩,hc⟩
    refine ⟨⟨h84,h45⟩,⟨h128,h813,h1314,h1410,h1011⟩,?_⟩
    intro t ht htj
    by_cases ht2 : t = 2
    · subst t
      norm_num [C]
      exact ⟨h1215,h1513,h1318,h1814,h1419,h1920,h2016,h1617⟩
    have hprev := (c_shift (t-1) f).mp (hc (t-1) (by omega) (by omega))
    simpa only [show t-1+1 = t by omega] using hprev
end BKS10Structure
namespace BKS10Words
def word {n : ℕ} (w : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn (fun i => (w.symm i).val)
theorem word_perm {n : ℕ} (w : Equiv.Perm (Fin n)) : (word w).Perm (List.range n) := by
  have hr : List.ofFn (fun i : Fin n => i.val) = List.range n := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem (xs := List.range n))
  simpa only [word,Function.comp_def,hr] using
    Equiv.Perm.ofFn_comp_perm w.symm (fun i : Fin n => i.val)
theorem word_idxOf {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    (word w).idxOf i.val = (w i).val := by
  have hd : (word w).Nodup := (word_perm w).nodup_iff.mpr List.nodup_range
  have he := hd.idxOf_getElem (i := (w i).val) (by simp [word])
  simpa [word] using he
end BKS10Words
namespace BKS10Gluing
open D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscending
def keep (x : ℕ) : Bool := decide (x ≠ 4 ∧ x ≠ 5)
def Shuffle (low high : List ℕ) :=
  {l : List ℕ // l.Perm (low ++ high) ∧ l.filter keep = low ∧
    l.filter (fun x => !(keep x)) = high}
private theorem shuffle_finite (low high : List ℕ) : Finite (Shuffle low high) := by
  apply Set.Finite.to_subtype
  apply (List.finite_toSet (low ++ high).permutations).subset
  intro l hl
  exact List.mem_permutations.mpr hl.1
theorem shuffle_card (low high : List ℕ)
    (hl : ∀ x ∈ low, keep x = true) (hh : ∀ x ∈ high, keep x = false) :
    Nat.card (Shuffle low high) = (low.length + high.length).choose low.length := by
  exact shuffle_count keep low high hl hh
private def assemble (T : Set (List ℕ)) : (Σ r : T, Shuffle (13 :: r.val) [4,5] ⊕ Shuffle (15 :: 13 :: r.val) [4,5]) → List ℕ
  | ⟨_,Sum.inl l⟩ => 12 :: 15 :: 8 :: l.val
  | ⟨_,Sum.inr l⟩ => 12 :: 8 :: l.val
private def language (T : Set (List ℕ)) : Set (List ℕ) := Set.range (assemble T)
private theorem assembly_injective (T : Set (List ℕ)) : Function.Injective (assemble T) := by
  rintro ⟨r1,k1⟩ ⟨r2,k2⟩ he
  cases k1 with
  | inl l1 =>
    cases k2 with
    | inl l2 =>
      have ht : l1.val = l2.val := by simpa only [assemble, List.cons.injEq,
        true_and] using he
      have hr := congrArg (List.filter keep) ht
      rw [l1.property.2.1,l2.property.2.1] at hr
      have hre : r1 = r2 := Subtype.ext (List.cons.inj hr).2
      subst r2
      have hle : l1 = l2 := Subtype.ext ht
      subst l2
      rfl
    | inr l2 => simp [assemble] at he
  | inr l1 =>
    cases k2 with
    | inl l2 => simp [assemble] at he
    | inr l2 =>
      have ht : l1.val = l2.val := by simpa only [assemble, List.cons.injEq,
        true_and] using he
      have hr := congrArg (List.filter keep) ht
      rw [l1.property.2.1,l2.property.2.1] at hr
      have hre : r1 = r2 := Subtype.ext (List.cons.inj (List.cons.inj hr).2).2
      subst r2
      have hle : l1 = l2 := Subtype.ext ht
      subst l2
      rfl
private theorem shuffle_square (s : ℕ) :
    (s+3).choose 2 + (s+4).choose 2 = (s+3)^2 := by
  have h1 := Nat.add_one_mul_choose_eq (s+2) 1
  have h2 := Nat.add_one_mul_choose_eq (s+3) 1
  simp only [Nat.choose_one_right] at h1 h2
  nlinarith
private theorem language_card (T : Set (List ℕ)) (hT : T.Finite) (s : ℕ)
    (hlen : ∀ r ∈ T, (r : List ℕ).length = s)
    (hdis : ∀ r ∈ T, ∀ x ∈ r, x ≠ 4 ∧ x ≠ 5) :
    (language T).ncard = (s+3)^2 * T.ncard := by
  classical
  letI : Finite T := hT.to_subtype
  letI : Fintype T := Fintype.ofFinite T
  letI (r : T) : Finite (Shuffle (13 :: r.val) [4,5]) := shuffle_finite _ _
  letI (r : T) : Finite (Shuffle (15 :: 13 :: r.val) [4,5]) := shuffle_finite _ _
  have hc := Nat.card_congr (Equiv.ofInjective (assemble T) (assembly_injective T))
  change Nat.card ((Σ r : T, Shuffle (13 :: r.val) [4,5] ⊕ Shuffle (15 :: 13 :: r.val) [4,5])) = (language T).ncard at hc
  rw [← hc]
  change Nat.card (Σ r : T,
    Shuffle (13 :: r.val) [4,5] ⊕ Shuffle (15 :: 13 :: r.val) [4,5]) = _
  rw [Nat.card_sigma]
  have hf (r : T) :
      Nat.card (Shuffle (13 :: r.val) [4,5] ⊕ Shuffle (15 :: 13 :: r.val) [4,5]) =
      (s+3)^2 := by
    rw [Nat.card_sum]
    have hp : ∀ x ∈ r.val, keep x = true := by
      intro x hx
      simp only [keep, decide_eq_true_eq]
      exact hdis r.val r.property x hx
    rw [shuffle_card _ _ (by simpa [keep] using hp) (by simp [keep]),
      shuffle_card _ _ (by simpa [keep] using hp) (by simp [keep])]
    simp only [List.length_cons, List.length_nil, hlen r.val r.property]
    have hs1 : (s+1+2).choose (s+1) = (s+3).choose 2 := Nat.choose_symm_add
    have hs2 : (s+1+1+2).choose (s+1+1) = (s+4).choose 2 := Nat.choose_symm_add
    rw [hs1,hs2]
    exact shuffle_square s
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card T = T.ncard := (Nat.card_eq_fintype_card (α := T)).symm
  simp only [hcard,Nat.cast_id,Nat.mul_comm]
theorem binomial_factor (j : ℕ) (hj : 3 ≤ j) :
    121 * Nat.choose (j-3) 0 + 168 * Nat.choose (j-3) 1 +
      72 * Nat.choose (j-3) 2 = (6*j-7)^2 := by
  let n := j-3
  have hjn : j = n+3 := by dsimp [n] <;> omega
  have hn : 2 * Nat.choose n 2 = n*(n-1) := by
    by_cases hn0 : n = 0
    · simp [hn0]
    · have h := Nat.add_one_mul_choose_eq (n-1) 1
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.choose_one_right,
        Nat.mul_comm] using h.symm
  have h6 : 6*j-7 = 6*n+11 := by omega
  change 121 * Nat.choose n 0 + 168 * Nat.choose n 1 + 72 * Nat.choose n 2 = _
  rw [h6]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.mul_one]
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hsub : n-1+1 = n := by omega
    have hpoly : n*(n-1)+n = n*n := by
      calc
        n*(n-1)+n = n*((n-1)+1) := by ring
        _ = n*n := by rw [hsub]
    nlinarith
end BKS10Gluing
namespace BKS10List
theorem idxOf_filter_lt_iff (p : ℕ → Bool) (l : List ℕ) (a b : ℕ)
    (ha : p a = true) (hb : p b = true) :
    (l.filter p).idxOf a < (l.filter p).idxOf b ↔ l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hpx : p x = true
    · by_cases hxa : x = a
      · subst x
        by_cases hab : a = b
        · subst b; simp
        · simp [List.filter_cons, ha, List.idxOf_cons, hab, Ne.symm hab]
      · by_cases hxb : x = b
        · subst x
          simp [List.filter_cons, hb, List.idxOf_cons, hxa, Ne.symm hxa]
        · simpa [List.filter_cons, hpx, List.idxOf_cons, hxa, Ne.symm hxa,
            hxb, Ne.symm hxb] using ih
    · have hxa : x ≠ a := by intro h; subst x; contradiction
      have hxb : x ≠ b := by intro h; subst x; contradiction
      simpa [List.filter_cons, hpx, List.idxOf_cons, hxa, Ne.symm hxa,
        hxb, Ne.symm hxb] using ih
private theorem idxOf_map_injective (f : ℕ → ℕ) (hf : Function.Injective f)
    (l : List ℕ) (a : ℕ) : (l.map f).idxOf (f a) = l.idxOf a := by
  simpa only [List.map_id, id_eq] using
    D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery.idxOf_map_relation
      l f id a (fun _ _ => hf.eq_iff)
private theorem first_of_least (l : List ℕ) (a : ℕ) (ha : a ∈ l)
    (hmin : ∀ x ∈ l, x ≠ a → l.idxOf a < l.idxOf x) :
    ∃ r, l = a :: r := by
  cases l with
  | nil => simp at ha
  | cons x xs =>
    by_cases hxa : x = a
    · subst x; exact ⟨xs,rfl⟩
    · have h := hmin x (by simp) hxa
      simp only [List.idxOf_cons_self] at h
      omega
theorem strip_least (l L : List ℕ) (a : ℕ) (hp : l.Perm (a :: L))
    (hm : ∀ x ∈ l, x ≠ a → l.idxOf a < l.idxOf x) :
    ∃ r, l = a :: r ∧ r.Perm L := by
  obtain ⟨r,rfl⟩ := first_of_least l a (hp.mem_iff.mpr (by simp)) hm
  exact ⟨r,rfl,List.Perm.cons_inv hp⟩
end BKS10List
namespace BKS10Realization
open BKS10List BKS10Gluing
private theorem marker_constraints (L : List ℕ) (hd : List.Disjoint L [12,15,8,13,4,5]) :
    ∀ x ∈ L, x ≠ 12 ∧ x ≠ 15 ∧ x ≠ 8 ∧ x ≠ 13 ∧ x ≠ 4 ∧ x ≠ 5 := by
  intro x hx
  simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using
    (List.disjoint_left.mp hd hx)
private def G (L l : List ℕ) : Prop :=
  l.idxOf 12 < l.idxOf 15 ∧ l.idxOf 15 < l.idxOf 13 ∧
  l.idxOf 12 < l.idxOf 8 ∧ l.idxOf 8 < l.idxOf 13 ∧
  l.idxOf 8 < l.idxOf 4 ∧ l.idxOf 4 < l.idxOf 5 ∧
  ∀ x ∈ L, l.idxOf 13 < l.idxOf x
private theorem prefix_cases (L l : List ℕ) (hd : List.Disjoint L [12,15,8,13,4,5])
    (hp : l.Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: L)) (hg : G L l) :
    (∃ z, l = 12 :: 15 :: 8 :: z ∧ z.Perm (13 :: 4 :: 5 :: L) ∧
      z.idxOf 4 < z.idxOf 5 ∧ ∀ x ∈ L, z.idxOf 13 < z.idxOf x) ∨
    (∃ z, l = 12 :: 8 :: z ∧ z.Perm (15 :: 13 :: 4 :: 5 :: L) ∧
      z.idxOf 15 < z.idxOf 13 ∧ z.idxOf 4 < z.idxOf 5 ∧
      ∀ x ∈ L, z.idxOf 13 < z.idxOf x) := by
  rcases hg with ⟨h1215,h1513,h128,h813,h84,h45,hcross⟩
  have hmin : ∀ x ∈ l, x ≠ 12 → l.idxOf 12 < l.idxOf x := by
    intro x hx hne
    have hx := hp.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|hx
    · exact (hne rfl).elim
    all_goals first | omega | (have hc := hcross x hx <;> omega)
  obtain ⟨r1,rfl,hp1⟩ := strip_least l _ 12 hp hmin
  have h1513 : r1.idxOf 15 < r1.idxOf 13 := by simpa [List.idxOf_cons] using h1513
  have h813 : r1.idxOf 8 < r1.idxOf 13 := by simpa [List.idxOf_cons] using h813
  have h84 : r1.idxOf 8 < r1.idxOf 4 := by simpa [List.idxOf_cons] using h84
  have h45 : r1.idxOf 4 < r1.idxOf 5 := by simpa [List.idxOf_cons] using h45
  have hc1 (x : ℕ) (hx : x ∈ L) : r1.idxOf 13 < r1.idxOf x := by
    have hn := Ne.symm (marker_constraints L hd x hx).1
    simpa [List.idxOf_cons,hn] using hcross x hx
  have hne : r1.idxOf 15 ≠ r1.idxOf 8 := by
    intro he
    have he' := (List.idxOf_inj (hp1.mem_iff.mpr (by simp : 15 ∈ 15 :: 8 :: 13 :: 4 :: 5 :: L))).mp he
    norm_num at he'
  rcases lt_or_gt_of_ne hne with h158 | h815
  · have hm : ∀ x ∈ r1, x ≠ 15 → r1.idxOf 15 < r1.idxOf x := by
      intro x hx hne
      have hx := hp1.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|hx
      · exact (hne rfl).elim
      all_goals try omega
      have hc := hc1 x hx
      omega
    obtain ⟨r2,rfl,hp2⟩ := strip_least r1 _ 15 hp1 hm
    have h813 : r2.idxOf 8 < r2.idxOf 13 := by simpa [List.idxOf_cons] using h813
    have h84 : r2.idxOf 8 < r2.idxOf 4 := by simpa [List.idxOf_cons] using h84
    have h45 : r2.idxOf 4 < r2.idxOf 5 := by simpa [List.idxOf_cons] using h45
    have hc2 (x : ℕ) (hx : x ∈ L) : r2.idxOf 13 < r2.idxOf x := by
      have hn := Ne.symm (marker_constraints L hd x hx).2.1
      simpa [List.idxOf_cons,hn] using hc1 x hx
    have hm : ∀ x ∈ r2, x ≠ 8 → r2.idxOf 8 < r2.idxOf x := by
      intro x hx hne
      have hx := hp2.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|rfl|rfl|hx
      · exact (hne rfl).elim
      all_goals try omega
      have hc := hc2 x hx
      omega
    obtain ⟨z,rfl,hpz⟩ := strip_least r2 _ 8 hp2 hm
    left
    refine ⟨z,rfl,hpz,?_,?_⟩
    · simpa [List.idxOf_cons] using h45
    · intro x hx
      have hn := Ne.symm (marker_constraints L hd x hx).2.2.1
      simpa [List.idxOf_cons,hn] using hc2 x hx
  · have hperm : r1.Perm (8 :: 15 :: 13 :: 4 :: 5 :: L) :=
      hp1.trans (List.Perm.swap 8 15 _)
    have hm : ∀ x ∈ r1, x ≠ 8 → r1.idxOf 8 < r1.idxOf x := by
      intro x hx hne
      have hx := hperm.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|hx
      · exact (hne rfl).elim
      all_goals try omega
      have hc := hc1 x hx
      omega
    obtain ⟨z,rfl,hpz⟩ := strip_least r1 _ 8 hperm hm
    right
    refine ⟨z,rfl,hpz,?_,?_,?_⟩
    · simpa [List.idxOf_cons] using h1513
    · simpa [List.idxOf_cons] using h45
    · intro x hx
      have hn := Ne.symm (marker_constraints L hd x hx).2.2.1
      simpa [List.idxOf_cons,hn] using hc1 x hx
private theorem pair_eq (z : List ℕ) (hp : z.Perm [4,5])
    (h : z.idxOf 4 < z.idxOf 5) : z = [4,5] := by
  have hm : ∀ x ∈ z, x ≠ 4 → z.idxOf 4 < z.idxOf x := by
    intro x hx hn
    have hx := hp.mem_iff.mp hx
    simp only [List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl
    · exact (hn rfl).elim
    · exact h
  obtain ⟨r,rfl,hpr⟩ := strip_least z [5] 4 hp hm
  have hr := List.perm_singleton.mp hpr
  rw [hr]
theorem keep_all (L : List ℕ) (hd : List.Disjoint L [12,15,8,13,4,5]) :
    ∀ x ∈ L, keep x = true := by
  intro x hx
  simpa only [keep,decide_eq_true_eq] using (marker_constraints L hd x hx).2.2.2.2
private theorem filter_remainder (L z r P : List ℕ) (hd : List.Disjoint L [12,15,8,13,4,5])
    (hr : r.Perm L) (hP : ∀ x ∈ P, x ∉ L)
    (he : z.filter keep = P ++ r) :
    z.filter (fun x => decide (x ∈ L)) = r := by
  let sel : ℕ → Bool := fun x => decide (x ∈ L)
  have hcomp : (z.filter keep).filter sel = z.filter sel := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x hx
    by_cases hxl : x ∈ L
    · simp [sel,hxl,keep_all L hd x hxl]
    · simp [sel,hxl]
  rw [he,List.filter_append] at hcomp
  have hpf : P.filter sel = [] := List.filter_eq_nil_iff.mpr (by
    intro x hx
    simp [sel,hP x hx])
  have hrf : r.filter sel = r := List.filter_eq_self.mpr (by
    intro x hx
    simp [sel,hr.mem_iff.mp hx])
  simpa only [hpf,hrf,List.nil_append] using hcomp.symm
theorem one_tail (L z : List ℕ) (hd : List.Disjoint L [12,15,8,13,4,5])
    (hp : z.Perm (13 :: 4 :: 5 :: L))
    (h45 : z.idxOf 4 < z.idxOf 5)
    (hc : ∀ x ∈ L, z.idxOf 13 < z.idxOf x) :
    ∃ r, r.Perm L ∧ z.Perm ((13 :: r) ++ [4,5]) ∧
      z.filter keep = 13 :: r ∧ z.filter (fun x => !(keep x)) = [4,5] := by
  have hkeep := keep_all L hd
  have hLf : L.filter keep = L := List.filter_eq_self.mpr hkeep
  have hLn : L.filter (fun x => !(keep x)) = [] := List.filter_eq_nil_iff.mpr (by
    intro x hx
    simp [hkeep x hx])
  have hlow : (z.filter keep).Perm (13 :: L) := by
    simpa [keep,hLf] using hp.filter keep
  have hhigh : (z.filter (fun x => !(keep x))).Perm [4,5] := by
    simpa only [List.filter_cons,show keep 13 = true by decide,show keep 15 = true by decide,
      show keep 4 = false by decide,show keep 5 = false by decide,
      Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true,hLn] using
      hp.filter (fun x => !(keep x))
  have huv : z.filter (fun x => !(keep x)) = [4,5] := pair_eq _ hhigh
    ((idxOf_filter_lt_iff _ z 4 5 (by decide) (by decide)).mpr h45)
  have hm : ∀ x ∈ z.filter keep, x ≠ 13 →
      (z.filter keep).idxOf 13 < (z.filter keep).idxOf x := by
    intro x hx hn
    have hx := hlow.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact (hn rfl).elim
    · exact (idxOf_filter_lt_iff keep z 13 x (by decide) (hkeep x hx)).mpr (hc x hx)
  obtain ⟨r,he,hr⟩ := strip_least (z.filter keep) L 13 hlow hm
  refine ⟨r,hr,?_,he,huv⟩
  have hpart := List.filter_append_perm keep z
  rw [he,huv] at hpart
  exact hpart.symm
private theorem two_tail (L z : List ℕ) (hd : List.Disjoint L [12,15,8,13,4,5])
    (hp : z.Perm (15 :: 13 :: 4 :: 5 :: L))
    (h1513 : z.idxOf 15 < z.idxOf 13) (h45 : z.idxOf 4 < z.idxOf 5)
    (hc : ∀ x ∈ L, z.idxOf 13 < z.idxOf x) :
    ∃ r, r.Perm L ∧ z.Perm ((15 :: 13 :: r) ++ [4,5]) ∧
      z.filter keep = 15 :: 13 :: r ∧
      z.filter (fun x => !(keep x)) = [4,5] := by
  have hkeep := keep_all L hd
  have hLf : L.filter keep = L := List.filter_eq_self.mpr hkeep
  have hLn : L.filter (fun x => !(keep x)) = [] := List.filter_eq_nil_iff.mpr (by
    intro x hx
    simp [hkeep x hx])
  have hlow : (z.filter keep).Perm (15 :: 13 :: L) := by
    simpa [keep,hLf] using hp.filter keep
  have hhigh : (z.filter (fun x => !(keep x))).Perm [4,5] := by
    simpa only [List.filter_cons,show keep 13 = true by decide,show keep 15 = true by decide,
      show keep 4 = false by decide,show keep 5 = false by decide,
      Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true,hLn] using
      hp.filter (fun x => !(keep x))
  have huv : z.filter (fun x => !(keep x)) = [4,5] := pair_eq _ hhigh
    ((idxOf_filter_lt_iff _ z 4 5 (by decide) (by decide)).mpr h45)
  have h15c : (z.filter keep).idxOf 15 < (z.filter keep).idxOf 13 :=
    (idxOf_filter_lt_iff keep z 15 13 (by decide) (by decide)).mpr h1513
  have hcx (x : ℕ) (hx : x ∈ L) :
      (z.filter keep).idxOf 13 < (z.filter keep).idxOf x :=
    (idxOf_filter_lt_iff keep z 13 x (by decide) (hkeep x hx)).mpr (hc x hx)
  have hm : ∀ x ∈ z.filter keep, x ≠ 15 →
      (z.filter keep).idxOf 15 < (z.filter keep).idxOf x := by
    intro x hx hn
    have hx := hlow.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|rfl|hx
    · exact (hn rfl).elim
    · exact h15c
    · have hh := hcx x hx
      omega
  obtain ⟨r1,he1,hp1⟩ := strip_least (z.filter keep) (13 :: L) 15 hlow hm
  have hc1 (x : ℕ) (hx : x ∈ L) : r1.idxOf 13 < r1.idxOf x := by
    have hn := Ne.symm (marker_constraints L hd x hx).2.1
    simpa [he1,List.idxOf_cons,hn] using hcx x hx
  have hm1 : ∀ x ∈ r1, x ≠ 13 → r1.idxOf 13 < r1.idxOf x := by
    intro x hx hn
    have hx := hp1.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact (hn rfl).elim
    · exact hc1 x hx
  obtain ⟨r,he2,hr⟩ := strip_least r1 L 13 hp1 hm1
  have he : z.filter keep = 15 :: 13 :: r := by rw [he1,he2]
  refine ⟨r,hr,?_,he,huv⟩
  have hpart := List.filter_append_perm keep z
  rw [he,huv] at hpart
  exact hpart.symm
private def markers : List ℕ := [12,15,8,13,4,5]
private theorem marked_notmem (L : List ℕ) (hd : List.Disjoint L [12,15,8,13,4,5])
    (x : ℕ) (hx : x ∈ markers) : x ∉ L := by
  exact List.Disjoint.symm hd hx
private theorem g_to_language (L l : List ℕ) (T : Set (List ℕ))
    (hd : List.Disjoint L [12,15,8,13,4,5]) (hp : l.Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: L))
    (hg : G L l) (hT : l.filter (fun x => decide (x ∈ L)) ∈ T) :
    l ∈ language T := by
  rcases prefix_cases L l hd hp hg with ⟨z,rfl,hpz,h45,hc⟩|⟨z,rfl,hpz,h15c,h45,hc⟩
  · obtain ⟨r,hr,hperm,hlow,hhigh⟩ := one_tail L z hd hpz h45 hc
    have hwlow : (12 :: 15 :: 8 :: z).filter keep = [12,15,8,13] ++ r := by
      simp [keep,hlow]
    have hP : ∀ x ∈ [12,15,8,13], x ∉ L := by
      intro x hx
      apply marked_notmem L hd x
      simp only [markers,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at *
      tauto
    have he := filter_remainder L (12 :: 15 :: 8 :: z) r [12,15,8,13] hd hr hP hwlow
    have hrT : r ∈ T := by rwa [he] at hT
    refine ⟨⟨⟨r,hrT⟩,Sum.inl ⟨z,hperm,hlow,hhigh⟩⟩,rfl⟩
  · obtain ⟨r,hr,hperm,hlow,hhigh⟩ := two_tail L z hd hpz h15c h45 hc
    have hwlow : (12 :: 8 :: z).filter keep = [12,8,15,13] ++ r := by
      simp [keep,hlow]
    have hP : ∀ x ∈ [12,8,15,13], x ∉ L := by
      intro x hx
      apply marked_notmem L hd x
      simp only [markers,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at *
      tauto
    have he := filter_remainder L (12 :: 8 :: z) r [12,8,15,13] hd hr hP hwlow
    have hrT : r ∈ T := by rwa [he] at hT
    refine ⟨⟨⟨r,hrT⟩,Sum.inr ⟨z,hperm,hlow,hhigh⟩⟩,rfl⟩
private theorem language_to_g (L l : List ℕ) (T : Set (List ℕ))
    (hd : List.Disjoint L [12,15,8,13,4,5]) (hwords : ∀ r ∈ T, (r : List ℕ).Perm L)
    (hl : l ∈ language T) :
    l.Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: L) ∧ G L l ∧
      l.filter (fun x => decide (x ∈ L)) ∈ T := by
  rcases hl with ⟨⟨r,k⟩,rfl⟩
  have hr := hwords r.val r.property
  have hk (x : ℕ) (hx : x ∈ L) : keep x = true := keep_all L hd x hx
  cases k with
  | inl z =>
    change (12 :: 15 :: 8 :: z.val).Perm _ ∧ G L (12 :: 15 :: 8 :: z.val) ∧
      (12 :: 15 :: 8 :: z.val).filter (fun x => decide (x ∈ L)) ∈ T
    have hperm : ((13 :: r.val) ++ [4,5]).Perm (13 :: 4 :: 5 :: L) := by
      apply List.Perm.cons 13
      exact List.perm_append_comm.trans (hr.append_left [4,5])
    have huv : z.val.idxOf 4 < z.val.idxOf 5 := by
      apply (idxOf_filter_lt_iff (fun x => !(keep x)) z.val 4 5 (by decide) (by decide)).mp
      rw [z.property.2.2]
      decide
    have hcx (x : ℕ) (hx : x ∈ L) : z.val.idxOf 13 < z.val.idxOf x := by
      apply (idxOf_filter_lt_iff keep z.val 13 x (by decide) (hk x hx)).mp
      rw [z.property.2.1]
      have hn := Ne.symm (marker_constraints L hd x hx).2.2.2.1
      simp [List.idxOf_cons,hn]
    refine ⟨(z.property.1.trans hperm).cons 8 |>.cons 15 |>.cons 12,?_,?_⟩
    · unfold G
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · simp [List.idxOf_cons]
      · simp [List.idxOf_cons] <;> omega
      · simp [List.idxOf_cons]
      · simp [List.idxOf_cons] <;> omega
      · simp [List.idxOf_cons] <;> omega
      · simpa [List.idxOf_cons] using huv
      · intro x hx
        have hn := marker_constraints L hd x hx
        simpa [List.idxOf_cons,Ne.symm hn.1,Ne.symm hn.2.1,Ne.symm hn.2.2.1] using hcx x hx
    · have hwlow : (12 :: 15 :: 8 :: z.val).filter keep = [12,15,8,13] ++ r.val := by
        simp [keep,z.property.2.1]
      have hP : ∀ x ∈ [12,15,8,13], x ∉ L := by
        intro x hx
        apply marked_notmem L hd x
        simp only [markers,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at *
        tauto
      rw [filter_remainder L _ r.val [12,15,8,13] hd hr hP hwlow]
      exact r.property
  | inr z =>
    change (12 :: 8 :: z.val).Perm _ ∧ G L (12 :: 8 :: z.val) ∧
      (12 :: 8 :: z.val).filter (fun x => decide (x ∈ L)) ∈ T
    have hperm : ((15 :: 13 :: r.val) ++ [4,5]).Perm (15 :: 13 :: 4 :: 5 :: L) := by
      apply List.Perm.cons 15
      apply List.Perm.cons 13
      exact List.perm_append_comm.trans (hr.append_left [4,5])
    have huv : z.val.idxOf 4 < z.val.idxOf 5 := by
      apply (idxOf_filter_lt_iff (fun x => !(keep x)) z.val 4 5 (by decide) (by decide)).mp
      rw [z.property.2.2]
      decide
    have hbc : z.val.idxOf 15 < z.val.idxOf 13 := by
      apply (idxOf_filter_lt_iff keep z.val 15 13 (by decide) (by decide)).mp
      rw [z.property.2.1]
      simp [List.idxOf_cons]
    have hcx (x : ℕ) (hx : x ∈ L) : z.val.idxOf 13 < z.val.idxOf x := by
      apply (idxOf_filter_lt_iff keep z.val 13 x (by decide) (hk x hx)).mp
      rw [z.property.2.1]
      have hn := marker_constraints L hd x hx
      simp [List.idxOf_cons,Ne.symm hn.2.1,Ne.symm hn.2.2.2.1]
    refine ⟨((z.property.1.trans hperm).cons 8 |>.cons 12).trans
      ((List.Perm.swap 15 8 _).cons 12),?_,?_⟩
    · unfold G
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · simp [List.idxOf_cons] <;> omega
      · simpa [List.idxOf_cons] using hbc
      · simp [List.idxOf_cons]
      · simp [List.idxOf_cons] <;> omega
      · simp [List.idxOf_cons] <;> omega
      · simpa [List.idxOf_cons] using huv
      · intro x hx
        have hn := marker_constraints L hd x hx
        simpa [List.idxOf_cons,Ne.symm hn.1,Ne.symm hn.2.2.1] using hcx x hx
    · have hwlow : (12 :: 8 :: z.val).filter keep = [12,8,15,13] ++ r.val := by
        simp [keep,z.property.2.1]
      have hP : ∀ x ∈ [12,8,15,13], x ∉ L := by
        intro x hx
        apply marked_notmem L hd x
        simp only [markers,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at *
        tauto
      rw [filter_remainder L _ r.val [12,8,15,13] hd hr hP hwlow]
      exact r.property
private theorem gluing_card (L : List ℕ) (T : Set (List ℕ)) (hd : List.Disjoint L [12,15,8,13,4,5])
    (hT : T.Finite) (hwords : ∀ r ∈ T, (r : List ℕ).Perm L) :
    ({l : List ℕ | l.Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: L) ∧ G L l ∧
      l.filter (fun x => decide (x ∈ L)) ∈ T} : Set (List ℕ)).ncard =
    (L.length+3)^2 * T.ncard := by
  have he : {l : List ℕ | l.Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: L) ∧ G L l ∧
      l.filter (fun x => decide (x ∈ L)) ∈ T} = language T := by
    ext l
    exact ⟨fun ⟨hp,hg,ht⟩ => g_to_language L l T hd hp hg ht,
      language_to_g L l T hd hwords⟩
  rw [he]
  apply language_card T hT L.length
  · intro r hr
    exact (hwords r hr).length_eq
  · intro r hr x hx
    exact (marker_constraints L hd x ((hwords r hr).mem_iff.mp hx)).2.2.2.2
end BKS10Realization
namespace BKS10Residual
open BKS10Structure BKS10Gluing BKS10List BKS10Realization
def labels (j : ℕ) : List ℕ := [4,5,8,10,11] ++ List.range' 12 (6*j-9)
def words (j : ℕ) : Set (List ℕ) := {l | l.Perm (labels j) ∧ Q j l.idxOf}
private def shiftedWords (j : ℕ) : Set (List ℕ) :=
  {l | l.Perm ((labels j).map (fun x => x+6)) ∧ Q j (fun x => l.idxOf (x+6))}
theorem mem_labels (j : ℕ) (hj : 2 ≤ j) (x : ℕ) :
    x ∈ labels j ↔ QSupport j x := by
  simp only [labels,List.mem_append,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false,List.mem_range'_1,QSupport]
  omega
private theorem labels_length (j : ℕ) (hj : 2 ≤ j) : (labels j).length = 6*j-4 := by
  simp only [labels,List.length_append,List.length_cons,List.length_nil,List.length_range']
  omega
theorem labels_nodup (j : ℕ) : (labels j).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨by decide,List.nodup_range',?_⟩
  rw [List.disjoint_left]
  intro x hx hy
  simp only [List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hx
  have hy := List.mem_range'_1.mp hy
  omega
private theorem support_split (j : ℕ) (hj : 2 ≤ j) (x : ℕ) :
    QSupport (j+1) x ↔ x ∈ markers ∨ ∃ y, QSupport j y ∧ x = y+6 := by
  constructor
  · intro hx
    by_cases hm : x ∈ markers
    · exact Or.inl hm
    · right
      refine ⟨x-6,?_,?_⟩
      all_goals simp only [QSupport,markers,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at *
      all_goals omega
  · rintro (hm|⟨y,hy,rfl⟩)
    · simp only [markers,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hm
      unfold QSupport
      omega
    · unfold QSupport at *
      omega
private theorem shifted_disjoint (j : ℕ) (hj : 2 ≤ j) :
    List.Disjoint ((labels j).map (fun x => x+6)) [12,15,8,13,4,5] := by
  rw [List.disjoint_left]
  intro x hx hm
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  have hy := (mem_labels j hj y).mp hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  unfold QSupport at hy
  omega
private theorem labels_glue_perm (j : ℕ) (hj : 2 ≤ j) :
    (labels (j+1)).Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 ::
      (labels j).map (fun x => x+6)) := by
  let L := (labels j).map (fun x => x+6)
  have hd := shifted_disjoint j hj
  have hnot (x : ℕ) (hx : x ∈ markers) : x ∉ L := marked_notmem L hd x hx
  have hnd : L.Nodup := (labels_nodup j).map (fun _ _ h => Nat.add_right_cancel h)
  have hnd' : (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: L).Nodup := by
    simp [List.nodup_cons,hnd,hnot 12 (by decide),hnot 15 (by decide),
      hnot 8 (by decide),hnot 13 (by decide),hnot 4 (by decide),hnot 5 (by decide)]
  apply (List.perm_ext_iff_of_nodup (labels_nodup _) hnd').mpr
  intro x
  rw [mem_labels (j+1) (by omega),support_split j hj]
  simp only [L,markers,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false,List.mem_map]
  constructor
  · rintro (hm|⟨y,hy,he⟩)
    · tauto
    · right;right;right;right;right;right
      exact ⟨y,(mem_labels j hj y).mpr hy,he.symm⟩
  · rintro (h|h|h|h|h|h|⟨y,hy,he⟩)
    all_goals try (left;tauto)
    right
    exact ⟨y,(mem_labels j hj y).mp hy,he.symm⟩
theorem words_finite (j : ℕ) : (words j).Finite := by
  apply (List.finite_toSet (labels j).permutations).subset
  intro l hl
  exact List.mem_permutations.mpr hl.1
theorem q_congr (j : ℕ) (hj : 2 ≤ j) (f g : ℕ → ℕ)
    (hc : ∀ x y, QSupport j x → QSupport j y → (f x < f y ↔ g x < g y)) :
    Q j f ↔ Q j g := by
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3,h4,h5,h6⟩,htail⟩
    refine ⟨⟨(hc 8 4 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h0,
      (hc 4 5 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h1⟩,
      ⟨(hc 12 8 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h2,
      (hc 8 13 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h3,
      (hc 13 14 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h4,
      (hc 14 10 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h5,
      (hc 10 11 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h6⟩,?_⟩
    intro t ht htj
    rcases htail t ht htj with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    unfold C
    exact ⟨(hc (6*t) (6*t+3) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h0,
      (hc (6*t+3) (6*t+1) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h1,
      (hc (6*t+1) (6*t+6) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h2,
      (hc (6*t+6) (6*t+2) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h3,
      (hc (6*t+2) (6*t+7) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h4,
      (hc (6*t+7) (6*t+8) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h5,
      (hc (6*t+8) (6*t+4) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h6,
      (hc (6*t+4) (6*t+5) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mp h7⟩
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3,h4,h5,h6⟩,htail⟩
    refine ⟨⟨(hc 8 4 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h0,
      (hc 4 5 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h1⟩,
      ⟨(hc 12 8 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h2,
      (hc 8 13 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h3,
      (hc 13 14 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h4,
      (hc 14 10 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h5,
      (hc 10 11 (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h6⟩,?_⟩
    intro t ht htj
    rcases htail t ht htj with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    unfold C
    exact ⟨(hc (6*t) (6*t+3) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h0,
      (hc (6*t+3) (6*t+1) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h1,
      (hc (6*t+1) (6*t+6) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h2,
      (hc (6*t+6) (6*t+2) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h3,
      (hc (6*t+2) (6*t+7) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h4,
      (hc (6*t+7) (6*t+8) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h5,
      (hc (6*t+8) (6*t+4) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h6,
      (hc (6*t+4) (6*t+5) (by unfold QSupport <;> omega) (by unfold QSupport <;> omega)).mpr h7⟩
private theorem q_filter_iff (j : ℕ) (hj : 2 ≤ j) (l : List ℕ) :
    Q j (fun x => (l.filter (fun z => decide (z ∈ (labels j).map (fun y => y+6)))).idxOf (x+6)) ↔
      Q j (fun x => l.idxOf (x+6)) := by
  let sel : ℕ → Bool := fun z => decide (z ∈ (labels j).map (fun y => y+6))
  have hs (x : ℕ) (hx : QSupport j x) : sel (x+6) = true := by
    simp only [sel,decide_eq_true_eq,List.mem_map]
    exact ⟨x,(mem_labels j hj x).mpr hx,rfl⟩
  exact q_congr j hj _ _ (fun x y hx hy => idxOf_filter_lt_iff sel l
    (x+6) (y+6) (hs x hx) (hs y hy))
private theorem shifted_words_image (j : ℕ) :
    shiftedWords j = List.map (fun x => x+6) '' words j := by
  ext l
  constructor
  · rintro ⟨hp,hq⟩
    let r := l.map (fun x => x-6)
    have hmin (x : ℕ) (hx : x ∈ l) : 6 ≤ x := by
      obtain ⟨y,_,he⟩ := List.mem_map.mp (hp.mem_iff.mp hx)
      omega
    have he : r.map (fun x => x+6) = l := by
      change (l.map (fun x => x-6)).map (fun x => x+6) = l
      rw [List.map_map]
      calc
        l.map ((fun x => x+6) ∘ (fun x => x-6)) = l.map id :=
          List.map_congr_left (fun x hx => Nat.sub_add_cancel (hmin x hx))
        _ = l := List.map_id l
    have hpr : r.Perm (labels j) := by
      have hrhs : ((labels j).map (fun x => x+6)).map (fun x => x-6) = labels j := by
        rw [List.map_map]
        calc
          (labels j).map ((fun x => x-6) ∘ (fun x => x+6)) = (labels j).map id := by
            apply List.map_congr_left
            intro x hx
            dsimp only [Function.comp_apply,id_eq]
            omega
          _ = labels j := List.map_id _
      have hm := hp.map (fun x => x-6)
      change (l.map (fun x => x-6)).Perm
        (((labels j).map (fun x => x+6)).map (fun x => x-6)) at hm
      rw [hrhs] at hm
      exact hm
    have hidx (x : ℕ) : l.idxOf (x+6) = r.idxOf x := by
      rw [← he]
      exact idxOf_map_injective (fun x => x+6) (fun _ _ h => Nat.add_right_cancel h) r x
    refine ⟨r,⟨hpr,?_⟩,he⟩
    simpa only [hidx] using hq
  · rintro ⟨r,⟨hp,hq⟩,rfl⟩
    refine ⟨hp.map (fun x => x+6),?_⟩
    have hidx (x : ℕ) : (r.map (fun x => x+6)).idxOf (x+6) = r.idxOf x :=
      idxOf_map_injective (fun x => x+6) (fun _ _ h => Nat.add_right_cancel h) r x
    simpa only [hidx] using hq
private theorem shifted_words_card (j : ℕ) : (shiftedWords j).ncard = (words j).ncard := by
  rw [shifted_words_image]
  exact Set.ncard_image_of_injective _
    (List.map_injective_iff.mpr (fun _ _ h => Nat.add_right_cancel h))
private theorem words_as_gluing (j : ℕ) (hj : 2 ≤ j) :
    words (j+1) = {l : List ℕ |
      l.Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: (labels j).map (fun x => x+6)) ∧
      G ((labels j).map (fun x => x+6)) l ∧
      l.filter (fun x => decide (x ∈ (labels j).map (fun y => y+6))) ∈ shiftedWords j} := by
  let L := (labels j).map (fun x => x+6)
  let sel : ℕ → Bool := fun x => decide (x ∈ L)
  have hd := shifted_disjoint j hj
  have hnot (x : ℕ) (hx : x ∈ markers) : x ∉ L := marked_notmem L hd x hx
  have hfL : L.filter sel = L := List.filter_eq_self.mpr (by intro x hx; simp [sel,hx])
  have hpFilter (l : List ℕ) (hp : l.Perm (12 :: 15 :: 8 :: 13 :: 4 :: 5 :: L)) :
      (l.filter sel).Perm L := by
    simpa [sel,hfL,hnot 12 (by decide),hnot 15 (by decide),hnot 8 (by decide),
      hnot 13 (by decide),hnot 4 (by decide),hnot 5 (by decide)] using hp.filter sel
  have hcross (l : List ℕ) :
      (∀ x, QSupport j x → l.idxOf 13 < l.idxOf (x+6)) ↔
        ∀ y ∈ L, l.idxOf 13 < l.idxOf y := by
    constructor
    · intro h y hy
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      exact h x ((mem_labels j hj x).mp hx)
    · intro h x hx
      exact h (x+6) (List.mem_map.mpr ⟨x,(mem_labels j hj x).mpr hx,rfl⟩)
  have hq (l : List ℕ) : Q (j+1) l.idxOf ↔ G L l ∧ Q j (fun x => l.idxOf (x+6)) := by
    rw [q_gluing_iff j hj,hcross]
    unfold G
    tauto
  ext l
  constructor
  · rintro ⟨hp,hql⟩
    have hp' := hp.trans (labels_glue_perm j hj)
    have hgen := (hq l).mp hql
    refine ⟨hp',hgen.1,hpFilter l hp',?_⟩
    exact (q_filter_iff j hj l).mpr hgen.2
  · rintro ⟨hp,hg,hfperm,hfq⟩
    refine ⟨hp.trans (labels_glue_perm j hj).symm,(hq l).mpr ⟨hg,?_⟩⟩
    exact (q_filter_iff j hj l).mp hfq
theorem residual_recurrence (j : ℕ) (hj : 2 ≤ j) :
    (words (j+1)).ncard = (6*j-1)^2 * (words j).ncard := by
  let L := (labels j).map (fun x => x+6)
  have hT : (shiftedWords j).Finite := by
    rw [shifted_words_image]
    exact (words_finite j).image _
  have hwords : ∀ r ∈ shiftedWords j, (r : List ℕ).Perm L := fun r hr => hr.1
  have hc := gluing_card L (shiftedWords j) (shifted_disjoint j hj) hT hwords
  rw [words_as_gluing j hj]
  change _ = _ at hc
  rw [hc,shifted_words_card]
  congr 2
  dsimp [L]
  rw [List.length_map,labels_length j hj]
  omega
end BKS10Residual
end D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson135289467Core
