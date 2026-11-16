/- GID: D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Product factors for the pattern 135289467 with overlap three. -/
/-
admission_basis: open-problem-resolution (#21331; Proved)
escape_witness: none; settling result
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22588
The source packing count is reused from PackingMaximumRefutation; claim retains the
literal zero-based pattern vector and binomial expression. List.Disjoint is used
for marker exclusion; inverse ranks use List.Nodup.getEquiv and Fin.equivSubtype.
Declaration classifications:
name | proof_shape | consumers | frozen dependencies | escape_witness
BKS10Source.rankEquiv | bind-only | BKS10Source.rank_word, BKS10Source.word_rank, BKS10Source.sourceWordEquiv | none | none
BKS10Source.rank_word | bind-only | BKS10Source.sourceWordEquiv | none | none
BKS10Source.word_rank | bind-only | BKS10Source.sourceWordEquiv | none | none
BKS10Source.rawWords | bind-only | BKS10Source.sourceWordEquiv, BKS10Source.count_rawWords, BKS10Head.raw_words_as_heads, BKS10Head.raw_words_card, BKS10BaseSymbolic.second_count, result | none | none
BKS10Source.chain_strictMono | bind-only | BKS10Source.packing_word_iff | none | none
BKS10Source.packing_word_iff | bind-only | BKS10Source.sourceWordEquiv | F2,F5,F7 | none
BKS10Source.sourceWordEquiv | bind-only | BKS10Source.count_rawWords | F2,F3,F5,F7 | none
BKS10Source.count_rawWords | bind-only | BKS10BaseSymbolic.second_count, result | F2,F3,F4,F5,F7 | none
BKS10Head.firstHead | bind-only | BKS10Head.prefix_cases, BKS10Head.head_disjoint, BKS10Head.full_labels_perm, BKS10Head.raw_words_as_heads, BKS10Head.raw_words_card | none | none
BKS10Head.secondHead | bind-only | BKS10Head.prefix_cases, BKS10Head.raw_words_as_heads, BKS10Head.raw_words_card | none | none
BKS10Head.prefix_cases | bind-only | BKS10Head.raw_words_as_heads | none | none
BKS10Head.head_disjoint | bind-only | BKS10Head.full_labels_perm, BKS10Head.raw_words_as_heads | none | none
BKS10Head.full_labels_perm | bind-only | BKS10Head.raw_words_as_heads | none | none
BKS10Head.q_prefix_iff | bind-only | BKS10Head.raw_words_as_heads | none | none
BKS10Head.raw_words_as_heads | content | BKS10Head.raw_words_card | none | none
BKS10Head.raw_words_card | content | BKS10BaseSymbolic.second_count, result | none | none
BKS10BaseSymbolic.triple_eq | bind-only | BKS10BaseSymbolic.base_words | none | none
BKS10BaseSymbolic.baseAssembly | bind-only | BKS10BaseSymbolic.baseAssembly_injective, BKS10BaseSymbolic.base_words, BKS10BaseSymbolic.residual_two | none | none
BKS10BaseSymbolic.baseAssembly_injective | bind-only | BKS10BaseSymbolic.residual_two | none | none
BKS10BaseSymbolic.base_words | content | BKS10BaseSymbolic.residual_two | none | none
BKS10BaseSymbolic.residual_two | content | BKS10BaseSymbolic.second_count | F6 | none
BKS10BaseSymbolic.second_count | content | result | F2,F3,F4,F5,F6,F7 | none
claim | bind-only | result | F4 | none
result | content | settling result | F1,F2,F3,F4,F5,F6,F7 | none
F1=D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.idxOf_map_relation@sha256:5e891f7ccf9d332606ce84dd6f66275885afb3e21efbb91dff37d568de8a34a6; F2=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Packs@sha256:d112cd1535182761aa1994452e746869ff7dc769951a75cc5689d293e5b6a0c6
F3=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.SourcePacking@sha256:63cb260ce4ddaa04f19ce5a8a41d51ad0f18bae5986f2ca34f3100509714c17e; F4=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count@sha256:2688014241f92fd81e3f5324d3bb76c60cae1cb28dfcb2ed21d487b71a30103f
F5=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.windowIndex@sha256:62b5ac78d467b174c8991bdd37a362faa5f9cb4727404339737d76a6937ddaeb; F6=D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.shuffle_count@sha256:4f51163ed6cf5a49beea5be248806044fc9b754635d5f7ab2c697edda88ae394; F7=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.windowIndex._proof_3@sha256:44018f94eeb19704569d74d9f5310be5261e9cc1cc5391de07823b8bd5c0b9e4
-/
import D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson135289467Core
import D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson135289467Product


open D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson135289467Core

namespace BKS10Source
open BKS10Structure BKS10Words BKS10Residual
open BlitvicKammounSteingrimsson135289467
open D5.S3.Combinatorics.Permutation.PackingMaximumRefutation

private noncomputable def rankEquiv {n : ℕ} (l : List ℕ) (hl : l.Perm (List.range n)) :
    Equiv.Perm (Fin n) :=
  ((Fin.equivSubtype.trans (Equiv.subtypeEquivRight (fun x =>
    (hl.mem_iff.trans List.mem_range).symm))).trans
    (List.Nodup.getEquiv l (hl.nodup_iff.mpr List.nodup_range)).symm).trans
    (finCongr (by simpa using hl.length_eq))

private theorem rank_word {n : ℕ} (w : Equiv.Perm (Fin n)) :
    rankEquiv (word w) (word_perm w) = w := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  change (word w).idxOf i.val = (w i).val
  exact word_idxOf w i

private theorem word_rank {n : ℕ} (l : List ℕ) (hl : l.Perm (List.range n)) :
    word (rankEquiv l hl) = l := by
  have hlen : l.length = n := by simpa using hl.length_eq
  have hnd : l.Nodup := hl.nodup_iff.mpr List.nodup_range
  apply List.ext_getElem (by simp [word, hlen])
  intro i hi hj
  have hx : l[i] < n := List.mem_range.mp (hl.mem_iff.mp (List.getElem_mem hj))
  have he : rankEquiv l hl ⟨l[i],hx⟩ = ⟨i, by simpa [word] using hi⟩ := by
    apply Fin.ext
    change l.idxOf l[i] = i
    exact hnd.idxOf_getElem i hj
  have hi' : i < n := by simpa [word] using hi
  have hv : (rankEquiv l hl).symm ⟨i,hi'⟩ = ⟨l[i],hx⟩ := by
    exact (rankEquiv l hl).symm_apply_eq.mpr he.symm
  simpa [word] using congrArg Fin.val hv

private def rawWords (j : ℕ) : Set (List ℕ) :=
  {l | l.Perm (List.range (9+(j-1)*6)) ∧ ∀ t, t < j → C t l.idxOf}

private theorem chain_strictMono (t : ℕ) (f : ℕ → ℕ) :
    StrictMono (fun a : Fin 9 => f (6*t+(inversePattern a).val)) ↔ C t f := by
  rw [Fin.strictMono_iff_lt_succ]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [inversePattern] using h 0
    · simpa [inversePattern] using h 1
    · simpa [inversePattern] using h 2
    · simpa [inversePattern] using h 3
    · simpa [inversePattern] using h 4
    · simpa [inversePattern] using h 5
    · simpa [inversePattern] using h 6
    · simpa [inversePattern] using h 7
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ i
    fin_cases i
    · simpa [inversePattern] using h0
    · simpa [inversePattern] using h1
    · simpa [inversePattern] using h2
    · simpa [inversePattern] using h3
    · simpa [inversePattern] using h4
    · simpa [inversePattern] using h5
    · simpa [inversePattern] using h6
    · simpa [inversePattern] using h7

private theorem packing_word_iff (j : ℕ) (w : Equiv.Perm (Fin (9+(j-1)*6))) :
    Packs pattern 3 j w ↔ ∀ t, t < j → C t (word w).idxOf := by
  have hidx (t : Fin j) (a : Fin 9) :
      (word w).idxOf (6*t.val+a.val) = (w (windowIndex 9 3 j t a)).val := by
    simpa [windowIndex,Nat.mul_comm] using word_idxOf w (windowIndex 9 3 j t a)
  rw [packing_chain_iff]
  constructor
  · intro h t ht
    apply (chain_strictMono t (word w).idxOf).mp
    intro a b hab
    have hh := h ⟨t,ht⟩ hab
    change (w (windowIndex 9 3 j ⟨t,ht⟩ (inversePattern a))).val <
      (w (windowIndex 9 3 j ⟨t,ht⟩ (inversePattern b))).val at hh
    simpa only [← hidx ⟨t,ht⟩ (inversePattern a),← hidx ⟨t,ht⟩ (inversePattern b)] using hh
  · intro h t a b hab
    have hm := (chain_strictMono t.val (word w).idxOf).mpr (h t.val t.isLt)
    have hh := hm hab
    change (w (windowIndex 9 3 j t (inversePattern a))).val <
      (w (windowIndex 9 3 j t (inversePattern b))).val
    simpa only [hidx] using hh

private noncomputable def sourceWordEquiv (j : ℕ) : SourcePacking pattern 3 j ≃ rawWords j where
  toFun w := ⟨word w.val,word_perm w.val,(packing_word_iff j w.val).mp w.property⟩
  invFun l := ⟨rankEquiv l.val l.property.1,(packing_word_iff j _).mpr (by
    simpa only [word_rank] using l.property.2)⟩
  left_inv w := Subtype.ext (rank_word w.val)
  right_inv l := Subtype.ext (word_rank l.val l.property.1)

private theorem count_rawWords (j : ℕ) : count pattern 3 j = (rawWords j).ncard :=
  Nat.card_congr (sourceWordEquiv j)

end BKS10Source



namespace BKS10Head
open BKS10Structure BKS10List BKS10Words BKS10Residual BKS10Source

private def firstHead : List ℕ := [0,3,1,6,2,9,7]
private def secondHead : List ℕ := [0,3,1,6,9,2,7]

private theorem prefix_cases (L l : List ℕ)
    (hd : ∀ x ∈ L, x ∉ firstHead)
    (hp : l.Perm (firstHead ++ L)) (hH : Head l.idxOf)
    (hcross : ∀ x ∈ L, l.idxOf 7 < l.idxOf x) :
    (∃ r, l = firstHead ++ r ∧ r.Perm L) ∨
    (∃ r, l = secondHead ++ r ∧ r.Perm L) := by
  rcases hH with ⟨h03,h31,h16,h62,h69,h27,h97⟩
  dsimp only at h03 h31 h16 h62 h69 h27 h97
  change l.Perm (0 :: 3 :: 1 :: 6 :: 2 :: 9 :: 7 :: L) at hp
  have hm1 : ∀ x ∈ l, x ≠ 0 → l.idxOf 0 < l.idxOf x := by
    intro x hx hn
    have hx := hp.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|hx
    · exact (hn rfl).elim
    all_goals first | omega | (have hc := hcross x hx <;> omega)
  obtain ⟨r1,rfl,hp1⟩ := strip_least l _ 0 hp hm1
  have h31_1 : r1.idxOf 3 < r1.idxOf 1 := by simpa [List.idxOf_cons] using h31
  have h16_1 : r1.idxOf 1 < r1.idxOf 6 := by simpa [List.idxOf_cons] using h16
  have h62_1 : r1.idxOf 6 < r1.idxOf 2 := by simpa [List.idxOf_cons] using h62
  have h69_1 : r1.idxOf 6 < r1.idxOf 9 := by simpa [List.idxOf_cons] using h69
  have h27_1 : r1.idxOf 2 < r1.idxOf 7 := by simpa [List.idxOf_cons] using h27
  have h97_1 : r1.idxOf 9 < r1.idxOf 7 := by simpa [List.idxOf_cons] using h97
  have hc1 (x : ℕ) (hx : x ∈ L) : r1.idxOf 7 < r1.idxOf x := by
    have hn : 0 ≠ x := by
      intro he
      subst x
      exact hd 0 hx (by decide)
    simpa [List.idxOf_cons,hn] using hcross x hx
  have hm2 : ∀ x ∈ r1, x ≠ 3 → r1.idxOf 3 < r1.idxOf x := by
    intro x hx hn
    have hx := hp1.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|hx
    · exact (hn rfl).elim
    all_goals try omega
    have hc := hc1 x hx
    omega
  obtain ⟨r2,rfl,hp2⟩ := strip_least r1 _ 3 hp1 hm2
  have h16_1_2 : r2.idxOf 1 < r2.idxOf 6 := by simpa [List.idxOf_cons] using h16_1
  have h62_1_2 : r2.idxOf 6 < r2.idxOf 2 := by simpa [List.idxOf_cons] using h62_1
  have h69_1_2 : r2.idxOf 6 < r2.idxOf 9 := by simpa [List.idxOf_cons] using h69_1
  have h27_1_2 : r2.idxOf 2 < r2.idxOf 7 := by simpa [List.idxOf_cons] using h27_1
  have h97_1_2 : r2.idxOf 9 < r2.idxOf 7 := by simpa [List.idxOf_cons] using h97_1
  have hc2 (x : ℕ) (hx : x ∈ L) : r2.idxOf 7 < r2.idxOf x := by
    have hn : 3 ≠ x := by
      intro he
      subst x
      exact hd 3 hx (by decide)
    simpa [List.idxOf_cons,hn] using hc1 x hx
  have hm3 : ∀ x ∈ r2, x ≠ 1 → r2.idxOf 1 < r2.idxOf x := by
    intro x hx hn
    have hx := hp2.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|hx
    · exact (hn rfl).elim
    all_goals try omega
    have hc := hc2 x hx
    omega
  obtain ⟨r3,rfl,hp3⟩ := strip_least r2 _ 1 hp2 hm3
  have h62_1_2_3 : r3.idxOf 6 < r3.idxOf 2 := by simpa [List.idxOf_cons] using h62_1_2
  have h69_1_2_3 : r3.idxOf 6 < r3.idxOf 9 := by simpa [List.idxOf_cons] using h69_1_2
  have h27_1_2_3 : r3.idxOf 2 < r3.idxOf 7 := by simpa [List.idxOf_cons] using h27_1_2
  have h97_1_2_3 : r3.idxOf 9 < r3.idxOf 7 := by simpa [List.idxOf_cons] using h97_1_2
  have hc3 (x : ℕ) (hx : x ∈ L) : r3.idxOf 7 < r3.idxOf x := by
    have hn : 1 ≠ x := by
      intro he
      subst x
      exact hd 1 hx (by decide)
    simpa [List.idxOf_cons,hn] using hc2 x hx
  have hm4 : ∀ x ∈ r3, x ≠ 6 → r3.idxOf 6 < r3.idxOf x := by
    intro x hx hn
    have hx := hp3.mem_iff.mp hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl|rfl|rfl|rfl|hx
    · exact (hn rfl).elim
    all_goals try omega
    have hc := hc3 x hx
    omega
  obtain ⟨r4,rfl,hp4⟩ := strip_least r3 _ 6 hp3 hm4
  have h27_1_2_3_4 : r4.idxOf 2 < r4.idxOf 7 := by simpa [List.idxOf_cons] using h27_1_2_3
  have h97_1_2_3_4 : r4.idxOf 9 < r4.idxOf 7 := by simpa [List.idxOf_cons] using h97_1_2_3
  have hc4 (x : ℕ) (hx : x ∈ L) : r4.idxOf 7 < r4.idxOf x := by
    have hn : 6 ≠ x := by
      intro he
      subst x
      exact hd 6 hx (by decide)
    simpa [List.idxOf_cons,hn] using hc3 x hx
  have hne : r4.idxOf 2 ≠ r4.idxOf 9 := by
    intro he
    have he' := (List.idxOf_inj (hp4.mem_iff.mpr (by simp : 2 ∈ 2 :: 9 :: 7 :: L))).mp he
    norm_num at he'
  rcases lt_or_gt_of_ne hne with h29 | h92
  · have hm5 : ∀ x ∈ r4, x ≠ 2 → r4.idxOf 2 < r4.idxOf x := by
      intro x hx hn
      have hx := hp4.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|rfl|hx
      · exact (hn rfl).elim
      all_goals try omega
      have hc := hc4 x hx
      omega
    obtain ⟨r5,rfl,hp5⟩ := strip_least r4 _ 2 hp4 hm5
    have h97_1_2_3_4_5 : r5.idxOf 9 < r5.idxOf 7 := by simpa [List.idxOf_cons] using h97_1_2_3_4
    have hc5 (x : ℕ) (hx : x ∈ L) : r5.idxOf 7 < r5.idxOf x := by
      have hn : 2 ≠ x := by
        intro he
        subst x
        exact hd 2 hx (by decide)
      simpa [List.idxOf_cons,hn] using hc4 x hx
    have hm6 : ∀ x ∈ r5, x ≠ 9 → r5.idxOf 9 < r5.idxOf x := by
      intro x hx hn
      have hx := hp5.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · exact (hn rfl).elim
      all_goals try omega
      have hc := hc5 x hx
      omega
    obtain ⟨r6,rfl,hp6⟩ := strip_least r5 _ 9 hp5 hm6
    have hc6 (x : ℕ) (hx : x ∈ L) : r6.idxOf 7 < r6.idxOf x := by
      have hn : 9 ≠ x := by
        intro he
        subst x
        exact hd 9 hx (by decide)
      simpa [List.idxOf_cons,hn] using hc5 x hx
    have hm7 : ∀ x ∈ r6, x ≠ 7 → r6.idxOf 7 < r6.idxOf x := by
      intro x hx hn
      have hx := hp6.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact (hn rfl).elim
      all_goals try omega
      have hc := hc6 x hx
      omega
    obtain ⟨r7,rfl,hp7⟩ := strip_least r6 _ 7 hp6 hm7
    left
    exact ⟨r7,rfl,hp7⟩
  · have hpSwap : r4.Perm (9 :: 2 :: 7 :: L) := hp4.trans (List.Perm.swap 9 2 _)
    have hm8 : ∀ x ∈ r4, x ≠ 9 → r4.idxOf 9 < r4.idxOf x := by
      intro x hx hn
      have hx := hpSwap.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|rfl|hx
      · exact (hn rfl).elim
      all_goals try omega
      have hc := hc4 x hx
      omega
    obtain ⟨r8,rfl,hp8⟩ := strip_least r4 _ 9 hpSwap hm8
    have h27_1_2_3_4_8 : r8.idxOf 2 < r8.idxOf 7 := by simpa [List.idxOf_cons] using h27_1_2_3_4
    have hc8 (x : ℕ) (hx : x ∈ L) : r8.idxOf 7 < r8.idxOf x := by
      have hn : 9 ≠ x := by
        intro he
        subst x
        exact hd 9 hx (by decide)
      simpa [List.idxOf_cons,hn] using hc4 x hx
    have hm9 : ∀ x ∈ r8, x ≠ 2 → r8.idxOf 2 < r8.idxOf x := by
      intro x hx hn
      have hx := hp8.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · exact (hn rfl).elim
      all_goals try omega
      have hc := hc8 x hx
      omega
    obtain ⟨r9,rfl,hp9⟩ := strip_least r8 _ 2 hp8 hm9
    have hc9 (x : ℕ) (hx : x ∈ L) : r9.idxOf 7 < r9.idxOf x := by
      have hn : 2 ≠ x := by
        intro he
        subst x
        exact hd 2 hx (by decide)
      simpa [List.idxOf_cons,hn] using hc8 x hx
    have hm10 : ∀ x ∈ r9, x ≠ 7 → r9.idxOf 7 < r9.idxOf x := by
      intro x hx hn
      have hx := hp9.mem_iff.mp hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact (hn rfl).elim
      all_goals try omega
      have hc := hc9 x hx
      omega
    obtain ⟨r10,rfl,hp10⟩ := strip_least r9 _ 7 hp9 hm10
    right
    exact ⟨r10,rfl,hp10⟩

private theorem head_disjoint (j : ℕ) (hj : 2 ≤ j) :
    ∀ x ∈ labels j, x ∉ firstHead := by
  intro x hx
  have hx := (mem_labels j hj x).mp hx
  simp only [firstHead,List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false]
  unfold QSupport at hx
  omega

private theorem full_labels_perm (j : ℕ) (hj : 2 ≤ j) :
    (List.range (9+(j-1)*6)).Perm (firstHead ++ labels j) := by
  have hdis : List.Disjoint firstHead (labels j) := by
    rw [List.disjoint_left]
    intro x hx hy
    exact head_disjoint j hj x hy hx
  have hnd : (firstHead ++ labels j).Nodup :=
    List.nodup_append'.mpr ⟨by decide,labels_nodup j,hdis⟩
  apply (List.perm_ext_iff_of_nodup List.nodup_range hnd).mpr
  intro x
  simp only [List.mem_range,List.mem_append,mem_labels j hj,firstHead,
    List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false,QSupport]
  omega

private theorem q_prefix_iff (j : ℕ) (hj : 2 ≤ j) (r : List ℕ) (H : List ℕ)
    (hH : ∀ x, QSupport j x → x ∉ H) :
    Q j (H ++ r).idxOf ↔ Q j r.idxOf := by
  apply q_congr j hj
  intro x y hx hy
  simp [List.idxOf_append,hH x hx,hH y hy]

private theorem raw_words_as_heads (j : ℕ) (hj : 2 ≤ j) :
    rawWords j = (List.append firstHead '' words j) ∪ (List.append secondHead '' words j) := by
  have hd := head_disjoint j hj
  have hH1 (x : ℕ) (hx : QSupport j x) : x ∉ firstHead := hd x ((mem_labels j hj x).mpr hx)
  have hH2 (x : ℕ) (hx : QSupport j x) : x ∉ secondHead := by
    have hn := hH1 x hx
    simpa [firstHead,secondHead,or_comm,or_left_comm,or_assoc] using hn
  have hpermH : secondHead.Perm firstHead :=
    (((List.Perm.swap 2 9 [7]).cons 6).cons 1 |>.cons 3).cons 0
  ext l
  constructor
  · rintro ⟨hp,hraw⟩
    have hh := (head_iff j hj l.idxOf).mp hraw
    have hcross (x : ℕ) (hx : x ∈ labels j) : l.idxOf 7 < l.idxOf x :=
      lt_of_lt_of_le hh.2.1 (q_min j hj l.idxOf hh.2.2 x ((mem_labels j hj x).mp hx))
    rcases prefix_cases (labels j) l hd (hp.trans (full_labels_perm j hj)) hh.1 hcross with
      ⟨r,rfl,hr⟩|⟨r,rfl,hr⟩
    · left
      exact ⟨r,⟨hr,(q_prefix_iff j hj r firstHead hH1).mp hh.2.2⟩,rfl⟩
    · right
      exact ⟨r,⟨hr,(q_prefix_iff j hj r secondHead hH2).mp hh.2.2⟩,rfl⟩
  · rintro (⟨r,⟨hr,hq⟩,rfl⟩|⟨r,⟨hr,hq⟩,rfl⟩)
    · refine ⟨(hr.append_left firstHead).trans (full_labels_perm j hj).symm,?_⟩
      apply (head_iff j hj _).mpr
      refine ⟨?_,?_,(q_prefix_iff j hj r firstHead hH1).mpr hq⟩
      · simp [Head,firstHead,List.idxOf_append]
      · simp [firstHead,List.idxOf_append] <;> omega
    · refine ⟨((hpermH.append hr).trans (full_labels_perm j hj).symm),?_⟩
      apply (head_iff j hj _).mpr
      refine ⟨?_,?_,(q_prefix_iff j hj r secondHead hH2).mpr hq⟩
      · simp [Head,secondHead,List.idxOf_append]
      · simp [secondHead,List.idxOf_append] <;> omega

private theorem raw_words_card (j : ℕ) (hj : 2 ≤ j) :
    (rawWords j).ncard = 2 * (words j).ncard := by
  have hdis : Disjoint (List.append firstHead '' words j) (List.append secondHead '' words j) := by
    rw [Set.disjoint_left]
    rintro l ⟨r,hr,he⟩ ⟨s,hs,hf⟩
    have hh := he.trans hf.symm
    simp [firstHead,secondHead] at hh
  have hinj (H : List ℕ) : Function.Injective (List.append H) := by
    intro r s he
    exact (List.append_right_inj H).mp he
  rw [raw_words_as_heads j hj,Set.ncard_union_eq hdis
    ((words_finite j).image _) ((words_finite j).image _),
    Set.ncard_image_of_injective _ (hinj firstHead),
    Set.ncard_image_of_injective _ (hinj secondHead)]
  omega

end BKS10Head




namespace BKS10BaseSymbolic
open BKS10Structure BKS10List BKS10Gluing BKS10Realization BKS10Residual

private theorem triple_eq (r : List ℕ) (hp : r.Perm [14,10,11])
    (h1 : r.idxOf 14 < r.idxOf 10) (h2 : r.idxOf 10 < r.idxOf 11) :
    r = [14,10,11] := by
  have hm : ∀ x ∈ r, x ≠ 14 → r.idxOf 14 < r.idxOf x := by
    intro x hx hn
    have hx := hp.mem_iff.mp hx
    simp only [List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact (hn rfl).elim
    · exact h1
    · omega
  obtain ⟨s,rfl,hs⟩ := strip_least r [10,11] 14 hp hm
  have h2 : s.idxOf 10 < s.idxOf 11 := by simpa [List.idxOf_cons] using h2
  have hm : ∀ x ∈ s, x ≠ 10 → s.idxOf 10 < s.idxOf x := by
    intro x hx hn
    have hx := hs.mem_iff.mp hx
    simp only [List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl
    · exact (hn rfl).elim
    · exact h2
  obtain ⟨t,rfl,ht⟩ := strip_least s [11] 10 hs hm
  rw [List.perm_singleton.mp ht]

private def baseAssembly : Shuffle [13,14,10,11] [4,5] → List ℕ :=
  fun z => 12 :: 8 :: z.val

private theorem baseAssembly_injective : Function.Injective baseAssembly := by
  intro z w h
  apply Subtype.ext
  simpa only [baseAssembly,List.cons.injEq,true_and] using h

private theorem base_words : words 2 = Set.range baseAssembly := by
  have hperm : (labels 2).Perm [12,8,13,4,5,14,10,11] := by decide +kernel
  ext l
  constructor
  · rintro ⟨hp,hq⟩
    have hp := hp.trans hperm
    rcases hq with ⟨⟨h84,h45⟩,⟨h128,h813,h1314,h1410,h1011⟩,ht⟩
    dsimp only at h84 h45 h128 h813 h1314 h1410 h1011
    have hm : ∀ x ∈ l, x ≠ 12 → l.idxOf 12 < l.idxOf x := by
      intro x hx hn
      have hx := hp.mem_iff.mp hx
      simp only [List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact (hn rfl).elim
      all_goals omega
    obtain ⟨s,rfl,hs⟩ := strip_least l [8,13,4,5,14,10,11] 12 hp hm
    have h84 : s.idxOf 8 < s.idxOf 4 := by simpa [List.idxOf_cons] using h84
    have h45 : s.idxOf 4 < s.idxOf 5 := by simpa [List.idxOf_cons] using h45
    have h813 : s.idxOf 8 < s.idxOf 13 := by simpa [List.idxOf_cons] using h813
    have h1314 : s.idxOf 13 < s.idxOf 14 := by simpa [List.idxOf_cons] using h1314
    have h1410 : s.idxOf 14 < s.idxOf 10 := by simpa [List.idxOf_cons] using h1410
    have h1011 : s.idxOf 10 < s.idxOf 11 := by simpa [List.idxOf_cons] using h1011
    have hm : ∀ x ∈ s, x ≠ 8 → s.idxOf 8 < s.idxOf x := by
      intro x hx hn
      have hx := hs.mem_iff.mp hx
      simp only [List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact (hn rfl).elim
      all_goals omega
    obtain ⟨z,rfl,hz⟩ := strip_least s [13,4,5,14,10,11] 8 hs hm
    have h45 : z.idxOf 4 < z.idxOf 5 := by simpa [List.idxOf_cons] using h45
    have h1314 : z.idxOf 13 < z.idxOf 14 := by simpa [List.idxOf_cons] using h1314
    have h1410 : z.idxOf 14 < z.idxOf 10 := by simpa [List.idxOf_cons] using h1410
    have h1011 : z.idxOf 10 < z.idxOf 11 := by simpa [List.idxOf_cons] using h1011
    have hd : List.Disjoint [14,10,11] [12,15,8,13,4,5] := by simp [List.disjoint_left]
    have hc : ∀ x ∈ [14,10,11], z.idxOf 13 < z.idxOf x := by
      intro x hx
      simp only [List.mem_cons,List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl <;> omega
    obtain ⟨r,hr,hperm,hlow,hhigh⟩ := one_tail [14,10,11] z hd hz h45 hc
    have h14 : keep 14 = true := keep_all [14,10,11] hd 14 (by simp)
    have h10 : keep 10 = true := keep_all [14,10,11] hd 10 (by simp)
    have h11 : keep 11 = true := keep_all [14,10,11] hd 11 (by simp)
    have h1 := (idxOf_filter_lt_iff keep z 14 10 h14 h10).mpr h1410
    have h2 := (idxOf_filter_lt_iff keep z 10 11 h10 h11).mpr h1011
    rw [hlow] at h1 h2
    have hre : r = [14,10,11] := triple_eq r hr
      (by simpa [List.idxOf_cons] using h1) (by simpa [List.idxOf_cons] using h2)
    subst r
    exact ⟨⟨z,hperm,hlow,hhigh⟩,rfl⟩
  · rintro ⟨z,rfl⟩
    have hp : (baseAssembly z).Perm (labels 2) := by
      have hperm' : ([13,14,10,11] ++ [4,5]).Perm [13,4,5,14,10,11] :=
        (List.perm_append_comm (l₁ := [14,10,11]) (l₂ := [4,5])).cons 13
      exact ((z.property.1.trans hperm').cons 8 |>.cons 12).trans hperm.symm
    have hlow (a b : ℕ) (ha : keep a = true) (hb : keep b = true)
        (hab : ([13,14,10,11] : List ℕ).idxOf a < ([13,14,10,11] : List ℕ).idxOf b) :
        z.val.idxOf a < z.val.idxOf b := by
      apply (idxOf_filter_lt_iff keep z.val a b ha hb).mp
      simpa only [z.property.2.1] using hab
    have h45 : z.val.idxOf 4 < z.val.idxOf 5 := by
      apply (idxOf_filter_lt_iff (fun x => !(keep x)) z.val 4 5 (by decide) (by decide)).mp
      rw [z.property.2.2]
      decide
    have h1314 := hlow 13 14 (by decide) (by decide) (by decide)
    have h1410 := hlow 14 10 (by decide) (by decide) (by decide)
    have h1011 := hlow 10 11 (by decide) (by decide) (by decide)
    refine ⟨hp,?_,?_,?_⟩
    · change (baseAssembly z).idxOf 8 < (baseAssembly z).idxOf 4 ∧ _
      constructor
      · simp [baseAssembly,List.idxOf_cons]
      · simpa [baseAssembly,List.idxOf_cons] using h45
    · change (baseAssembly z).idxOf 12 < (baseAssembly z).idxOf 8 ∧ _
      refine ⟨by simp [baseAssembly,List.idxOf_cons],?_,?_,?_,?_⟩
      · simp [baseAssembly,List.idxOf_cons]
      · simpa [baseAssembly,List.idxOf_cons] using h1314
      · simpa [baseAssembly,List.idxOf_cons] using h1410
      · simpa [baseAssembly,List.idxOf_cons] using h1011
    · intro t ht htj
      omega

private theorem residual_two : (words 2).ncard = 15 := by
  rw [base_words]
  have hc := Nat.card_congr (Equiv.ofInjective baseAssembly baseAssembly_injective)
  change Nat.card (Shuffle [13,14,10,11] [4,5]) = (Set.range baseAssembly).ncard at hc
  rw [← hc,shuffle_card _ _ (by simp [keep]) (by simp [keep])]
  decide +kernel

private theorem second_count : D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.count
    BlitvicKammounSteingrimsson135289467.pattern 3 2 = 30 := by
  rw [BKS10Source.count_rawWords,BKS10Head.raw_words_card 2 (by decide),residual_two]

end BKS10BaseSymbolic



open D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
open BlitvicKammounSteingrimsson135289467

def claim : Prop :=
  count (![0, 2, 4, 1, 7, 8, 3, 5, 6] : Fin 9 → Fin 9) 3 1 = 1 ∧
  count (![0, 2, 4, 1, 7, 8, 3, 5, 6] : Fin 9 → Fin 9) 3 2 = 30 ∧
  ∀ (j : ℕ), 3 ≤ j →
    count (![0, 2, 4, 1, 7, 8, 3, 5, 6] : Fin 9 → Fin 9) 3 j =
      (121 * Nat.choose (j - 3) 0 + 168 * Nat.choose (j - 3) 1 +
        72 * Nat.choose (j - 3) 2) *
      count (![0, 2, 4, 1, 7, 8, 3, 5, 6] : Fin 9 → Fin 9) 3 (j - 1)

theorem result : claim := by
  refine ⟨first_count,BKS10BaseSymbolic.second_count,?_⟩
  intro j hj
  change count pattern 3 j =
    (121 * Nat.choose (j-3) 0 + 168 * Nat.choose (j-3) 1 + 72 * Nat.choose (j-3) 2) *
      count pattern 3 (j-1)
  rw [BKS10Source.count_rawWords j,BKS10Source.count_rawWords (j-1),
    BKS10Head.raw_words_card j (by omega),BKS10Head.raw_words_card (j-1) (by omega),
    BKS10Gluing.binomial_factor j hj]
  have hr := BKS10Residual.residual_recurrence (j-1) (by omega)
  rw [show j-1+1 = j by omega,show 6*(j-1)-1 = 6*j-7 by omega] at hr
  rw [hr]
  ring



end D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson135289467Product
