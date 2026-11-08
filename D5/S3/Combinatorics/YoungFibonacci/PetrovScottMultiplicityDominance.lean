/- GID: D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fibonacci multiplicity support has equal hike and prefix dominance. -/

/-
admission_basis: open-problem-resolution (#22953; Proved)
Direct frozen dependencies: D5/S1/Words/UnaryGapWords.gap
statement_id: sha256:eb97511a3e585f1d47a8f21e1cbd7fc6d00a9b02403101318e2a8a69a79d90d9
used by endWord and, through it, endWord_count_mono, fib_reverse,
split_dominates, support_dominates, result; all other declarations: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25184
The public definitions and claim retain the expressions of #22953; the binary
letter predicate used by the proofs is inlined rather than given a second name.
The printed odd-length splitB bound is retained. This result concerns the
fixed-weight matrix; it does not verify the corrected matrix or Figure 8.
The proof compares reversed-prefix counts under enlargement of trailing runs,
then uses equal weight and hike to transfer the comparison to forward prefixes.
Utility none: all weights and list lengths are unbounded; no finite screen is
used in the proof.
Declaration classification (same-delivery helpers expanded):
matrix_support: proof_shape: bind-only; escape_witness: none; consumers: support_hike, support_dominates.
fib_hike: proof_shape: bind-only; escape_witness: none; consumers: split_hike.
split_length: proof_shape: bind-only; escape_witness: none; consumers: split_hike, split_dominates.
split_hike: proof_shape: bind-only; escape_witness: none; consumers: support_hike, split_dominates.
support_hike: proof_shape: bind-only; escape_witness: none; consumers: support_length, result.
yf_sum_formula: proof_shape: bind-only; escape_witness: none; consumers: support_length, dominates_of_reverse_counts, split_dominates.
support_length: proof_shape: bind-only; escape_witness: none; consumers: support_no_reverse_lex.
dominates_no_reverse_lex: proof_shape: content; escape_witness: dominates_no_reverse_lex; consumers: support_no_reverse_lex.
support_no_reverse_lex: proof_shape: content; escape_witness: dominates_no_reverse_lex; consumers: result.
count_take_ones: proof_shape: bind-only; escape_witness: none; consumers: endWord_count_mono.
endWord_count_mono: proof_shape: content; escape_witness: endWord_count_mono; consumers: split_dominates.
fib_reverse: proof_shape: bind-only; escape_witness: none; consumers: split_dominates.
count_decomp: proof_shape: bind-only; escape_witness: none; consumers: dominates_of_reverse_counts.
dominates_of_reverse_counts: proof_shape: bind-only; escape_witness: none; consumers: split_dominates.
tailRuns_mono: proof_shape: bind-only; escape_witness: none; consumers: split_dominates.
split_trailing: proof_shape: bind-only; escape_witness: none; consumers: split_dominates.
split_dominates: proof_shape: content; escape_witness: endWord_count_mono; consumers: support_dominates.
support_dominates: proof_shape: content; escape_witness: endWord_count_mono; consumers: result.
result: proof_shape: content; escape_witness: endWord_count_mono; consumers: none.
-/

import D5.S1.Words.UnaryGapWords
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Order.Partition.Finpartition

set_option autoImplicit false

namespace D5.S3.Combinatorics.YoungFibonacci.PetrovScottMultiplicityDominance

noncomputable section
open scoped Classical

/-- The source's words of weight n, using its existing List Nat carrier. -/
def YF (n : ℕ) (w : List ℕ) : Prop :=
  (∀ a : ℕ, a ∈ w → a = 1 ∨ a = 2) ∧ w.sum = n

/-- The source's total hike. -/
def hike (w : List ℕ) : ℕ := w.count 2

/-- Inverse of the ribbon-row composition on its stated domain.
The one-row ribbon is the all-ones word; interior rows contribute a-2 ones. -/
def Fib (c : List ℕ) : List ℕ :=
  if c.length ≤ 1 then List.replicate (c.headD 0) 1
  else List.replicate (c.headD 0 - 1) 1 ++
    (List.range (c.length - 1)).flatMap (fun j =>
      [2] ++ List.replicate (c[j+1]! - (if j+2 = c.length then 1 else 2)) 1)

/-- Definition 8.12, A, with one-based source coordinates shifted in the list. -/
def splitA (k : List ℕ) : List ℕ :=
  let m := k.length
  let p := m / 2
  if m ≤ 2 then k
  else if m = 3 then [k[0]!, k[1]! + k[2]!]
  else [k[0]!] ++
    (List.range (p-1)).map (fun j => k[2*j+1]! + k[2*j+2]!) ++
    [if m % 2 = 0 then k[2*p-1]! else k[2*p-1]! + k[2*p]!]

/-- Definition 8.12, B, literally: the sum has exactly p odd-indexed parts.
For positive parts, (1+sum)-p equals the printed integer expression 1-p+sum. -/
def splitB (k : List ℕ) : List ℕ :=
  let m := k.length
  let p := m / 2
  if m ≤ 2 then k
  else if m = 3 then [k[0]! + k[2]!, k[1]!]
  else [1 + ((List.range p).map (fun j => k[2*j]!)).sum - p] ++
    (List.range (p-1)).map (fun j => 1 + k[2*j+1]!) ++ [k[2*p-1]!]

/-- Consecutive elements of a block, hence an arc in the source drawing. -/
def Arc {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n)))
    (a b : Fin n) : Prop :=
  a < b ∧ ∃ block ∈ pi.parts, a ∈ block ∧ b ∈ block ∧
    ∀ c ∈ block, ¬ (a < c ∧ c < b)

/-- Source noncrossing: no pair of arcs with interleaved endpoints. -/
def IsNoncrossing {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n))) : Prop :=
  ∀ a b c d : Fin n, Arc pi a b → Arc pi c d → ¬ (a < c ∧ c < b ∧ b < d)

/-- Active arcs immediately before i, represented by their left endpoints. -/
def Gamma {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n)))
    (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun a => ∃ b : Fin n, Arc pi a b ∧ a < i ∧ i ≤ b)

/-- Position, starting at one, of i's predecessor in the increasing active set.
The value is zero when i has no predecessor; g uses only non-first elements. -/
def gamma {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n)))
    (i : Fin n) : ℕ :=
  ((Gamma pi i).filter (fun a => ∃ b : Fin n, Arc pi b i ∧ a ≤ b)).card

/-- Equation (8.1), ell_k. -/
def ell {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n))) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => (Gamma pi i).card = k)).card

/-- Equation (8.1), g_k: closers or transients whose predecessor has rank k. -/
def g {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n))) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n =>
    (∃ a : Fin n, Arc pi a i) ∧ gamma pi i = k)).card

/-- Maximum occupied level; n>=1 in the claim. -/
def peak {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n))) : ℕ :=
  Finset.univ.sup (fun i : Fin n => (Gamma pi i).card)

/-- Definition 8.16, with precisely the optional final zero deleted. -/
def z {n : ℕ} (pi : Finpartition (Finset.univ : Finset (Fin n))) : List ℕ :=
  let p := peak pi
  let zs := ell pi 0 :: (List.range p).flatMap (fun j =>
    [g pi (j+1), ell pi (j+1) - g pi (j+1)])
  if ell pi p = g pi p then zs.dropLast else zs

/-- Corollary 8.20: count the noncrossing partitions with composition k. -/
def multiplicity (n : ℕ) (k : List ℕ) : ℕ :=
  (Finset.univ.filter (fun pi : Finpartition (Finset.univ : Finset (Fin n)) =>
    IsNoncrossing pi ∧ z pi = k)).card

/-- Definition 8.21: the unique matching composition, or zero.
Both indices in claim have weight n. No weight completion is made in splitB. -/
def matrixEntry (n : ℕ) (u v : List ℕ) : ℕ :=
  if h : ∃ k : Composition n, u = Fib (splitA k.blocks) ∧ v = Fib (splitB k.blocks)
  then multiplicity n (Classical.choose h).blocks
  else 0

/-- The cited dominance order, including every common nonempty prefix. -/
def Dominates (u v : List ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ min u.length v.length → (v.take k).sum ≤ (u.take k).sum

/-- Conjecture 8.22, both sentences. The first conjunct is upper triangularity
in the descending lexicographic ordering displayed in Figure 8. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ u : List ℕ, ∀ v : List ℕ, YF n u → YF n v →
    (List.Lex (fun a b : ℕ => b < a) v u → matrixEntry n u v = 0) ∧
    (matrixEntry n u v ≠ 0 → Dominates u v ∧ hike u = hike v)

private theorem matrix_support {n : ℕ} {u v : List ℕ}
    (h : matrixEntry n u v ≠ 0) :
    ∃ k : Composition n, u = Fib (splitA k.blocks) ∧ v = Fib (splitB k.blocks) ∧
      multiplicity n k.blocks ≠ 0 := by
  unfold matrixEntry at h
  by_cases hex : ∃ k : Composition n, u = Fib (splitA k.blocks) ∧ v = Fib (splitB k.blocks)
  · have hs := Classical.choose_spec hex
    rcases hs with ⟨hu, hv⟩
    exact ⟨Classical.choose hex, hu, hv, by simpa only [dif_pos hex] using h⟩
  · simp [hex] at h

private theorem fib_hike (c : List ℕ) : hike (Fib c) = c.length - 1 := by
  have sum_map_one : ∀ (l : List ℕ), (l.map (fun _ => 1)).sum = l.length := by
    intro l
    simp
  by_cases h : c.length ≤ 1
  · simp [hike, Fib, h, List.count_replicate]
  · simp only [hike, Fib, h, ↓reduceIte, List.count_append, List.count_flatMap,
      Function.comp_apply]
    have hmap : List.map (List.count 2 ∘ fun j =>
        [2] ++ List.replicate (c[j + 1]! - (if j + 2 = c.length then 1 else 2)) 1)
        (List.range (c.length - 1)) = List.map (fun _ => 1) (List.range (c.length - 1)) := by
      apply List.map_congr_left
      intro j hj
      simp [Function.comp_def, List.count_replicate]
    rw [hmap, sum_map_one]
    simp [List.count_replicate, List.length_range]

private theorem split_length (k : List ℕ) : (splitA k).length = (splitB k).length := by
  by_cases hle : k.length ≤ 2
  · simp [splitA, splitB, hle]
  · by_cases h3 : k.length = 3
    · simp [splitA, splitB, hle, h3]
    · simp [splitA, splitB, hle, h3]

private theorem split_hike (k : List ℕ) :
    hike (Fib (splitA k)) = hike (Fib (splitB k)) := by
  rw [fib_hike, fib_hike, split_length]

private theorem support_hike {n : ℕ} {u v : List ℕ}
    (hmat : matrixEntry n u v ≠ 0) : hike u = hike v := by
  rcases matrix_support hmat with ⟨k, hu, hv, _⟩
  rw [hu, hv, split_hike]

private theorem yf_sum_formula {n : ℕ} {w : List ℕ} (hw : YF n w) :
    w.sum = w.length + hike w := by
  induction w generalizing n with
  | nil => simp [hike]
  | cons a t ih =>
      have ha := hw.1 a (by simp)
      have ht : YF (n - a) t := by
        refine ⟨?_, ?_⟩
        · exact List.forall_mem_of_forall_mem_cons hw.1
        · have hsum := hw.2
          simp only [List.sum_cons] at hsum
          omega
      rw [List.sum_cons, List.length_cons, ih ht]
      rcases ha with rfl | rfl <;> simp [hike] <;> omega

private theorem support_length {n : ℕ} {u v : List ℕ}
    (hu : YF n u) (hv : YF n v) (hmat : matrixEntry n u v ≠ 0) :
    u.length = v.length := by
  have hhk := support_hike hmat
  have su := yf_sum_formula hu
  have sv := yf_sum_formula hv
  have sun := hu.2
  have svn := hv.2
  rw [su] at sun
  rw [sv] at svn
  omega

private theorem dominates_no_reverse_lex {u v : List ℕ}
    (hu : ∀ a, a ∈ u → a = 1 ∨ a = 2)
    (hv : ∀ a, a ∈ v → a = 1 ∨ a = 2) (hlen : u.length = v.length)
    (hdom : Dominates u v) :
    ¬ List.Lex (fun a b : ℕ => b < a) v u := by
  intro hlex
  induction u generalizing v with
  | nil =>
      cases hlex
  | cons a us ih =>
      cases v with
      | nil =>
          cases hlex
          simp at hlen
      | cons b vs =>
          cases hlex with
          | rel hrel =>
              have ha := hu a (by simp)
              have hb := hv b (by simp)
              have hone := hdom 1 (by omega) (by simp)
              simp at hone
              rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
          | cons htail =>
              have hlen' : us.length = vs.length := by exact Nat.add_right_cancel hlen
              have hus : ∀ a, a ∈ us → a = 1 ∨ a = 2 := by
                exact List.forall_mem_of_forall_mem_cons hu
              have hvs : ∀ a, a ∈ vs → a = 1 ∨ a = 2 := by
                exact List.forall_mem_of_forall_mem_cons hv
              have hdom' : Dominates us vs := by
                intro k hk hkl
                have hfull := hdom (k + 1) (by omega)
                  (by simpa using hkl)
                simpa [List.take] using hfull
              exact ih hus hvs hlen' hdom' htail

private theorem support_no_reverse_lex {n : ℕ} {u v : List ℕ}
    (hu : YF n u) (hv : YF n v) (hmat : matrixEntry n u v ≠ 0)
    (hdom : Dominates u v) :
    ¬ List.Lex (fun a b : ℕ => b < a) v u := by
  apply dominates_no_reverse_lex
  · exact hu.1
  · exact hv.1
  · exact support_length hu hv hmat
  · exact hdom

private def endWord (rs : List ℕ) (a : ℕ) : List ℕ :=
  D5.S1.Words.UnaryGapWords.gap 1 (List.replicate rs.length 2) (rs ++ [a])

private theorem count_take_ones (r k : ℕ) (w : List ℕ) :
    ((List.replicate r 1 ++ 2 :: w).take k).count 2 =
      if k ≤ r then 0 else 1 + (w.take (k - r - 1)).count 2 := by
  by_cases h : k ≤ r
  · simp [List.take_append, List.take_replicate, h, Nat.sub_eq_zero_of_le h, List.count_replicate]
  · have hp : 0 < k - r := by omega
    simp [List.take_append, List.take_replicate, h, List.take_cons hp,
      List.count_replicate, Nat.add_comm]

private theorem endWord_count_mono {rs ss : List ℕ}
    (h : List.Forall₂ (fun r s : ℕ => s ≤ r) rs ss) (a b k : ℕ) :
    ((endWord rs a).take k).count 2 ≤ ((endWord ss b).take k).count 2 := by
  induction h generalizing k with
  | nil => simp [endWord, D5.S1.Words.UnaryGapWords.gap,
      List.take_replicate, List.count_replicate]
  | @cons r s rs ss hrs htail ih =>
      simp only [endWord, List.length_cons, List.replicate_succ, List.cons_append,
        D5.S1.Words.UnaryGapWords.gap, List.headD_cons, List.tail_cons] at *
      rw [count_take_ones, count_take_ones]
      by_cases hr : k ≤ r
      · simp [hr]
      · have hs : ¬ k ≤ s := by omega
        simp only [hr, hs, ↓reduceIte]
        apply Nat.add_le_add_left
        exact (ih (k - r - 1)).trans
          ((List.take_sublist_take_left (by omega : k - r - 1 ≤ k - s - 1)).count_le 2)

private def tailRuns (c : List ℕ) : List ℕ :=
  (List.range (c.length - 1)).map (fun j =>
    c[j+1]! - (if j+2 = c.length then 1 else 2))

private theorem fib_reverse (c : List ℕ) (hc : 2 ≤ c.length) :
    (Fib c).reverse = endWord (tailRuns c).reverse (c.headD 0 - 1) := by
  have hgap (rs : List ℕ) (a : ℕ) :
      D5.S1.Words.UnaryGapWords.gap 1 (List.replicate rs.length 2) (rs ++ [a]) =
        rs.flatMap (fun r => List.replicate r 1 ++ [2]) ++ List.replicate a 1 := by
    induction rs with
    | nil => simp [D5.S1.Words.UnaryGapWords.gap]
    | cons r rs ih =>
        simpa [List.length_cons, List.replicate_succ, D5.S1.Words.UnaryGapWords.gap,
          List.flatMap_cons, List.append_assoc] using ih
  have h : ¬ c.length ≤ 1 := by exact Nat.not_le_of_lt hc
  simp only [Fib, h, ↓reduceIte, List.reverse_append, List.reverse_replicate,
    List.reverse_flatMap, endWord, hgap, tailRuns, ← List.map_reverse, List.flatMap_map,
    Function.comp_def, List.reverse_append, List.reverse_singleton]

private theorem count_decomp (w : List ℕ) (k : ℕ) :
    (w.take k).count 2 + (w.drop k).count 2 = w.count 2 := by
  rw [← List.count_append, List.take_append_drop]

private theorem dominates_of_reverse_counts {n : ℕ} {u v : List ℕ}
    (hu : YF n u) (hv : YF n v) (hlen : u.length = v.length)
    (hhike : hike u = hike v)
    (hc : ∀ k, (u.reverse.take k).count 2 ≤ (v.reverse.take k).count 2) :
    Dominates u v := by
  intro k hk hkl
  have hku : k ≤ u.length := le_trans hkl (min_le_left _ _)
  have hkv : k ≤ v.length := le_trans hkl (min_le_right _ _)
  have hd := hc (u.length - k)
  simp only [List.take_reverse, List.count_reverse] at hd
  have he : u.length - (u.length - k) = k := by exact Nat.sub_sub_self hku
  have he' : v.length - (u.length - k) = k := by omega
  rw [he, he'] at hd
  have hdu := count_decomp u k
  have hdv := count_decomp v k
  have hct : (v.take k).count 2 ≤ (u.take k).count 2 := by
    unfold hike at hhike
    omega
  have htu : YF (u.take k).sum (u.take k) :=
    ⟨fun a ha => hu.1 a (List.mem_of_mem_take ha), rfl⟩
  have htv : YF (v.take k).sum (v.take k) :=
    ⟨fun a ha => hv.1 a (List.mem_of_mem_take ha), rfl⟩
  have su := yf_sum_formula htu
  have sv := yf_sum_formula htv
  simp only [List.length_take, Nat.min_eq_left hku, Nat.min_eq_left hkv, hike] at su sv
  omega

private theorem tailRuns_mono {c d : List ℕ} (hlen : c.length = d.length)
    (hcoord : ∀ i, 1 ≤ i → i < c.length → d[i]! ≤ c[i]!) :
    List.Forall₂ (fun r s : ℕ => s ≤ r) (tailRuns c) (tailRuns d) := by
  unfold tailRuns
  rw [← hlen]
  apply List.forall₂_of_length_eq_of_get
  · simp
  · intro i hi hj
    have hib : i < c.length - 1 := by simpa using hi
    have hc := hcoord (i+1) (by omega) (by omega)
    simpa using Nat.sub_le_sub_right hc (if i+2 = c.length then 1 else 2)

private theorem split_trailing (k : List ℕ)
    (hpos : ∀ i, i < k.length → 1 ≤ k[i]!) :
    ∀ i, 1 ≤ i → i < (splitA k).length → (splitB k)[i]! ≤ (splitA k)[i]! := by
  intro i hi hib
  by_cases hle : k.length ≤ 2
  · simp [splitA, splitB, hle]
  · by_cases h3 : k.length = 3
    · have hie : i = 1 := by
        simp [splitA, hle, h3] at hib
        omega
      subst i
      simp [splitA, splitB, hle, h3]
    · have hp : 2 ≤ k.length / 2 := by omega
      have him : i ≤ k.length / 2 := by
        simp [splitA, hle, h3] at hib
        omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      by_cases hj : j < k.length / 2 - 1
      · have hposj : 1 ≤ k[2*j+2]! := hpos _ (by omega)
        have hsum : 1 + k[2*j+1]! ≤ k[2*j+1]! + k[2*j+2]! := by omega
        simpa [splitA, splitB, hle, h3, List.cons_append,
          List.getElem?_append, hj] using hsum
      · have hje : j = k.length / 2 - 1 := by omega
        subst j
        simp [splitA, splitB, hle, h3, List.cons_append, List.getElem?_append]
        split_ifs <;> omega

private theorem split_dominates {n : ℕ} (k : Composition n)
    (hu : YF n (Fib (splitA k.blocks))) (hv : YF n (Fib (splitB k.blocks))) :
    Dominates (Fib (splitA k.blocks)) (Fib (splitB k.blocks)) := by
  by_cases hsmall : k.blocks.length ≤ 2
  · simp only [splitA, splitB, hsmall, ↓reduceIte]
    intro q hq hql
    exact le_rfl
  · have ha : 2 ≤ (splitA k.blocks).length := by
      by_cases h3 : k.blocks.length = 3
      · simp [splitA, hsmall, h3]
      · simp [splitA, hsmall, h3]
    have hb : 2 ≤ (splitB k.blocks).length := by rw [← split_length]; exact ha
    have hlen : (Fib (splitA k.blocks)).length = (Fib (splitB k.blocks)).length := by
      have su := yf_sum_formula hu
      have sv := yf_sum_formula hv
      have ht := split_hike k.blocks
      have snu := hu.2
      have snv := hv.2
      omega
    apply dominates_of_reverse_counts hu hv hlen (split_hike k.blocks)
    intro q
    rw [fib_reverse _ ha, fib_reverse _ hb]
    apply endWord_count_mono
    apply List.forall₂_reverse_iff.mpr
    apply tailRuns_mono (split_length k.blocks)
    apply split_trailing
    intro i hi
    have hp := k.blocks_pos (List.getElem_mem hi)
    simpa only [getElem!_pos k.blocks i hi] using (Nat.succ_le_of_lt hp)

private theorem support_dominates {n : ℕ} {u v : List ℕ}
    (hu : YF n u) (hv : YF n v) (hmat : matrixEntry n u v ≠ 0) :
    Dominates u v := by
  rcases matrix_support hmat with ⟨k, rfl, rfl, _⟩
  exact split_dominates k hu hv

theorem result : claim := by
  intro n hn u v hu hv
  constructor
  · intro hlex
    by_contra hnon
    exact support_no_reverse_lex hu hv hnon (support_dominates hu hv hnon) hlex
  · intro hnon
    exact ⟨support_dominates hu hv hnon, support_hike hnon⟩

end
end D5.S3.Combinatorics.YoungFibonacci.PetrovScottMultiplicityDominance
