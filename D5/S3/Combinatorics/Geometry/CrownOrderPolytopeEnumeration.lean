/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Composition, mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph, mathlib/module/Mathlib.Data.Fintype.Powerset]
   utility: none
   digest: Fixed-length parity compositions are counted, and endpoint-free crown blocks are connected cycle subgraphs. -/

/- Library search (2026-09-19): the pinned Mathlib Composition API supplies positive
   list compositions, blocksFun, and the unrestricted composition equivalence, but no
   fixed-length prescribed-parity count. Repository search found no crown-partition or
   prescribed-parity composition enumeration. The construction below is the reversible
   evenization in Lemma 3.5 of arXiv:2504.05123v3, before cyclic cut multiplicity. -/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeCCP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open scoped BigOperators

/-- A positive ordered composition with its number of blocks fixed in the type. -/
structure IndexedComposition (total length : ℕ) where
  blocks : List ℕ
  blocks_length : blocks.length = length
  blocks_pos : ∀ {a}, a ∈ blocks → 0 < a
  blocks_sum : blocks.sum = total
  deriving DecidableEq

namespace IndexedComposition

/-- The block at a fixed-length index. -/
def block {total length : ℕ} (c : IndexedComposition total length) (j : Fin length) : ℕ :=
  c.blocks.get (Fin.cast c.blocks_length.symm j)

/-- Fixed-length compositions in the source model are exactly fixed-length Mathlib
compositions. This is the bridge used by the later path-partition enumeration. -/
def compositionEquiv (total length : ℕ) :
    IndexedComposition total length ≃ {c : Composition total // c.length = length} where
  toFun c := ⟨
    { blocks := c.blocks
      blocks_pos := c.blocks_pos
      blocks_sum := c.blocks_sum },
    c.blocks_length⟩
  invFun c :=
    { blocks := c.1.blocks
      blocks_length := c.2
      blocks_pos := c.1.blocks_pos
      blocks_sum := c.1.blocks_sum }
  left_inv c := by rfl
  right_inv c := by cases c; rfl

private noncomputable instance fintype (total length : ℕ) :
    Fintype (IndexedComposition total length) :=
  Fintype.ofEquiv {c : Composition total // c.length = length}
    (compositionEquiv total length).symm

end IndexedComposition

/-- Positions of the odd blocks of a fixed-length composition. -/
def oddSupport {total length : ℕ} (c : IndexedComposition total length) : Finset (Fin length) :=
  Finset.univ.filter fun j => Odd (c.block j)

/-- Positive compositions with a prescribed number of odd blocks. -/
abbrev PrescribedOddComposition (total length oddCount : ℕ) :=
  {c : IndexedComposition total length // (oddSupport c).card = oddCount}

/-- Finsets of positions having a prescribed cardinality. -/
abbrev PositionSet (length count : ℕ) :=
  {S : Finset (Fin length) // S.card = count}

private def evenizedBlock {total length : ℕ} (c : IndexedComposition total length)
    (j : Fin length) : ℕ :=
  if Odd (c.block j) then c.block j / 2 + 1 else c.block j / 2

private def evenize {n i m : ℕ} (c : PrescribedOddComposition (2 * n) i (2 * m)) :
    IndexedComposition (n + m) i := by
  have sum_block {total length : ℕ} (c : IndexedComposition total length) :
      ∑ j, c.block j = total := by
    have hlist : List.ofFn c.block = c.blocks := by
      apply List.ext_get
      · simp [c.blocks_length]
      · intro j hj₁ hj₂
        simp [IndexedComposition.block]
    calc
      ∑ j, c.block j = (List.ofFn c.block).sum := List.sum_ofFn.symm
      _ = c.blocks.sum := congrArg List.sum hlist
      _ = total := c.blocks_sum
  have two_mul_evenizedBlock {total length : ℕ}
      (c : IndexedComposition total length) (j : Fin length) :
      2 * evenizedBlock c j = c.block j + if Odd (c.block j) then 1 else 0 := by
    unfold evenizedBlock
    split_ifs with h
    · have hhalf := Nat.two_mul_div_two_add_one_of_odd h
      rw [mul_add]
      omega
    · have heven : Even (c.block j) := Nat.not_odd_iff_even.mp h
      rw [Nat.two_mul_div_two_of_even heven]
      omega
  have block_pos {total length : ℕ} (c : IndexedComposition total length)
      (j : Fin length) : 0 < c.block j := by
    exact c.blocks_pos (List.get_mem _ _)
  have evenizedBlock_pos {total length : ℕ}
      (c : IndexedComposition total length) (j : Fin length) :
      0 < evenizedBlock c j := by
    unfold evenizedBlock
    split_ifs with h
    · omega
    · have heven : Even (c.block j) := Nat.not_odd_iff_even.mp h
      obtain ⟨a, ha⟩ := heven
      have := block_pos c j
      omega
  exact {
    blocks := List.ofFn (evenizedBlock c.1)
    blocks_length := List.length_ofFn
    blocks_pos := by
      intro a ha
      rw [List.mem_ofFn] at ha
      obtain ⟨j, rfl⟩ := ha
      exact evenizedBlock_pos c.1 j
    blocks_sum := by
      have hpoint :
          2 * ∑ j, evenizedBlock c.1 j =
            ∑ j, (c.1.block j + if Odd (c.1.block j) then 1 else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => two_mul_evenizedBlock c.1 j
      have hindicator :
          (∑ j, if Odd (c.1.block j) then 1 else 0) = 2 * m := by
        rw [← Finset.card_filter]
        exact c.2
      have hsum := (sum_block c.1)
      simp only [Finset.sum_add_distrib] at hpoint
      rw [hsum, hindicator] at hpoint
      rw [List.sum_ofFn]
      omega }
private def decodeBlock {n i m : ℕ} (S : Finset (Fin i)) (c : IndexedComposition (n + m) i)
    (j : Fin i) : ℕ :=
  if j ∈ S then 2 * c.block j - 1 else 2 * c.block j

private def decodedComposition {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
    IndexedComposition (2 * n) i := by
  have sum_block {total length : ℕ} (c : IndexedComposition total length) :
      ∑ j, c.block j = total := by
    have hlist : List.ofFn c.block = c.blocks := by
      apply List.ext_get
      · simp [c.blocks_length]
      · intro j hj₁ hj₂
        simp [IndexedComposition.block]
    calc
      ∑ j, c.block j = (List.ofFn c.block).sum := List.sum_ofFn.symm
      _ = c.blocks.sum := congrArg List.sum hlist
      _ = total := c.blocks_sum
  have block_pos {total length : ℕ} (c : IndexedComposition total length)
      (j : Fin length) : 0 < c.block j := by
    exact c.blocks_pos (List.get_mem _ _)
  have decodeBlock_pos {n i m : ℕ} (S : Finset (Fin i))
      (c : IndexedComposition (n + m) i) (j : Fin i) :
      0 < decodeBlock S c j := by
    unfold decodeBlock
    split_ifs <;> have := block_pos c j <;> omega
  have decodeBlock_add_indicator {n i m : ℕ} (S : Finset (Fin i))
      (c : IndexedComposition (n + m) i) (j : Fin i) :
      decodeBlock S c j + (if j ∈ S then 1 else 0) = 2 * c.block j := by
    unfold decodeBlock
    split_ifs <;> have := block_pos c j <;> omega
  let S := data.1.1
  let c := data.2
  exact
    { blocks := List.ofFn (decodeBlock S c)
      blocks_length := List.length_ofFn
      blocks_pos := by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨j, rfl⟩ := ha
        exact decodeBlock_pos S c j
      blocks_sum := by
        have hpoint :
            (∑ j, decodeBlock S c j) + (∑ j, if j ∈ S then 1 else 0) =
              ∑ j, 2 * c.block j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => decodeBlock_add_indicator S c j
        have hindicator : (∑ j, if j ∈ S then 1 else 0) = 2 * m := by
          simpa [S] using data.1.2
        have hright : (∑ j, 2 * c.block j) = 2 * (n + m) := by
          rw [← Finset.mul_sum, (sum_block c)]
        rw [hindicator, hright] at hpoint
        rw [List.sum_ofFn]
        omega }
private def decode {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
    PrescribedOddComposition (2 * n) i (2 * m) := by
  have block_pos {total length : ℕ} (c : IndexedComposition total length)
      (j : Fin length) : 0 < c.block j := by
    exact c.blocks_pos (List.get_mem _ _)
  have odd_decodeBlock_iff {n i m : ℕ} (S : Finset (Fin i))
      (c : IndexedComposition (n + m) i) (j : Fin i) :
      Odd (decodeBlock S c j) ↔ j ∈ S := by
    unfold decodeBlock
    split_ifs with h
    · refine ⟨fun _ => h, fun _ => ?_⟩
      have hpos := block_pos c j
      refine ⟨c.block j - 1, ?_⟩
      omega
    · refine ⟨?_, fun hj => (h hj).elim⟩
      rintro ⟨a, ha⟩
      omega
  have block_decodedComposition {n i m : ℕ}
      (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) (j : Fin i) :
      (decodedComposition data).block j = decodeBlock data.1.1 data.2 j := by
    unfold IndexedComposition.block
    have hindex : Fin.cast (decodedComposition data).blocks_length.symm j =
        ⟨j, by simp [decodedComposition]⟩ := Fin.ext rfl
    rw [hindex]
    exact List.get_ofFn _ _
  refine ⟨decodedComposition data, ?_⟩
  calc
    (oddSupport (decodedComposition data)).card = data.1.1.card := by
      apply congrArg Finset.card
      ext j
      simp only [oddSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [block_decodedComposition]
      exact odd_decodeBlock_iff _ _ _
    _ = 2 * m := data.1.2
/-- Lemma 3.5's parity step: a positive composition of `2n` into `i` blocks
with exactly `2m` odd blocks is equivalent to choosing those `2m` positions
and a positive composition of `n+m` into `i` blocks. The forward map adds one
to each odd block and halves; the inverse doubles and subtracts one exactly at
the recorded positions. -/
def parityEvenizationEquiv (n i m : ℕ) :
    PrescribedOddComposition (2 * n) i (2 * m) ≃
      PositionSet i (2 * m) × IndexedComposition (n + m) i := by
  have ic_ext {total length : ℕ} {c d : IndexedComposition total length}
      (h : c.blocks = d.blocks) : c = d := by
    cases c
    cases d
    cases h
    rfl
  have ic_ext_block {total length : ℕ} {c d : IndexedComposition total length}
      (h : ∀ j, c.block j = d.block j) : c = d := by
    apply ic_ext
    apply List.ext_get
    · exact c.blocks_length.trans d.blocks_length.symm
    · intro j hjc hjd
      have hblock := h (Fin.cast c.blocks_length ⟨j, hjc⟩)
      simpa [IndexedComposition.block] using hblock
  have block_decodedComposition {n i m : ℕ}
      (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) (j : Fin i) :
      (decodedComposition data).block j = decodeBlock data.1.1 data.2 j := by
    unfold IndexedComposition.block
    have hindex : Fin.cast (decodedComposition data).blocks_length.symm j =
        ⟨j, by simp [decodedComposition]⟩ := Fin.ext rfl
    rw [hindex]
    exact List.get_ofFn _ _
  have block_decode {n i m : ℕ}
      (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) (j : Fin i) :
      (decode data).1.block j = decodeBlock data.1.1 data.2 j := by
    exact block_decodedComposition data j
  have block_evenize {n i m : ℕ}
      (c : PrescribedOddComposition (2 * n) i (2 * m)) (j : Fin i) :
      (evenize c).block j = evenizedBlock c.1 j := by
    unfold IndexedComposition.block
    have hindex : Fin.cast (evenize c).blocks_length.symm j =
        ⟨j, by simp [evenize]⟩ := Fin.ext rfl
    rw [hindex]
    exact List.get_ofFn _ _
  have decodeBlock_evenizedBlock {n i m : ℕ}
      (c : PrescribedOddComposition (2 * n) i (2 * m)) (j : Fin i) :
      decodeBlock (oddSupport c.1) (evenize c) j = c.1.block j := by
    have hmem : j ∈ oddSupport c.1 ↔ Odd (c.1.block j) := by simp [oddSupport]
    simp only [decodeBlock, hmem, block_evenize]
    unfold evenizedBlock
    split_ifs with h
    · have hhalf := Nat.two_mul_div_two_add_one_of_odd h
      rw [mul_add]
      omega
    · have heven : Even (c.1.block j) := Nat.not_odd_iff_even.mp h
      rw [Nat.two_mul_div_two_of_even heven]
  have decode_evenize {n i m : ℕ}
      (c : PrescribedOddComposition (2 * n) i (2 * m)) :
      decode (⟨oddSupport c.1, c.2⟩, evenize c) = c := by
    apply Subtype.ext
    apply ic_ext_block
    intro j
    rw [block_decode]
    exact decodeBlock_evenizedBlock c j
  have block_pos {total length : ℕ} (c : IndexedComposition total length)
      (j : Fin length) : 0 < c.block j := by
    exact c.blocks_pos (List.get_mem _ _)
  have odd_decodeBlock_iff {n i m : ℕ} (S : Finset (Fin i))
      (c : IndexedComposition (n + m) i) (j : Fin i) :
      Odd (decodeBlock S c j) ↔ j ∈ S := by
    unfold decodeBlock
    split_ifs with h
    · refine ⟨fun _ => h, fun _ => ?_⟩
      have hpos := block_pos c j
      refine ⟨c.block j - 1, ?_⟩
      omega
    · refine ⟨?_, fun hj => (h hj).elim⟩
      rintro ⟨a, ha⟩
      omega
  have oddSupport_decode {n i m : ℕ}
      (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
      oddSupport (decode data).1 = data.1.1 := by
    ext j
    simp only [oddSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [block_decode]
    exact odd_decodeBlock_iff _ _ _
  have evenizedBlock_decodeBlock {n i m : ℕ}
      (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) (j : Fin i) :
      evenizedBlock (decode data).1 j = data.2.block j := by
    have hodd : Odd ((decode data).1.block j) ↔ j ∈ data.1.1 := by
      rw [block_decode]
      exact odd_decodeBlock_iff _ _ _
    unfold evenizedBlock
    rw [block_decode]
    have hodd' : Odd (decodeBlock data.1.1 data.2 j) ↔ j ∈ data.1.1 :=
      odd_decodeBlock_iff _ _ _
    rw [if_congr hodd' rfl rfl]
    simp only [decodeBlock]
    split_ifs with h
    · have hpos := block_pos data.2 j
      omega
    · omega
  have evenize_decode {n i m : ℕ}
      (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
      (⟨oddSupport (decode data).1, (decode data).2⟩, evenize (decode data)) = data := by
    apply Prod.ext
    · apply Subtype.ext
      exact oddSupport_decode data
    · apply ic_ext_block
      intro j
      rw [block_evenize]
      exact evenizedBlock_decodeBlock data j
  exact {
    toFun c := (⟨oddSupport c.1, c.2⟩, evenize c)
    invFun := decode
    left_inv := decode_evenize
    right_inv := evenize_decode }
/-- The parity-evenization equivalence with its second component exposed as the
pinned Mathlib `Composition` type used by the subsequent path-block count. -/
def parityCompositionEquiv (n i m : ℕ) :
    PrescribedOddComposition (2 * n) i (2 * m) ≃
      PositionSet i (2 * m) × {c : Composition (n + m) // c.length = i} :=
  (parityEvenizationEquiv n i m).trans
    (Equiv.prodCongr (Equiv.refl _) (IndexedComposition.compositionEquiv (n + m) i))

def fixedLengthCompositionEquiv (total length : ℕ) (htotal : 0 < total)
    (hlength : 0 < length) :
    {c : Composition total // c.length = length} ≃
      {s : Finset (Fin (total - 1)) // s.card = length - 1} := by
  have card_compositionAsSetEquiv {total : ℕ} (htotal : 0 < total)
      (c : CompositionAsSet total) :
      ((compositionAsSetEquiv total) c).card = c.length - 1 := by
    classical
    let shift : Fin (total - 1) ↪ Fin (total + 1) :=
      { toFun := fun j => ⟨j + 1, by omega⟩
        inj' := by intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h) }
    let s := (compositionAsSetEquiv total) c
    have hmem (j : Fin (total - 1)) :
        j ∈ s ↔ (⟨1 + j.val, by omega⟩ : Fin total.succ) ∈ c.boundaries := by
      simp [s, compositionAsSetEquiv]
    have hbound : c.boundaries = insert 0 (insert (Fin.last total) (s.map shift)) := by
      ext x
      constructor
      · intro hx
        by_cases hx0 : x = 0
        · simp [hx0]
        by_cases hxlast : x = Fin.last total
        · simp [hxlast]
        have hxpos : 0 < x.val := Nat.pos_of_ne_zero fun h => hx0 (Fin.ext h)
        have hxlt : x.val < total := by
          have hxle : x.val ≤ total := Nat.le_of_lt_succ x.isLt
          exact lt_of_le_of_ne hxle fun h => hxlast (Fin.ext h)
        let j : Fin (total - 1) := ⟨x.val - 1, by omega⟩
        have hshift : shift j = x := by
          apply Fin.ext
          change x.val - 1 + 1 = x.val
          omega
        have hj : j ∈ s := by
          apply (hmem j).2
          have hpoint : (⟨1 + j.val, by omega⟩ : Fin total.succ) = x := by
            apply Fin.ext
            change 1 + (x.val - 1) = x.val
            omega
          rw [hpoint]
          exact hx
        simp [hj, ← hshift]
      · intro hx
        rcases Finset.mem_insert.mp hx with hx0 | hx
        · simpa [hx0] using c.zero_mem
        rcases Finset.mem_insert.mp hx with hxlast | hx
        · simpa [hxlast] using c.getLast_mem
        rcases Finset.mem_map.mp hx with ⟨j, hj, rfl⟩
        have hj' := (hmem j).1 hj
        have hpoint : (⟨1 + j.val, by omega⟩ : Fin total.succ) = shift j := by
          apply Fin.ext
          change 1 + j.val = j.val + 1
          omega
        rw [← hpoint]
        exact hj'
    have hzero_not_mem : (0 : Fin (total + 1)) ∉ s.map shift := by
      intro h
      rcases Finset.mem_map.mp h with ⟨j, _, hj⟩
      have hval := congrArg Fin.val hj
      change j.val + 1 = 0 at hval
      omega
    have hlast_not_mem : Fin.last total ∉ s.map shift := by
      intro h
      rcases Finset.mem_map.mp h with ⟨j, _, hj⟩
      have hjlt : j.val + 1 < total := by omega
      have hval := congrArg Fin.val hj
      change j.val + 1 = total at hval
      omega
    have hzero_ne_last : (0 : Fin (total + 1)) ≠ Fin.last total := by
      intro h
      have hval := congrArg Fin.val h
      change 0 = total at hval
      omega
    have hcard : c.boundaries.card = s.card + 2 := by
      rw [hbound, Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem hlast_not_mem, Finset.card_map]
      · simp [hzero_ne_last, hzero_not_mem]
    have hlen : s.card + 2 = c.length + 1 :=
      hcard.symm.trans c.card_boundaries_eq_succ_length
    dsimp [s] at hlen
    omega
  let e := (_root_.compositionEquiv total).trans (compositionAsSetEquiv total)
  apply e.subtypeEquiv
  intro c
  have hcard := card_compositionAsSetEquiv htotal c.toCompositionAsSet
  have hclength : 0 < c.length := c.length_pos_of_pos htotal
  change c.length = length ↔
    ((compositionAsSetEquiv total) c.toCompositionAsSet).card = length - 1
  rw [hcard, c.toCompositionAsSet_length]
  omega
private theorem card_prescribedOddComposition (n i m : ℕ)
    (htotal : 0 < n + m) (hlength : 0 < i) :
    Fintype.card (PrescribedOddComposition (2 * n) i (2 * m)) =
      Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1) := by
  have card_fixedLengthComposition_of_pos (total length : ℕ)
      (htotal : 0 < total) (hlength : 0 < length) :
      Fintype.card {c : Composition total // c.length = length} =
        Nat.choose (total - 1) (length - 1) := by
    rw [Fintype.card_congr (fixedLengthCompositionEquiv total length htotal hlength),
      Fintype.card_finset_len, Fintype.card_fin]
  have card_fixedLengthComposition (total length : ℕ) :
      Fintype.card {c : Composition total // c.length = length} =
        if total = 0 then if length = 0 then 1 else 0
        else if length = 0 then 0 else Nat.choose (total - 1) (length - 1) := by
    by_cases htotal : total = 0
    · subst total
      by_cases hlength : length = 0
      · subst length
        simp only [if_pos]
        apply Fintype.card_eq_one_iff.2
        let c0 : Composition 0 :=
          { blocks := []
            blocks_pos := by simp
            blocks_sum := by simp }
        refine ⟨⟨c0, rfl⟩, ?_⟩
        intro c
        apply Subtype.ext
        apply Composition.ext
        simpa [c0] using c.1.blocks_eq_nil.mpr rfl
      · simp only [if_pos, hlength, if_false]
        rw [Fintype.card_eq_zero_iff]
        exact ⟨fun c => hlength (c.2.symm.trans (c.1.length_eq_zero.mpr rfl))⟩
    · by_cases hlength : length = 0
      · subst length
        simp only [htotal, if_false, if_pos]
        rw [Fintype.card_eq_zero_iff]
        exact ⟨fun c => htotal (c.1.length_eq_zero.mp c.2)⟩
      · simp only [htotal, hlength, if_false]
        exact card_fixedLengthComposition_of_pos total length (Nat.pos_of_ne_zero htotal)
          (Nat.pos_of_ne_zero hlength)
  have card_indexedComposition (total length : ℕ) :
      Fintype.card (IndexedComposition total length) =
        if total = 0 then if length = 0 then 1 else 0
        else if length = 0 then 0 else Nat.choose (total - 1) (length - 1) := by
    rw [Fintype.card_congr (IndexedComposition.compositionEquiv total length)]
    exact card_fixedLengthComposition total length
  rw [Fintype.card_congr (parityEvenizationEquiv n i m), Fintype.card_prod,
    Fintype.card_finset_len, Fintype.card_fin, card_indexedComposition]
  have hlength_ne : i ≠ 0 := Nat.ne_of_gt hlength
  have hparts : ¬(n = 0 ∧ m = 0) := by omega
  simp [hlength_ne, hparts]
open D5.S3.Combinatorics.Geometry.CrownOrderPolytope

private theorem crownPartitionGraph_walk_to_cycle {n : ℕ} (hn : 2 ≤ n)
    (s : Setoid (CrownAugmentedVertex n)) {u v : CrownAugmentedVertex n}
    (p : (crownPartitionGraph s).Walk u v) :
    ∀ {i j : Fin (2 * n)}, u = .vertex i → v = .vertex j →
      (¬ s.r u .bottom) → (¬ s.r u .top) →
      ∃ q : (SimpleGraph.cycleGraph (2 * n)).Walk i j,
        ∀ k ∈ q.support, s.r u (.vertex k) := by
  have parity_succ_mod {n : ℕ} (_hn : 2 ≤ n) (a : Fin (2 * n)) :
      ((a.val + 1) % (2 * n)) % 2 = (a.val + 1) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    exact dvd_mul_right 2 n
  have pred_mod_succ_mod {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N)
      (hab : a = (b + 1) % N) : b = (a + N - 1) % N := by
    by_cases hwrap : b + 1 < N
    · rw [Nat.mod_eq_of_lt hwrap] at hab
      rw [hab, show b + 1 + N - 1 = b + N by omega, Nat.add_mod, Nat.mod_self,
        Nat.add_zero, Nat.mod_eq_of_lt hb]
      exact (Nat.mod_eq_of_lt hb).symm
    · have hbtop : b + 1 = N := by omega
      rw [hbtop, Nat.mod_self] at hab
      subst a
      rw [zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  have succ_mod_of_pred_mod {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N)
      (hba : b = (a + N - 1) % N) : a = (b + 1) % N := by
    by_cases ha0 : a = 0
    · subst a
      rw [zero_add, Nat.mod_eq_of_lt (by omega)] at hba
      rw [hba, show N - 1 + 1 = N by omega, Nat.mod_self]
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hform : a + N - 1 = (a - 1) + N := by omega
      have hpredlt : a - 1 < N := by omega
      have hsum : ((a - 1) + N) % N = a - 1 := by
        simp [Nat.mod_eq_of_lt hpredlt]
      rw [hform, hsum] at hba
      rw [hba, show a - 1 + 1 = a by omega, Nat.mod_eq_of_lt ha]
  have crownRelation_symm_iff_cycleGraph_adj {n : ℕ} (hn : 2 ≤ n)
      (i j : Fin (2 * n)) :
      crownRelation n i j ∨ crownRelation n j i ↔
        (SimpleGraph.cycleGraph (2 * n)).Adj i j := by
    letI : NeZero (2 * n) := ⟨by omega⟩
    constructor
    · intro h
      rw [SimpleGraph.cycleGraph_adj']
      rcases h with hij | hji
      · rcases hij with ⟨_, hnext | hprev⟩
        · right
          have hji : j = i + 1 := by
            apply Fin.ext
            simpa [Fin.add_def] using hnext
          simpa [hji] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
        · left
          have hij : i = j + 1 := by
            apply Fin.ext
            have hsucc := succ_mod_of_pred_mod (N := 2 * n) (a := i.val) (b := j.val)
              (by omega) i.isLt j.isLt hprev
            simpa [Fin.add_def] using hsucc
          simpa [hij] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
      · rcases hji with ⟨_, hnext | hprev⟩
        · left
          have hij : i = j + 1 := by
            apply Fin.ext
            simpa [Fin.add_def] using hnext
          simpa [hij] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
        · right
          have hji : j = i + 1 := by
            apply Fin.ext
            have hsucc := succ_mod_of_pred_mod (N := 2 * n) (a := j.val) (b := i.val)
              (by omega) j.isLt i.isLt hprev
            simpa [Fin.add_def] using hsucc
          simpa [hji] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
    · intro hij
      rw [SimpleGraph.cycleGraph_adj'] at hij
      rcases hij with hij | hji
      · have hsub : i - j = (1 : Fin (2 * n)) := by
          apply Fin.ext
          change (i - j).val = 1 % (2 * n)
          rw [Nat.mod_eq_of_lt (by omega)]
          exact hij
        have hij' : i = j + 1 := (sub_eq_iff_eq_add').mp hsub
        by_cases hj : j.val % 2 = 0
        · right
          refine ⟨hj, Or.inl ?_⟩
          have hval := congrArg Fin.val hij'
          simpa [Fin.add_def] using hval
        · left
          have hjodd : j.val % 2 = 1 := by omega
          have hival := congrArg Fin.val hij'
          have hival' : i.val = (j.val + 1) % (2 * n) := by
            simpa [Fin.add_def] using hival
          have hi : i.val % 2 = 0 := by
            rw [hival']
            rw [parity_succ_mod hn]
            omega
          refine ⟨hi, Or.inr ?_⟩
          exact pred_mod_succ_mod (N := 2 * n) (a := i.val) (b := j.val)
            (by omega) i.isLt j.isLt hival'
      · have hsub : j - i = (1 : Fin (2 * n)) := by
          apply Fin.ext
          change (j - i).val = 1 % (2 * n)
          rw [Nat.mod_eq_of_lt (by omega)]
          exact hji
        have hji' : j = i + 1 := (sub_eq_iff_eq_add').mp hsub
        by_cases hi : i.val % 2 = 0
        · left
          refine ⟨hi, Or.inl ?_⟩
          have hval := congrArg Fin.val hji'
          simpa [Fin.add_def] using hval
        · right
          have hiodd : i.val % 2 = 1 := by omega
          have hjval := congrArg Fin.val hji'
          have hjval' : j.val = (i.val + 1) % (2 * n) := by
            simpa [Fin.add_def] using hjval
          have hj : j.val % 2 = 0 := by
            rw [hjval']
            rw [parity_succ_mod hn]
            omega
          refine ⟨hj, Or.inr ?_⟩
          exact pred_mod_succ_mod (N := 2 * n) (a := j.val) (b := i.val)
            (by omega) j.isLt i.isLt hjval'
  have crownPartitionGraph_vertex_adj_iff_cycleGraph_adj {n : ℕ} (hn : 2 ≤ n)
      (s : Setoid (CrownAugmentedVertex n)) (i j : Fin (2 * n)) :
      (crownPartitionGraph s).Adj (.vertex i) (.vertex j) ↔
        s.r (.vertex i) (.vertex j) ∧ (SimpleGraph.cycleGraph (2 * n)).Adj i j := by
    rw [crownPartitionGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, h | h⟩
      · have hij : i ≠ j := by
          intro hij
          apply hne
          simp [hij]
        rcases h.2 with hij' | hrel
        · exact (hij hij').elim
        · exact ⟨h.1, (crownRelation_symm_iff_cycleGraph_adj hn i j).1 (Or.inl hrel)⟩
      · have hij : i ≠ j := by
          intro hij
          apply hne
          simp [hij]
        rcases h.2 with hji' | hrel
        · exact (hij hji'.symm).elim
        · exact ⟨s.symm h.1, (crownRelation_symm_iff_cycleGraph_adj hn i j).1 (Or.inr hrel)⟩
    · rintro ⟨hs, hadj⟩
      have hne : CrownAugmentedVertex.vertex i ≠ CrownAugmentedVertex.vertex j := by
        intro h
        have hij : i = j := by injection h
        exact hadj.ne hij
      refine ⟨hne, ?_⟩
      rcases (crownRelation_symm_iff_cycleGraph_adj hn i j).2 hadj with hrel | hrel
      · exact Or.inl ⟨hs, Or.inr hrel⟩
      · exact Or.inr ⟨s.symm hs, Or.inr hrel⟩
  induction p with
  | nil =>
      intro i j hui huv hbottom htop
      have hij : i = j := by simpa [hui] using huv
      subst j
      refine ⟨.nil, ?_⟩
      intro k hk
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hk
      subst k
      rw [← hui]
  | @cons a b c hab p ih =>
      intro i j hui hv hbottom htop
      subst a
      have hsab : s.r (.vertex i) b := by
        rw [crownPartitionGraph, SimpleGraph.fromRel_adj] at hab
        rcases hab.2 with h | h
        · exact h.1
        · exact s.symm h.1
      cases b with
      | bottom => exact (hbottom hsab).elim
      | top => exact (htop hsab).elim
      | vertex k =>
          have hcycle : (SimpleGraph.cycleGraph (2 * n)).Adj i k :=
            (crownPartitionGraph_vertex_adj_iff_cycleGraph_adj hn s i k).mp hab |>.2
          have hbottom' : ¬ s.r (.vertex k) .bottom := by
            intro hk
            exact hbottom (s.trans hsab hk)
          have htop' : ¬ s.r (.vertex k) .top := by
            intro hk
            exact htop (s.trans hsab hk)
          obtain ⟨q, hq⟩ := ih rfl hv hbottom' htop'
          refine ⟨q.cons hcycle, ?_⟩
          intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact s.refl _
          · exact s.trans hsab (hq x hx)
/-- For `n ≥ 2`, the original vertices in an actual CCP block disjoint from the augmented
bottom and top induce a connected subgraph of the cyclic comparability graph.  The transported
walk remains inside the same real partition block at every vertex, including across the cyclic
wraparound edge. -/
theorem crownPartition_originalBlock_cycleGraph_connected {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n) (i : Fin (2 * n))
    (hbottom : ¬ P.toSetoid.r (.vertex i) .bottom)
    (htop : ¬ P.toSetoid.r (.vertex i) .top) :
    ((SimpleGraph.cycleGraph (2 * n)).induce
      {j | P.toSetoid.r (.vertex i) (.vertex j)}).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨i, P.toSetoid.refl _⟩⟩ }
  intro a b
  obtain ⟨q, hq⟩ := crownPartitionGraph_walk_to_cycle hn P.toSetoid
    ((P.connected _ _).mp (P.toSetoid.trans (P.toSetoid.symm a.2) b.2)).some
    rfl rfl
    (fun ha => hbottom (P.toSetoid.trans a.2 ha))
    (fun ha => htop (P.toSetoid.trans a.2 ha))
  have hsupport : ∀ k ∈ q.support,
      P.toSetoid.r (.vertex i) (.vertex k) := by
    intro k hk
    exact P.toSetoid.trans a.2 (hq k hk)
  have w := q.induce {j | P.toSetoid.r (.vertex i) (.vertex j)} hsupport
  change Nonempty (((SimpleGraph.cycleGraph (2 * n)).induce
    {j | P.toSetoid.r (.vertex i) (.vertex j)}).Walk a b)
  simpa only [Subtype.coe_eta] using (show Nonempty _ from ⟨w⟩)

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
