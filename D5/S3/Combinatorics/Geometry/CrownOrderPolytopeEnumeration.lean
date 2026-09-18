/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Composition]
   utility: none
   digest: Prescribed-parity compositions are reversibly evenized with exact odd positions. -/

/- Library search (2026-09-19): the pinned Mathlib Composition API supplies positive
   list compositions, blocksFun, and the unrestricted composition equivalence, but no
   fixed-length prescribed-parity count. Repository search found no crown-partition or
   prescribed-parity composition enumeration. The construction below is the reversible
   evenization in Lemma 3.5 of arXiv:2504.05123v3, before cyclic cut multiplicity. -/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

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

@[ext]
private theorem ext {total length : ℕ} {c d : IndexedComposition total length}
    (h : c.blocks = d.blocks) : c = d := by
  cases c
  cases d
  cases h
  rfl

private theorem ext_block {total length : ℕ} {c d : IndexedComposition total length}
    (h : ∀ j, c.block j = d.block j) : c = d := by
  apply ext
  apply List.ext_get
  · exact c.blocks_length.trans d.blocks_length.symm
  · intro j hjc hjd
    have hblock := h (Fin.cast c.blocks_length ⟨j, hjc⟩)
    simpa [block] using hblock

private theorem block_pos {total length : ℕ} (c : IndexedComposition total length)
    (j : Fin length) : 0 < c.block j := by
  exact c.blocks_pos (List.get_mem _ _)

private theorem sum_block {total length : ℕ} (c : IndexedComposition total length) :
    ∑ j, c.block j = total := by
  have hlist : List.ofFn c.block = c.blocks := by
    apply List.ext_get
    · simp [c.blocks_length]
    · intro j hj₁ hj₂
      simp [block]
  calc
    ∑ j, c.block j = (List.ofFn c.block).sum := List.sum_ofFn.symm
    _ = c.blocks.sum := congrArg List.sum hlist
    _ = total := c.blocks_sum

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

private theorem two_mul_evenizedBlock {total length : ℕ}
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

private theorem evenizedBlock_pos {total length : ℕ}
    (c : IndexedComposition total length) (j : Fin length) :
    0 < evenizedBlock c j := by
  unfold evenizedBlock
  split_ifs with h
  · omega
  · have heven : Even (c.block j) := Nat.not_odd_iff_even.mp h
    obtain ⟨a, ha⟩ := heven
    have := c.block_pos j
    omega

private def evenize {n i m : ℕ} (c : PrescribedOddComposition (2 * n) i (2 * m)) :
    IndexedComposition (n + m) i where
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
    have hsum := c.1.sum_block
    simp only [Finset.sum_add_distrib] at hpoint
    rw [hsum, hindicator] at hpoint
    rw [List.sum_ofFn]
    omega

private theorem block_evenize {n i m : ℕ}
    (c : PrescribedOddComposition (2 * n) i (2 * m)) (j : Fin i) :
    (evenize c).block j = evenizedBlock c.1 j := by
  unfold IndexedComposition.block
  have hindex : Fin.cast (evenize c).blocks_length.symm j =
      ⟨j, by simp [evenize]⟩ := Fin.ext rfl
  rw [hindex]
  exact List.get_ofFn _ _

private def decodeBlock {n i m : ℕ} (S : Finset (Fin i)) (c : IndexedComposition (n + m) i)
    (j : Fin i) : ℕ :=
  if j ∈ S then 2 * c.block j - 1 else 2 * c.block j

private theorem decodeBlock_pos {n i m : ℕ} (S : Finset (Fin i))
    (c : IndexedComposition (n + m) i) (j : Fin i) :
    0 < decodeBlock S c j := by
  unfold decodeBlock
  split_ifs <;> have := c.block_pos j <;> omega

private theorem decodeBlock_add_indicator {n i m : ℕ} (S : Finset (Fin i))
    (c : IndexedComposition (n + m) i) (j : Fin i) :
    decodeBlock S c j + (if j ∈ S then 1 else 0) = 2 * c.block j := by
  unfold decodeBlock
  split_ifs <;> have := c.block_pos j <;> omega

private theorem odd_decodeBlock_iff {n i m : ℕ} (S : Finset (Fin i))
    (c : IndexedComposition (n + m) i) (j : Fin i) :
    Odd (decodeBlock S c j) ↔ j ∈ S := by
  unfold decodeBlock
  split_ifs with h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have hpos := c.block_pos j
    refine ⟨c.block j - 1, ?_⟩
    omega
  · refine ⟨?_, fun hj => (h hj).elim⟩
    rintro ⟨a, ha⟩
    omega

private def decodedComposition {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
    IndexedComposition (2 * n) i := by
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
          rw [← Finset.mul_sum, c.sum_block]
        rw [hindicator, hright] at hpoint
        rw [List.sum_ofFn]
        omega }

private theorem block_decodedComposition {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) (j : Fin i) :
    (decodedComposition data).block j = decodeBlock data.1.1 data.2 j := by
  unfold IndexedComposition.block
  have hindex : Fin.cast (decodedComposition data).blocks_length.symm j =
      ⟨j, by simp [decodedComposition]⟩ := Fin.ext rfl
  rw [hindex]
  exact List.get_ofFn _ _

private def decode {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
    PrescribedOddComposition (2 * n) i (2 * m) := by
  refine ⟨decodedComposition data, ?_⟩
  calc
    (oddSupport (decodedComposition data)).card = data.1.1.card := by
      apply congrArg Finset.card
      ext j
      simp only [oddSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [block_decodedComposition]
      exact odd_decodeBlock_iff _ _ _
    _ = 2 * m := data.1.2

private theorem block_decode {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) (j : Fin i) :
    (decode data).1.block j = decodeBlock data.1.1 data.2 j := by
  exact block_decodedComposition data j

private theorem oddSupport_decode {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
    oddSupport (decode data).1 = data.1.1 := by
  ext j
  simp only [oddSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [block_decode]
  exact odd_decodeBlock_iff _ _ _

private theorem decodeBlock_evenizedBlock {n i m : ℕ}
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

private theorem evenizedBlock_decodeBlock {n i m : ℕ}
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
  · have hpos := data.2.block_pos j
    omega
  · omega

private theorem decode_evenize {n i m : ℕ}
    (c : PrescribedOddComposition (2 * n) i (2 * m)) :
    decode (⟨oddSupport c.1, c.2⟩, evenize c) = c := by
  apply Subtype.ext
  apply IndexedComposition.ext_block
  intro j
  rw [block_decode]
  exact decodeBlock_evenizedBlock c j

private theorem evenize_decode {n i m : ℕ}
    (data : PositionSet i (2 * m) × IndexedComposition (n + m) i) :
    (⟨oddSupport (decode data).1, (decode data).2⟩, evenize (decode data)) = data := by
  apply Prod.ext
  · apply Subtype.ext
    exact oddSupport_decode data
  · apply IndexedComposition.ext_block
    intro j
    rw [block_evenize]
    exact evenizedBlock_decodeBlock data j

/-- Lemma 3.5's parity step: a positive composition of `2n` into `i` blocks
with exactly `2m` odd blocks is equivalent to choosing those `2m` positions
and a positive composition of `n+m` into `i` blocks. The forward map adds one
to each odd block and halves; the inverse doubles and subtracts one exactly at
the recorded positions. -/
def parityEvenizationEquiv (n i m : ℕ) :
    PrescribedOddComposition (2 * n) i (2 * m) ≃
      PositionSet i (2 * m) × IndexedComposition (n + m) i where
  toFun c := (⟨oddSupport c.1, c.2⟩, evenize c)
  invFun := decode
  left_inv := decode_evenize
  right_inv := evenize_decode

/-- The parity-evenization equivalence with its second component exposed as the
pinned Mathlib `Composition` type used by the subsequent path-block count. -/
def parityCompositionEquiv (n i m : ℕ) :
    PrescribedOddComposition (2 * n) i (2 * m) ≃
      PositionSet i (2 * m) × {c : Composition (n + m) // c.length = i} :=
  (parityEvenizationEquiv n i m).trans
    (Equiv.prodCongr (Equiv.refl _) (IndexedComposition.compositionEquiv (n + m) i))

private theorem card_prescribedOddComposition (n i m : ℕ) :
    Fintype.card (PrescribedOddComposition (2 * n) i (2 * m)) =
      Nat.choose i (2 * m) * Fintype.card (IndexedComposition (n + m) i) := by
  rw [Fintype.card_congr (parityEvenizationEquiv n i m), Fintype.card_prod,
    Fintype.card_finset_len, Fintype.card_fin]

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
