import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SharedSixLeaves

/-! Geometry and degree counts for singleton-cut supports in the five-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SingletonCutObstructions

open Finset Q5SmallParitySupport Q5SharedSixLeaves

/-- Adjacency in the five-cube. -/
def adjacent (x y : BitVec 5) : Prop :=
  x ^^^ y ∈ ({1, 2, 4, 8, 16} : Finset (BitVec 5))

instance (x y : BitVec 5) : Decidable (adjacent x y) :=
  inferInstanceAs (Decidable (_ ∈ (_ : Finset (BitVec 5))))

private theorem adjacent_comm (x y : BitVec 5) : adjacent x y ↔ adjacent y x := by
  simp only [adjacent, BitVec.xor_comm x y]

private theorem adjacent_flip (x y : BitVec 5) :
    adjacent x y ↔ ∃ i : Fin 5, x ^^^ BitVec.twoPow 5 i.val = y :=
  (show ∀ i j : Fin 32, adjacent (BitVec.ofFin i) (BitVec.ofFin j) ↔
    ∃ k : Fin 5, BitVec.ofFin i ^^^ BitVec.twoPow 5 k.val = BitVec.ofFin j by decide)
    x.toFin y.toFin

private theorem degree_filter (S : Finset (BitVec 5)) (x : BitVec 5) :
    degree S x = (S.filter (adjacent x)).card := rfl

private theorem degree_mono {S T : Finset (BitVec 5)} (h : S ⊆ T) (x : BitVec 5) :
    degree S x ≤ degree T x :=
  card_le_card (filter_subset_filter _ h)

private theorem degree_congr {S T : Finset (BitVec 5)} (x : BitVec 5)
    (h : ∀ y, adjacent x y → (y ∈ S ↔ y ∈ T)) :
    degree S x = degree T x := by
  rw [degree_filter, degree_filter]
  congr 1
  ext y
  simp only [mem_filter]
  exact and_congr_left (h y)

private theorem xor_cancel {n : Nat} (x a : BitVec n) : x ^^^ a ^^^ a = x := by
  simp [BitVec.xor_assoc]

private theorem swap_xor (x a b : BitVec 5) : x ^^^ a ^^^ b = x ^^^ b ^^^ a := by
  simp only [BitVec.xor_assoc, BitVec.xor_comm a b]

private def translation (a : BitVec 5) : BitVec 5 ↪ BitVec 5 :=
  ⟨(· ^^^ a), fun _ _ h => (BitVec.xor_left_inj a).mp h⟩

@[simp] private theorem translation_apply (a x : BitVec 5) :
    translation a x = x ^^^ a := rfl

@[simp] private theorem mem_translate {S : Finset (BitVec 5)} {a x : BitVec 5} :
    x ∈ S.map (translation a) ↔ x ^^^ a ∈ S := by
  simp only [mem_map, translation_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [xor_cancel] using hy
  · intro hx
    exact ⟨x ^^^ a, hx, xor_cancel x a⟩

private theorem bitParity_xor (x a : BitVec 5) :
    bitParity (x ^^^ a) = (bitParity x ^^ bitParity a) := by
  simp only [bitParity, BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm]

private theorem parity_of_adjacent {x y : BitVec 5} (h : adjacent x y) :
    bitParity y = !bitParity x := by
  obtain ⟨i, rfl⟩ := (adjacent_flip x y).mp h
  have units : ∀ i : Fin 5, bitParity (BitVec.twoPow 5 i.val) = true := by decide
  rw [bitParity_xor, units, Bool.xor_true]

private theorem degree_translate (S : Finset (BitVec 5)) (x a : BitVec 5) :
    degree (S.map (translation a)) x = degree S (x ^^^ a) := by
  rw [degree_filter, degree_filter, filter_map, card_map]
  congr 1
  ext y
  have h : x ^^^ (y ^^^ a) = (x ^^^ a) ^^^ y := by
    simp only [BitVec.xor_assoc, BitVec.xor_comm a y]
  simp [Function.comp_def, adjacent, h]

private theorem oddNeighborImage_translate (S : Finset (BitVec 5)) (a : BitVec 5) :
    oddNeighborImage (S.map (translation a)) = (oddNeighborImage S).map (translation a) := by
  ext x
  simp only [mem_oddNeighborImage, mem_translate, neighborParity, swap_xor x _ a]

private def neighbors (x : BitVec 5) : Finset (BitVec 5) :=
  {x ^^^ 1, x ^^^ 2, x ^^^ 4, x ^^^ 8, x ^^^ 16}

private theorem mem_neighbors (x y : BitVec 5) : y ∈ neighbors x ↔ adjacent x y :=
  (show ∀ i j : Fin 32, BitVec.ofFin j ∈ neighbors (BitVec.ofFin i) ↔
    adjacent (BitVec.ofFin i) (BitVec.ofFin j) by decide) x.toFin y.toFin

private theorem flips_distinct (x : BitVec 5) :
    x ^^^ 1 ∉ ({x ^^^ 2, x ^^^ 4, x ^^^ 8, x ^^^ 16} : Finset (BitVec 5)) ∧
    x ^^^ 2 ∉ ({x ^^^ 4, x ^^^ 8, x ^^^ 16} : Finset (BitVec 5)) ∧
    x ^^^ 4 ∉ ({x ^^^ 8, x ^^^ 16} : Finset (BitVec 5)) ∧
    x ^^^ 8 ≠ x ^^^ 16 := by
  simp [BitVec.xor_right_inj]

private theorem degree_mod_two (S : Finset (BitVec 5)) (x : BitVec 5) :
    degree S x % 2 = (neighborParity S x).toNat := by
  have h : S.filter (adjacent x) = (neighbors x).filter (· ∈ S) := by
    ext y
    simp only [mem_filter, mem_neighbors, and_comm]
  rw [degree_filter, h]
  obtain ⟨h1, h2, h4, h8⟩ := flips_distinct x
  simp only [neighbors, neighborParity]
  by_cases a : x ^^^ 1 ∈ S <;> by_cases b : x ^^^ 2 ∈ S <;>
    by_cases c : x ^^^ 4 ∈ S <;> by_cases d : x ^^^ 8 ∈ S <;>
    by_cases e : x ^^^ 16 ∈ S <;>
    simp_all [filter_insert, filter_singleton, card_insert_of_notMem, BitVec.xor_right_inj]

private abbrev side (S : Finset (BitVec 5)) (p : Bool) :=
  S.filter fun x => bitParity x = p

private theorem card_sides (S : Finset (BitVec 5)) (p : Bool) :
    (side S p).card + (side S (!p)).card = S.card := by
  cases p
  · simpa only [Bool.not_false, Bool.not_eq_false] using
      (card_filter_add_card_filter_not (s := S) (fun x => bitParity x = false))
  · simpa only [Bool.not_true, Bool.not_eq_true] using
      (card_filter_add_card_filter_not (s := S) (fun x => bitParity x = true))

private theorem side_eq_image {S : Finset (BitVec 5)}
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) (p : Bool) :
    side S (!p) = oddNeighborImage (side S p) := by
  ext x
  rw [mem_oddNeighborImage, ← Bool.toNat_eq_one, ← degree_mod_two]
  by_cases hp : bitParity x = !p
  · have h : degree (side S p) x = degree S x :=
      degree_congr x fun y hy => by
        simp [side, parity_of_adjacent hy, hp]
    rw [h, degree_mod_two, ← hpar x]
    simp [hp]
  · have h : degree (side S p) x = 0 := by
      rw [degree_filter, card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨hyS, hxy⟩ := mem_filter.mp hy
      exact hp (by rw [parity_of_adjacent ((adjacent_comm x y).mp hxy), (mem_filter.mp hyS).2])
    simp [hp, h]

private def evenWord (i : Fin 16) : BitVec 5 :=
  let x := (BitVec.ofFin (w := 4) i).setWidth 5
  if bitParity x then x ^^^ 16 else x

private theorem evenWord_decode (x : BitVec 5) (h : bitParity x = false) :
    evenWord (x.setWidth 4).toFin = x :=
  (show ∀ i : Fin 32, bitParity (BitVec.ofFin i) = false →
    evenWord ((BitVec.ofFin (w := 5) i).setWidth 4).toFin = BitVec.ofFin i by decide) x.toFin h

private theorem image_singleton_card (a : BitVec 5) :
    (oddNeighborImage {a}).card = 5 := by
  have h := congrArg card (oddNeighborImage_translate ({a} : Finset (BitVec 5)) a)
  rw [card_map] at h
  have hz : (oddNeighborImage {0#5}).card = 5 := by decide
  simpa only [map_singleton, translation_apply, BitVec.xor_self, hz] using h.symm

private theorem image_triple_card {a b c : BitVec 5}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : bitParity b = bitParity a) (hq : bitParity c = bitParity a) :
    7 ≤ (oddNeighborImage {a, b, c}).card := by
  have table : ∀ i j : Fin 16, evenWord i ≠ 0 → evenWord j ≠ 0 → evenWord i ≠ evenWord j →
      7 ≤ (oddNeighborImage {0, evenWord i, evenWord j}).card := by decide
  have hd (x : BitVec 5) (hx : bitParity x = bitParity a) :
      evenWord ((x ^^^ a).setWidth 4).toFin = x ^^^ a :=
    evenWord_decode _ (by simp [bitParity_xor, hx])
  have h := table ((b ^^^ a).setWidth 4).toFin ((c ^^^ a).setWidth 4).toFin
  rw [hd b hp, hd c hq] at h
  have hb : b ^^^ a ≠ 0 := by simpa [BitVec.xor_eq_zero_iff] using hab.symm
  have hc : c ^^^ a ≠ 0 := by simpa [BitVec.xor_eq_zero_iff] using hac.symm
  have ht := h hb hc (fun h => hbc ((BitVec.xor_left_inj a).mp h))
  have hmap : ({a, b, c} : Finset (BitVec 5)).map (translation a) =
      {0, b ^^^ a, c ^^^ a} := by simp [map_insert]
  rwa [← hmap, oddNeighborImage_translate, card_map] at ht

private theorem parity_sizes {S : Finset (BitVec 5)} (hS : S.card = 8)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    ((side S false).card = 4 ∧ (side S true).card = 4) ∨
      ∃ p, (side S p).card = 2 ∧ (side S (!p)).card = 6 := by
  have small (p : Bool) (hle : (side S p).card ≤ 4) :
      (side S p).card = 2 ∨ (side S p).card = 4 := by
    have hsum := card_sides S p
    have him := side_eq_image hpar p
    have hc : (side S p).card = 0 ∨ (side S p).card = 1 ∨ (side S p).card = 2 ∨
        (side S p).card = 3 ∨ (side S p).card = 4 := by omega
    rcases hc with h | h | h | h | h
    · have hzero : (oddNeighborImage ∅).card = 0 := by decide
      have ho := congrArg card (him.trans (congrArg oddNeighborImage (card_eq_zero.mp h)))
      omega
    · obtain ⟨a, ha⟩ := card_eq_one.mp h
      have ho := congrArg card him
      rw [ha, image_singleton_card] at ho
      omega
    · exact Or.inl h
    · obtain ⟨a, b, c, hab, hac, hbc, heq⟩ := card_eq_three.mp h
      have hx (x : BitVec 5) (hx : x ∈ ({a, b, c} : Finset (BitVec 5))) : bitParity x = p :=
        (mem_filter.mp (show x ∈ side S p from heq.symm ▸ hx)).2
      rw [heq] at him
      have ho := image_triple_card hab hac hbc
        ((hx b (by simp)).trans (hx a (by simp)).symm)
        ((hx c (by simp)).trans (hx a (by simp)).symm)
      rw [← him] at ho
      omega
    · exact Or.inr h
  have hsum := card_sides S false
  change (side S false).card + (side S true).card = S.card at hsum
  by_cases he : (side S false).card ≤ 4
  · rcases small false he with h | h
    · exact Or.inr ⟨false, h, by change (side S true).card = 6; omega⟩
    · exact Or.inl ⟨h, by omega⟩
  · rcases small true (by omega) with h | h
    · exact Or.inr ⟨true, h, by change (side S false).card = 6; omega⟩
    · exact Or.inl ⟨by omega, h⟩

private theorem degree_le_five (S : Finset (BitVec 5)) (x : BitVec 5) :
    degree S x ≤ 5 := by
  calc
    degree S x = (S.filter (adjacent x)).card := rfl
    _ ≤ (neighbors x).card := card_le_card fun y hy =>
      (mem_neighbors x y).mpr (mem_filter.mp hy).2
    _ = 5 := (show ∀ i : Fin 32, (neighbors (BitVec.ofFin i)).card = 5 by decide) x.toFin

private theorem degree_of_parallel {S : Finset (BitVec 5)} {d : Fin 5}
    (hflip : ∀ x ∈ S, ∀ i : Fin 5, (x ^^^ BitVec.twoPow 5 i.val) ∈ S ↔ i = d)
    {x : BitVec 5} (hx : x ∈ S) :
    degree S x = 1 := by
  have h : S.filter (adjacent x) = {x ^^^ BitVec.twoPow 5 d.val} := by
    ext y
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hy, ha⟩
      obtain ⟨i, rfl⟩ := (adjacent_flip x y).mp ha
      rw [(hflip x hx i).mp hy]
    · rintro rfl
      exact ⟨(hflip x hx d).mpr rfl, (adjacent_flip _ _).mpr ⟨d, rfl⟩⟩
  rw [degree_filter, h, card_singleton]

private def parallelCarrier (d : Fin 5) : Finset (BitVec 5) :=
  let base := (neighbors 0).erase (BitVec.twoPow 5 d.val)
  base ∪ base.map (translation (BitVec.twoPow 5 d.val))

private theorem parallelCarrier_card (d : Fin 5) : (parallelCarrier d).card = 8 :=
  (show ∀ i : Fin 5, (parallelCarrier i).card = 8 by decide) d

private theorem parallelCarrier_external (d : Fin 5) (y : BitVec 5)
    (hy : y ∉ parallelCarrier d) (hd : degree (parallelCarrier d) y = 4) :
    y = 0 ∨ y = BitVec.twoPow 5 d.val :=
  (show ∀ (i : Fin 5) (j : Fin 32), let y := BitVec.ofFin j
    y ∉ parallelCarrier i → degree (parallelCarrier i) y = 4 →
    y = 0 ∨ y = BitVec.twoPow 5 i.val by decide) d y.toFin hy hd

private theorem translate_eq_parallelCarrier {S : Finset (BitVec 5)} {d : Fin 5} {x : BitVec 5}
    (hS : S.card = 8)
    (hflip : ∀ y ∈ S, (y ^^^ BitVec.twoPow 5 d.val) ∈ S)
    (hx : x ∉ S) (hdeg : degree S x = 4) :
    S.map (translation x) = parallelCarrier d := by
  let T := S.map (translation x)
  let k := BitVec.twoPow 5 d.val
  have hclose (y : BitVec 5) (hy : y ∈ T) : y ^^^ k ∈ T := by
    rw [mem_translate] at hy ⊢
    rw [swap_xor]
    exact hflip _ hy
  have hk : k ∉ T := by
    intro h
    have hzero : 0#5 ∈ T := by simpa only [BitVec.xor_self] using hclose k h
    exact hx (by simpa only [T, mem_translate, BitVec.zero_xor] using hzero)
  have hbase : (neighbors 0).erase k = T.filter (adjacent 0) := by
    symm
    apply eq_of_subset_of_card_le
    · intro y hy
      exact mem_erase.mpr ⟨fun he => hk (by simpa only [he] using (mem_filter.mp hy).1),
        (mem_neighbors _ _).mpr (mem_filter.mp hy).2⟩
    · rw [← degree_filter, degree_translate]
      change ((neighbors 0).erase k).card ≤ degree S (0#5 ^^^ x)
      rw [BitVec.zero_xor, hdeg]
      exact Nat.le_of_eq ((show ∀ i : Fin 5,
        ((neighbors 0).erase (BitVec.twoPow 5 i.val)).card = 4 by decide) d)
  change T = parallelCarrier d
  symm
  apply eq_of_subset_of_card_le
  · change (neighbors 0).erase k ∪ ((neighbors 0).erase k).map (translation k) ⊆ T
    rw [hbase]
    intro y hy
    rcases mem_union.mp hy with hy | hy
    · exact (mem_filter.mp hy).1
    · obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
      exact hclose z (mem_filter.mp hz).1
  · rw [parallelCarrier_card, show T.card = S.card from card_map _, hS]

private theorem parallel_external_card {S B : Finset (BitVec 5)} {d : Fin 5}
    (hS : S.card = 8) (hdis : Disjoint S B)
    (hflip : ∀ y ∈ S, (y ^^^ BitVec.twoPow 5 d.val) ∈ S) :
    (B.filter fun x => degree S x = 4).card ≤ 2 := by
  let H := B.filter fun x => degree S x = 4
  by_cases h : H.Nonempty
  · obtain ⟨x, hx⟩ := h
    have hnot (y : BitVec 5) (hy : y ∈ H) : y ∉ S :=
      fun hS => disjoint_left.mp hdis hS (mem_filter.mp hy).1
    have ht := translate_eq_parallelCarrier hS hflip (hnot x hx) (mem_filter.mp hx).2
    have hsub : H.map (translation x) ⊆ {0, BitVec.twoPow 5 d.val} := by
      intro y hy
      rw [mem_translate] at hy
      have ho : y ∉ parallelCarrier d := by
        rw [← ht, mem_translate]
        exact hnot _ hy
      have hd : degree (parallelCarrier d) y = 4 := by
        rw [← ht, degree_translate]
        exact (mem_filter.mp hy).2
      simpa only [mem_insert, mem_singleton] using parallelCarrier_external d y ho hd
    calc
      H.card = (H.map (translation x)).card := (card_map _).symm
      _ ≤ ({0, BitVec.twoPow 5 d.val} : Finset (BitVec 5)).card := card_le_card hsub
      _ ≤ 2 := card_insert_le _ _
  · change H.card ≤ 2
    rw [not_nonempty_iff_eq_empty.mp h, card_empty]
    decide

private def starCarrier (v : BitVec 5) : Finset (BitVec 5) :=
  {0, v} ∪ oddNeighborImage {0, v}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
-- After translation, only the sixteen even displacements of the second center remain.
private theorem star_profile (i : Fin 16)
    (h : (oddNeighborImage {0, evenWord i}).card = 6) :
    (evenWord i).cpop.toNat = 2 ∧
    (∀ j : Fin 32, let y := BitVec.ofFin j
      (y ∈ ({0, evenWord i} : Finset (BitVec 5)) → degree (starCarrier (evenWord i)) y = 3) ∧
      (y ∈ oddNeighborImage {0, evenWord i} → degree (starCarrier (evenWord i)) y = 1) ∧
      (y ∉ starCarrier (evenWord i) → degree (starCarrier (evenWord i)) y ≤ 2)) :=
  (show ∀ i : Fin 16, (oddNeighborImage {0, evenWord i}).card = 6 →
    (evenWord i).cpop.toNat = 2 ∧
    (∀ j : Fin 32, let y := BitVec.ofFin j
      (y ∈ ({0, evenWord i} : Finset (BitVec 5)) → degree (starCarrier (evenWord i)) y = 3) ∧
      (y ∈ oddNeighborImage {0, evenWord i} → degree (starCarrier (evenWord i)) y = 1) ∧
      (y ∉ starCarrier (evenWord i) → degree (starCarrier (evenWord i)) y ≤ 2)) by decide) i h

/-- An eight-point parity-fixed support has either four parallel induced edges or two
three-leaf stars. In the matching case, every external degree is at most four and at
most two external vertices have degree four. In the star case, the centers differ in
two coordinates and every external vertex has degree at most two. -/
theorem eight_point_dichotomy {S : Finset (BitVec 5)} (hS : S.card = 8)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    (∃ d : Fin 5,
      (∀ x ∈ S, ∀ i : Fin 5, (x ^^^ BitVec.twoPow 5 i.val) ∈ S ↔ i = d) ∧
      (∀ x ∈ S, degree S x = 1) ∧
      (∀ x ∉ S, degree S x ≤ 4) ∧
      (∀ B : Finset (BitVec 5), Disjoint S B → (B.filter fun x => degree S x = 4).card ≤ 2)) ∨
    (∃ (p : Bool) (a b : BitVec 5),
      side S p = {a, b} ∧ side S (!p) = oddNeighborImage {a, b} ∧
      (a ^^^ b).cpop.toNat = 2 ∧
      (side S p).card = 2 ∧ (side S (!p)).card = 6 ∧
      (∀ x ∈ side S p, degree S x = 3) ∧
      (∀ x ∈ side S (!p), degree S x = 1) ∧
      (∀ x ∉ S, degree S x ≤ 2)) := by
  rcases parity_sizes hS hpar with ⟨he, ho⟩ | ⟨p, hc, hl⟩
  · obtain ⟨d, _, hflip⟩ := parallel_of_neighborParity_of_card_four_four hpar he ho
    refine Or.inl ⟨d, hflip, fun _ hx => degree_of_parallel hflip hx, ?_, ?_⟩
    · intro x hx
      have hp : degree S x % 2 = 0 := by rw [degree_mod_two, ← hpar x]; simp [hx]
      have hd := degree_le_five S x
      omega
    · intro B hB
      exact parallel_external_card hS hB fun x hx => (hflip x hx d).mpr rfl
  · obtain ⟨a, b, _, heq⟩ := card_eq_two.mp hc
    have him := side_eq_image hpar p
    have hpart : side S p ∪ side S (!p) = S := by
      ext y
      cases p <;> cases hy : bitParity y <;> simp [side, hy]
    have hba : bitParity (b ^^^ a) = false := by
      have ha : bitParity a = p := (mem_filter.mp (show a ∈ side S p by simp [heq])).2
      have hb : bitParity b = p := (mem_filter.mp (show b ∈ side S p by simp [heq])).2
      simp [bitParity_xor, ha, hb]
    have hcenters : (side S p).map (translation a) = {0, b ^^^ a} := by
      rw [heq]
      simp [map_insert]
    have hleaves : (side S (!p)).map (translation a) = oddNeighborImage {0, b ^^^ a} := by
      rw [him, ← oddNeighborImage_translate, hcenters]
    have hcarrier : S.map (translation a) = starCarrier (b ^^^ a) := by
      rw [← hpart, map_union, hcenters, hleaves, starCarrier]
    have hcard : (oddNeighborImage {0, b ^^^ a}).card = 6 := by rw [← hleaves, card_map, hl]
    have hprofile := star_profile ((b ^^^ a).setWidth 4).toFin
    rw [evenWord_decode _ hba] at hprofile
    obtain ⟨hdist, hdegrees⟩ := hprofile hcard
    refine Or.inr ⟨p, a, b, heq, heq ▸ him,
      by simpa only [BitVec.xor_comm a b] using hdist,
      hc, hl, ?_, ?_, ?_⟩
    · intro x hx
      have hm : x ^^^ a ∈ ({0, b ^^^ a} : Finset (BitVec 5)) := by
        rw [← hcenters, mem_translate, xor_cancel]
        exact hx
      have h : degree (starCarrier (b ^^^ a)) (x ^^^ a) = 3 :=
        (hdegrees (x ^^^ a).toFin).1 hm
      simpa only [← hcarrier, degree_translate, xor_cancel] using h
    · intro x hx
      have hm : x ^^^ a ∈ oddNeighborImage {0, b ^^^ a} := by
        rw [← hleaves, mem_translate, xor_cancel]
        exact hx
      have h : degree (starCarrier (b ^^^ a)) (x ^^^ a) = 1 :=
        (hdegrees (x ^^^ a).toFin).2.1 hm
      simpa only [← hcarrier, degree_translate, xor_cancel] using h
    · intro x hx
      have hm : x ^^^ a ∉ starCarrier (b ^^^ a) := by
        rwa [← hcarrier, mem_translate, xor_cancel]
      have h : degree (starCarrier (b ^^^ a)) (x ^^^ a) ≤ 2 :=
        (hdegrees (x ^^^ a).toFin).2.2 hm
      simpa only [← hcarrier, degree_translate, xor_cancel] using h

#print axioms eight_point_dichotomy

/-- Number of neighbors in `S` sharing the label of `x`. -/
def sameLabelDegree {α : Type} [DecidableEq α] (S : Finset (BitVec 5))
    (label : BitVec 5 → α) (x : BitVec 5) : Nat :=
  degree (S.filter fun y => label y = label x) x

private theorem sum_relation_swap (R : BitVec 5 → BitVec 5 → Prop)
    [DecidableRel R] (hsymm : ∀ x y, R x y ↔ R y x) (S T : Finset (BitVec 5)) :
    ∑ x ∈ S, (T.filter (R x)).card = ∑ y ∈ T, (S.filter (R y)).card := by
  calc
    _ = ∑ x ∈ S, (T.bipartiteAbove R x).card := rfl
    _ = ∑ y ∈ T, (S.bipartiteBelow R y).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = _ := by
      apply sum_congr rfl
      intro y _
      unfold bipartiteBelow
      simp_rw [fun x => propext (hsymm x y)]

private theorem sum_degree_swap (S T : Finset (BitVec 5)) :
    ∑ x ∈ S, degree T x = ∑ y ∈ T, degree S y :=
  sum_relation_swap adjacent adjacent_comm S T

private theorem sameLabelDegree_le {α : Type} [DecidableEq α] (S : Finset (BitVec 5))
    (label : BitVec 5 → α) (x : BitVec 5) : sameLabelDegree S label x ≤ degree S x :=
  degree_mono (filter_subset _ _) _

private theorem sameLabelDegree_zero {α : Type} [DecidableEq α] {S : Finset (BitVec 5)}
    {label : BitVec 5 → α} {x : BitVec 5}
    (h : ∀ y ∈ S, adjacent x y → label y ≠ label x) :
    sameLabelDegree S label x = 0 := by
  rw [sameLabelDegree, degree_filter, card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hy, hxy⟩ := mem_filter.mp hy
  obtain ⟨hy, hlabel⟩ := mem_filter.mp hy
  exact h y hy hxy hlabel

private theorem degree_sameSide_zero {S : Finset (BitVec 5)} {x : BitVec 5} {p : Bool}
    (hx : bitParity x = p) : degree (side S p) x = 0 := by
  rw [degree_filter, card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hy, hadj⟩ := mem_filter.mp hy
  have hp : bitParity y = p := (mem_filter.mp hy).2
  have hn := parity_of_adjacent hadj
  rw [hx, hp] at hn
  cases p <;> contradiction

private theorem degree_oppositeSide {S : Finset (BitVec 5)} {x : BitVec 5} {p : Bool}
    (hx : bitParity x = p) : degree (side S (!p)) x = degree S x :=
  degree_congr x fun _ hadj => by simp [side, parity_of_adjacent hadj, hx]

private theorem one_degree_equation {d t q : Nat} {active : Bool}
    (hd : d = 1) (h : d + 2 * t + 2 * q = if active then 5 else 9) :
    t + q = 2 + (if active then 0 else 2) := by
  cases active <;> simp_all <;> omega

private theorem parallel_degree_contradiction {α : Type} [DecidableEq α]
    {S B : Finset (BitVec 5)} {label : BitVec 5 → α} {active : BitVec 5 → Bool}
    {d : Fin 5} (hS : S.card = 8) (hB : B.card = 4)
    (hflip : ∀ x ∈ S, ∀ i : Fin 5, (x ^^^ BitVec.twoPow 5 i.val) ∈ S ↔ i = d)
    (hdeg : ∀ x ∈ S, degree S x = 1)
    (hbound : ∀ x ∈ B, degree S x ≤ 4)
    (hhigh : (B.filter fun x => degree S x = 4).card ≤ 2)
    (hlocal : ∀ x ∈ S, degree S x + 2 * sameLabelDegree S label x + 2 * degree B x =
      if active x then 5 else 9)
    (hactive : ∀ x ∈ S, ∀ y ∈ S, adjacent x y → active x = true → active y = true →
      label x ≠ label y) : False := by
  let k := BitVec.twoPow 5 d.val
  have hpartner (x : BitVec 5) (hx : x ∈ S) : x ^^^ k ∈ S := (hflip x hx d).mpr rfl
  have hpair (x : BitVec 5) (hx : x ∈ S) : 4 ≤ degree B x + degree B (x ^^^ k) := by
    let y := x ^^^ k
    have hy : y ∈ S := hpartner x hx
    have ht (z : BitVec 5) (hz : z ∈ S) : sameLabelDegree S label z ≤ 1 :=
      (sameLabelDegree_le S label z).trans (hdeg z hz).le
    have hq := one_degree_equation (hdeg x hx) (hlocal x hx)
    have hr := one_degree_equation (hdeg y hy) (hlocal y hy)
    change 4 ≤ degree B x + degree B y
    by_cases ha : active x = true
    · by_cases hb : active y = true
      · have zero (u : BitVec 5) (hu : u ∈ S) (hau : active u = true)
            (hp : active (u ^^^ k) = true) : sameLabelDegree S label u = 0 := by
          apply sameLabelDegree_zero
          intro w hw huw
          obtain ⟨i, rfl⟩ := (adjacent_flip u w).mp huw
          have hi := (hflip u hu i).mp hw
          subst i
          exact (hactive u hu _ hw huw hau hp).symm
        have hzx := zero x hx ha hb
        have hzy := zero y hy hb (by simpa only [y, xor_cancel] using ha)
        simp only [ha, hb, ite_true, Nat.add_zero, hzx, hzy, Nat.zero_add] at hq hr
        omega
      · simp [ha] at hq
        simp [hb] at hr
        have htx := ht x hx
        have hty := ht y hy
        omega
    · simp [ha] at hq
      have hr' : 2 ≤ sameLabelDegree S label y + degree B y := by
        cases hb : active y <;> simp [hb] at hr <;> omega
      have htx := ht x hx
      have hty := ht y hy
      omega
  have hmap : S.map (translation k) = S := by
    apply eq_of_subset_of_card_le
    · intro x hx
      rw [mem_translate] at hx
      simpa only [xor_cancel] using hpartner (x ^^^ k) hx
    · rw [card_map]
  have hsum : (∑ x ∈ S, degree B (x ^^^ k)) = ∑ x ∈ S, degree B x := by
    change (∑ x ∈ S, degree B (translation k x)) = _
    rw [← sum_map, hmap]
  have hlower : 16 ≤ ∑ x ∈ S, degree B x := by
    have h := sum_le_sum hpair
    rw [sum_const_nat (fun _ _ => rfl), hS, sum_add_distrib, hsum] at h
    omega
  have hall : ∀ x ∈ B, degree S x = 4 := by
    intro x hx
    have hsum := sum_degree_swap S B
    have hrest : ∑ y ∈ B.erase x, degree S y ≤ 12 := by
      calc
        _ ≤ ∑ _y ∈ B.erase x, 4 := sum_le_sum fun y hy => hbound y (mem_erase.mp hy).2
        _ = 12 := by rw [sum_const_nat (fun _ _ => rfl), card_erase_of_mem hx, hB]
    rw [← sum_erase_add _ _ hx] at hsum
    have hle := hbound x hx
    omega
  rw [filter_eq_self.mpr hall, hB] at hhigh
  omega

private theorem star_degree_contradiction {α : Type} [DecidableEq α]
    {S B : Finset (BitVec 5)} {label : BitVec 5 → α} {active : BitVec 5 → Bool}
    {p : Bool} (hC : (side S p).card = 2) (hL : (side S (!p)).card = 6)
    (hB : B.card = 4) (hdis : Disjoint S B)
    (hcenter : ∀ x ∈ side S p, degree S x = 3)
    (hleaf : ∀ x ∈ side S (!p), degree S x = 1)
    (hout : ∀ x ∉ S, degree S x ≤ 2)
    (hlocal : ∀ x ∈ S, degree S x + 2 * sameLabelDegree S label x + 2 * degree B x =
      if active x then 5 else 9)
    (hactive : ∀ x ∈ S, ∀ y ∈ S, adjacent x y → active x = true → active y = true →
      label x ≠ label y)
    (hlabels : ∀ i, 4 * (S.filter fun x => label x = i).card ≤
      12 + (S.filter fun x => label x = i ∧ active x = true).card) : False := by
  let C := side S p
  let L := side S (!p)
  let t := sameLabelDegree S label
  have hsame (x : BitVec 5) (hx : x ∈ C) : t x ≤ 2 := by
    by_contra! hlarge
    let F := S.filter fun y => label y = label x
    let A := S.filter fun y => label y = label x ∧ active y = true
    have hxF : x ∈ F := mem_filter.mpr ⟨(mem_filter.mp hx).1, rfl⟩
    have hsub : F.filter (adjacent x) ⊆ F.erase x := by
      intro y hy
      obtain ⟨hy, ha⟩ := mem_filter.mp hy
      refine mem_erase.mpr ⟨fun he => ?_, hy⟩
      subst y
      exact (show (0#5 : BitVec 5) ∉ ({1, 2, 4, 8, 16} : Finset (BitVec 5)) by decide)
        (by simpa only [adjacent, BitVec.xor_self] using ha)
    have hle : t x ≤ F.card - 1 := by
      rw [← card_erase_of_mem hxF]
      exact card_le_card hsub
    have hAF : A ⊆ F := fun y hy =>
      mem_filter.mpr ⟨(mem_filter.mp hy).1, (mem_filter.mp hy).2.1⟩
    have hcard := card_le_card hAF
    have hi : 4 * F.card ≤ 12 + A.card := hlabels (label x)
    have heq : F = A := (eq_of_subset_of_card_le hAF (by omega)).symm
    have hax : active x = true :=
      (mem_filter.mp (show x ∈ A from heq ▸ hxF)).2.2
    have hh : t x = 0 := by
      apply sameLabelDegree_zero
      intro y hy hadj hlabel
      have hyF : y ∈ F := mem_filter.mpr ⟨hy, hlabel⟩
      have hay : active y = true :=
        (mem_filter.mp (show y ∈ A from heq ▸ hyF)).2.2
      exact (hactive x (mem_filter.mp hx).1 y hy hadj hax hay) hlabel.symm
    omega
  have htswap : ∑ x ∈ L, t x = ∑ y ∈ C, t y := by
    let R := fun x y => label y = label x ∧ adjacent x y
    have hrow (x : BitVec 5) (q : Bool) (hx : bitParity x = !q) :
        ((side S q).filter (R x)).card = t x := by
      calc
        _ = degree (side (S.filter fun y => label y = label x) q) x := by
          rw [degree_filter]
          congr 1
          ext y
          simp only [side, mem_filter, R]
          tauto
        _ = t x := by
          change _ = degree (S.filter fun y => label y = label x) x
          simpa only [Bool.not_not] using
            (degree_oppositeSide (S := S.filter fun y => label y = label x) hx)
    calc
      _ = ∑ x ∈ L, (C.filter (R x)).card :=
        sum_congr rfl fun x hx => (hrow x p (mem_filter.mp hx).2).symm
      _ = ∑ y ∈ C, (L.filter (R y)).card := by
        apply sum_relation_swap
        intro x y
        exact and_congr eq_comm (adjacent_comm x y)
      _ = _ := sum_congr rfl fun y hy =>
        hrow y (!p) (by simpa only [Bool.not_not] using (mem_filter.mp hy).2)
  have htbound : ∑ x ∈ L, t x ≤ 4 := by
    rw [htswap]
    calc
      _ ≤ ∑ _y ∈ C, 2 := sum_le_sum hsame
      _ = 4 := by rw [sum_const_nat (fun _ _ => rfl), show C.card = 2 from hC]
  have hinc : (∑ x ∈ L, degree B x) ≤ 2 * (side B p).card := by
    have hswap := sum_degree_swap L (side B p)
    have heq : (∑ x ∈ L, degree B x) = ∑ x ∈ L, degree (side B p) x :=
      sum_congr rfl fun x hx => by
        have hp : bitParity x = !p := (mem_filter.mp hx).2
        simpa only [Bool.not_not] using (degree_oppositeSide (S := B) hp).symm
    rw [heq, hswap]
    calc
      _ ≤ ∑ _y ∈ side B p, 2 := sum_le_sum fun y hy =>
        (degree_mono (filter_subset _ _) y).trans
          (hout y fun hys => disjoint_left.mp hdis hys (mem_filter.mp hy).1)
      _ = _ := by rw [sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  have hs : (side B p).card ≤ 4 := hB ▸ card_le_card (filter_subset _ _)
  have hlower : 12 + (∑ x ∈ L, if active x then 0 else 2) =
      (∑ x ∈ L, t x) + ∑ x ∈ L, degree B x := by
    have h := sum_congr (f := fun x => t x + degree B x)
      (g := fun x => 2 + (if active x then 0 else 2)) rfl
      (fun x (hx : x ∈ L) => one_degree_equation (hleaf x hx) (hlocal x (mem_filter.mp hx).1))
    rw [sum_add_distrib, sum_add_distrib, sum_const_nat (fun _ _ => rfl),
      show L.card = 6 from hL] at h
    exact h.symm
  have hfull : side B p = B :=
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have hAL (x : BitVec 5) (hx : x ∈ L) : active x = true := by
    by_contra h
    have hterm := single_le_sum (f := fun x => if active x then 0 else 2)
      (fun _ _ => Nat.zero_le _) hx
    simp [h] at hterm
    omega
  have hAC (x : BitVec 5) (hx : x ∈ C) : active x = true := by
    by_contra h
    have hb : degree B x = 0 := hfull ▸ degree_sameSide_zero (S := B) (mem_filter.mp hx).2
    have hh := hlocal x (mem_filter.mp hx).1
    simp only [hcenter x hx, hb, Nat.mul_zero, Nat.add_zero, ite_eq_right h] at hh
    change 3 + 2 * t x = 9 at hh
    have ht := hsame x hx
    omega
  have hAS (x : BitVec 5) (hx : x ∈ S) : active x = true := by
    by_cases hp : bitParity x = p
    · exact hAC x (mem_filter.mpr ⟨hx, hp⟩)
    · exact hAL x (mem_filter.mpr ⟨hx, by cases p <;> simpa using hp⟩)
  have hz : ∑ x ∈ L, t x = 0 := by
    apply sum_eq_zero
    intro x hx
    have hxs : x ∈ S := (mem_filter.mp hx).1
    exact sameLabelDegree_zero fun y hy ha =>
      (hactive x hxs y hy ha (hAS x hxs) (hAS y hy)).symm
  omega

/-- Eight singleton suffixes and four disjoint balanced suffixes are impossible under
the local degree equations, the active-label adjacency restriction, and the per-label
moment bound. The labels may belong to any type with decidable equality. -/
theorem eight_singletons_impossible {α : Type} [DecidableEq α]
    {S B : Finset (BitVec 5)} {label : BitVec 5 → α} {active : BitVec 5 → Bool}
    (hS : S.card = 8) (hB : B.card = 4) (hdis : Disjoint S B)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x)
    (hlocal : ∀ x ∈ S, degree S x + 2 * sameLabelDegree S label x + 2 * degree B x =
      if active x then 5 else 9)
    (hactive : ∀ x ∈ S, ∀ y ∈ S, adjacent x y → active x = true → active y = true →
      label x ≠ label y)
    (hlabels : ∀ i, 4 * (S.filter fun x => label x = i).card ≤
      12 + (S.filter fun x => label x = i ∧ active x = true).card) : False := by
  rcases eight_point_dichotomy hS hpar with
    ⟨d, hflip, hdeg, hbound, hhigh⟩ | ⟨p, _, _, _, _, _, hC, hL, hcenter, hleaf, hout⟩
  · exact parallel_degree_contradiction hS hB hflip hdeg
      (fun x hx => hbound x fun hs => disjoint_left.mp hdis hs hx) (hhigh B hdis) hlocal hactive
  · exact star_degree_contradiction hC hL hB hdis hcenter hleaf hout hlocal hactive hlabels

#print axioms eight_singletons_impossible


/-- Sum of induced degrees, equal to twice the number of induced cube edges. -/
def inducedDegreeSum (S : Finset (BitVec 5)) : Nat :=
  ∑ x ∈ S, degree S x

private abbrev slice (S : Finset (BitVec 5)) (i : Fin 5) (b : Bool) :=
  S.filter fun x => x.getLsbD i.val = b

private theorem slice_split (S : Finset (BitVec 5)) (i : Fin 5) (b : Bool) :
    Disjoint (slice S i b) (slice S i (!b)) ∧ slice S i b ∪ slice S i (!b) = S := by
  constructor
  · rw [disjoint_left]
    intro x hx hy
    have h := (mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2
    cases b <;> contradiction
  · ext x
    cases b <;> cases hx : x.getLsbD i.val <;>
      simp only [mem_union, mem_filter, hx, Bool.not_false, Bool.not_true] <;> simp

private theorem degree_union {A B : Finset (BitVec 5)} (hd : Disjoint A B) (x : BitVec 5) :
    degree (A ∪ B) x = degree A x + degree B x := by
  simp only [degree_filter, filter_union, card_union_of_disjoint
    (hd.mono (filter_subset _ _) (filter_subset _ _))]

private theorem degreeSum_union {A B : Finset (BitVec 5)} (hd : Disjoint A B) :
    inducedDegreeSum (A ∪ B) =
      inducedDegreeSum A + inducedDegreeSum B + 2 * (∑ x ∈ A, degree B x) := by
  unfold inducedDegreeSum
  rw [sum_union hd]
  simp_rw [degree_union hd, sum_add_distrib]
  rw [← sum_degree_swap A B]
  omega

private theorem bit_flip (x : BitVec 5) (i j : Fin 5) :
    (x ^^^ BitVec.twoPow 5 j.val).getLsbD i.val =
      (x.getLsbD i.val ^^ decide (i = j)) := by
  have h : (BitVec.twoPow 5 j.val).getLsbD i.val = decide (i = j) :=
    (show ∀ i j : Fin 5, (BitVec.twoPow 5 j.val).getLsbD i.val = decide (i = j) by decide) i j
  rw [BitVec.getLsbD_xor, h]

private theorem degree_cross_slice (S : Finset (BitVec 5)) (i : Fin 5) (x : BitVec 5) :
    degree (slice S i (!x.getLsbD i.val)) x =
      if x ^^^ BitVec.twoPow 5 i.val ∈ S then 1 else 0 := by
  have hf : (slice S i (!x.getLsbD i.val)).filter (adjacent x) =
      ({x ^^^ BitVec.twoPow 5 i.val} : Finset (BitVec 5)).filter (· ∈ S) := by
    ext y
    simp only [slice, mem_filter, mem_singleton]
    constructor
    · rintro ⟨⟨hy, hb⟩, ha⟩
      obtain ⟨j, rfl⟩ := (adjacent_flip x y).mp ha
      rw [bit_flip] at hb
      by_cases h : i = j
      · subst j
        exact ⟨rfl, hy⟩
      · cases x.getLsbD i.val <;> simp [h] at hb
    · rintro ⟨rfl, hy⟩
      exact ⟨⟨hy, by simp⟩, (adjacent_flip _ _).mpr ⟨i, rfl⟩⟩
  rw [degree_filter, hf, filter_singleton]
  split <;> simp

private theorem cross_le_card (S : Finset (BitVec 5)) (i : Fin 5) (b : Bool) :
    (∑ x ∈ slice S i b, degree (slice S i (!b)) x) ≤ (slice S i b).card := by
  calc
    _ ≤ ∑ _x ∈ slice S i b, 1 := sum_le_sum fun x hx => by
      have h := degree_cross_slice S i x
      rw [(mem_filter.mp hx).2] at h
      rw [h]
      split <;> decide
    _ = _ := sum_const_nat (fun _ _ => rfl) |>.trans (Nat.mul_one _)

private theorem varying_bit {S : Finset (BitVec 5)} (hS : 2 ≤ S.card) :
    ∃ i : Fin 5, (slice S i false).Nonempty ∧ (slice S i true).Nonempty := by
  obtain ⟨x, y, hx, hy, hxy⟩ := one_lt_card_iff.mp hS
  have hex : ∃ i : Fin 5, x.getLsbD i.val ≠ y.getLsbD i.val :=
    (show ∀ x y : Fin 32, x ≠ y →
      ∃ i : Fin 5, (BitVec.ofFin (w := 5) x).getLsbD i.val ≠
        (BitVec.ofFin (w := 5) y).getLsbD i.val by decide)
      x.toFin y.toFin (fun h => hxy (congrArg BitVec.ofFin h))
  obtain ⟨i, hi⟩ := hex
  cases hb : x.getLsbD i.val <;> cases hc : y.getLsbD i.val
  · exact (hi (hb.trans hc.symm)).elim
  · exact ⟨i, ⟨x, mem_filter.mpr ⟨hx, hb⟩⟩, ⟨y, mem_filter.mpr ⟨hy, hc⟩⟩⟩
  · exact ⟨i, ⟨y, mem_filter.mpr ⟨hy, hc⟩⟩, ⟨x, mem_filter.mpr ⟨hx, hb⟩⟩⟩
  · exact (hi (hb.trans hc.symm)).elim

/-- Small edge-isoperimetric upper bounds through size twelve. -/
private def edgeBound (n : Nat) : Nat :=
  [0, 0, 1, 2, 4, 5, 7, 9, 12, 13, 15, 17, 20][n]?.getD 0

private theorem edgeBound_split {a b : Nat} (h : a + b ≤ 12) :
    edgeBound a + edgeBound b + min a b ≤ edgeBound (a + b) :=
  (show ∀ a b : Fin 13, a.val + b.val ≤ 12 →
    edgeBound a.val + edgeBound b.val + min a.val b.val ≤ edgeBound (a.val + b.val)
    by decide) ⟨a, by omega⟩ ⟨b, by omega⟩ h

private theorem degreeSum_le_table {S : Finset (BitVec 5)} (hS : S.card ≤ 12) :
    inducedDegreeSum S ≤ 2 * edgeBound S.card := by
  suffices ∀ n : Nat, ∀ T : Finset (BitVec 5), T.card = n → n ≤ 12 →
      inducedDegreeSum T ≤ 2 * edgeBound n from this _ S rfl hS
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T ht hn
    by_cases h : 2 ≤ n
    · obtain ⟨i, hA, hB⟩ := varying_bit (show 2 ≤ T.card by omega)
      let A := slice T i false
      let B := slice T i true
      obtain ⟨hd, he⟩ := slice_split T i false
      change Disjoint A B at hd
      change A ∪ B = T at he
      have hsize : A.card + B.card = n := by rw [← card_union_of_disjoint hd, he, ht]
      have hapos : 0 < A.card := card_pos.mpr hA
      have hbpos : 0 < B.card := card_pos.mpr hB
      have ha := ih A.card (by omega) A rfl (by omega)
      have hb := ih B.card (by omega) B rfl (by omega)
      have hc₁ : (∑ x ∈ A, degree B x) ≤ A.card := cross_le_card T i false
      have hc₂ : (∑ x ∈ A, degree B x) ≤ B.card := by
        rw [sum_degree_swap A B]
        exact cross_le_card T i true
      have hc := le_min hc₁ hc₂
      have htable := edgeBound_split (show A.card + B.card ≤ 12 by omega)
      rw [hsize] at htable
      rw [← he, degreeSum_union hd]
      omega
    · have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · rw [card_eq_zero.mp ht]
        simp [inducedDegreeSum]
      · obtain ⟨x, rfl⟩ := card_eq_one.mp ht
        have hz : degree {x} x = 0 := by
          have hnot : ¬ adjacent x x := by simp [adjacent, BitVec.xor_self]
          simp [degree_filter, filter_singleton, hnot]
        simp [inducedDegreeSum, hz]

/-- A twelve-point subset of the five-cube induces at most twenty edges. -/
theorem degree_sum_le_forty_of_card_twelve {S : Finset (BitVec 5)} (hS : S.card = 12) :
    inducedDegreeSum S ≤ 40 := by
  have h := degreeSum_le_table (show S.card ≤ 12 by omega)
  rw [hS] at h
  exact h

#print axioms degree_sum_le_forty_of_card_twelve


private theorem saturated_cross {S : Finset (BitVec 5)} {i : Fin 5} {b : Bool}
    (hsat : (∑ x ∈ slice S i b, degree (slice S i (!b)) x) = (slice S i b).card)
    {x : BitVec 5} (hx : x ∈ slice S i b) :
    degree (slice S i (!b)) x = 1 := by
  let A := slice S i b
  let B := slice S i (!b)
  have hle (y : BitVec 5) (hy : y ∈ A) : degree B y ≤ 1 := by
    have h := degree_cross_slice S i y
    rw [(mem_filter.mp hy).2] at h
    change degree B y = _ at h
    rw [h]
    split <;> decide
  have hrest : (∑ y ∈ A.erase x, degree B y) ≤ A.card - 1 := by
    calc
      _ ≤ ∑ _y ∈ A.erase x, 1 := sum_le_sum fun y hy => hle y (mem_erase.mp hy).2
      _ = _ := by rw [sum_const_nat (fun _ _ => rfl), card_erase_of_mem hx, Nat.mul_one]
  have hpos : 1 ≤ A.card := card_pos.mpr ⟨x, hx⟩
  change (∑ y ∈ A, degree B y) = A.card at hsat
  rw [← sum_erase_add _ _ hx] at hsat
  change (∑ y ∈ A.erase x, degree B y) + degree B x = A.card at hsat
  have h := hle x hx
  change degree B x = 1
  omega

private theorem split_bounds (S : Finset (BitVec 5)) (i : Fin 5) (b : Bool)
    (hS : S.card ≤ 12) :
    let A := slice S i b
    let B := slice S i (!b)
    A.card + B.card = S.card ∧
    inducedDegreeSum S = inducedDegreeSum A + inducedDegreeSum B + 2 * (∑ x ∈ A, degree B x) ∧
    inducedDegreeSum A ≤ 2 * edgeBound A.card ∧
    inducedDegreeSum B ≤ 2 * edgeBound B.card ∧
    (∑ x ∈ A, degree B x) ≤ min A.card B.card := by
  dsimp
  obtain ⟨hd, hu⟩ := slice_split S i b
  refine ⟨by rw [← card_union_of_disjoint hd, hu], ?_, ?_, ?_, ?_⟩
  · rw [← degreeSum_union hd, hu]
  · exact degreeSum_le_table ((card_le_card (filter_subset _ _)).trans hS)
  · exact degreeSum_le_table ((card_le_card (filter_subset _ _)).trans hS)
  · apply le_min (cross_le_card S i b)
    rw [sum_degree_swap]
    simpa only [Bool.not_not] using cross_le_card S i (!b)

private theorem eight_split_saturated {S : Finset (BitVec 5)} {i : Fin 5} {b : Bool}
    (hS : S.card = 8) (hE : inducedDegreeSum S = 24)
    (hA : (slice S i b).Nonempty) (hB : (slice S i (!b)).Nonempty) :
    (∑ x ∈ slice S i b, degree (slice S i (!b)) x) = (slice S i b).card := by
  let A := slice S i b
  let B := slice S i (!b)
  obtain ⟨hn, he, ha, hb, hc⟩ := split_bounds S i b (by omega)
  change A.card + B.card = S.card at hn
  change inducedDegreeSum S = inducedDegreeSum A + inducedDegreeSum B +
    2 * (∑ x ∈ A, degree B x) at he
  change inducedDegreeSum A ≤ 2 * edgeBound A.card at ha
  change inducedDegreeSum B ≤ 2 * edgeBound B.card at hb
  change (∑ x ∈ A, degree B x) ≤ min A.card B.card at hc
  have hapos := card_pos.mpr hA
  have hbpos := card_pos.mpr hB
  change 0 < A.card at hapos
  change 0 < B.card at hbpos
  have htable : ∀ a z : Fin 9, 0 < a.val → 0 < z.val → a.val + z.val = 8 →
      12 ≤ edgeBound a.val + edgeBound z.val + min a.val z.val → a.val = 4 ∧ z.val = 4 :=
    by decide
  have hsum : A.card + B.card = 8 := hn.trans hS
  have ht : 12 ≤ edgeBound A.card + edgeBound B.card + min A.card B.card := by omega
  have hcards : A.card = 4 ∧ B.card = 4 :=
    htable ⟨A.card, by omega⟩ ⟨B.card, by omega⟩ hapos hbpos hsum ht
  obtain ⟨h4, h4'⟩ := hcards
  rw [h4] at ha
  rw [h4'] at hb
  rw [h4, h4'] at hc
  change inducedDegreeSum A ≤ 8 at ha
  change inducedDegreeSum B ≤ 8 at hb
  change (∑ x ∈ A, degree B x) ≤ 4 at hc
  change (∑ x ∈ A, degree B x) = A.card
  omega

private theorem degree_eq_count_directions (S : Finset (BitVec 5)) (x : BitVec 5) :
    degree S x = ((univ : Finset (Fin 5)).filter fun i =>
      x ^^^ BitVec.twoPow 5 i.val ∈ S).card := by
  let flip : Fin 5 ↪ BitVec 5 := ⟨fun i => x ^^^ BitVec.twoPow 5 i.val, by
    intro i j h
    exact (show ∀ i j : Fin 5, BitVec.twoPow 5 i.val = BitVec.twoPow 5 j.val → i = j by decide)
      i j ((BitVec.xor_right_inj x).mp h)⟩
  let D := (univ : Finset (Fin 5)).filter (fun i => flip i ∈ S)
  have hmap : S.filter (adjacent x) = D.map flip := by
    ext y
    simp only [mem_filter, mem_map, adjacent_flip, D, mem_univ, true_and]
    constructor
    · rintro ⟨hy, i, rfl⟩
      exact ⟨i, hy, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i, rfl⟩
  rw [degree_filter, hmap, card_map]
  rfl

private theorem degree_three_of_eight_maximal {S : Finset (BitVec 5)}
    (hS : S.card = 8) (hE : inducedDegreeSum S = 24) :
    ∀ x ∈ S, degree S x = 3 := by
  let V := (univ : Finset (Fin 5)).filter fun i =>
    (slice S i false).Nonempty ∧ (slice S i true).Nonempty
  have hdeg (x : BitVec 5) (hx : x ∈ S) : degree S x = V.card := by
    rw [degree_eq_count_directions]
    congr 1
    ext i
    simp only [V, mem_filter, mem_univ, true_and]
    let b := x.getLsbD i.val
    have hxb : x ∈ slice S i b := mem_filter.mpr ⟨hx, rfl⟩
    have hx' : (x ^^^ BitVec.twoPow 5 i.val).getLsbD i.val = !b := by
      change (x ^^^ BitVec.twoPow 5 i.val).getLsbD i.val = !x.getLsbD i.val
      simp
    constructor
    · intro hh
      have hy : x ^^^ BitVec.twoPow 5 i.val ∈ slice S i (!b) := mem_filter.mpr ⟨hh, hx'⟩
      cases hb : b
      · exact ⟨⟨x, hb ▸ hxb⟩, ⟨_, by simpa only [hb, Bool.not_false] using hy⟩⟩
      · exact ⟨⟨_, by simpa only [hb, Bool.not_true] using hy⟩, ⟨x, hb ▸ hxb⟩⟩
    · rintro ⟨hf, ht⟩
      have hn : (slice S i (!b)).Nonempty := by
        cases hb : b <;> simpa only [hb, Bool.not_false, Bool.not_true]
      have hc := saturated_cross (eight_split_saturated hS hE ⟨x, hxb⟩ hn) hxb
      change degree (slice S i (!x.getLsbD i.val)) x = 1 at hc
      rw [degree_cross_slice] at hc
      split at hc <;> simp_all
  have heq : inducedDegreeSum S = S.card * V.card := sum_const_nat hdeg
  intro x hx
  rw [hdeg x hx]
  rw [hS, hE] at heq
  omega

private theorem degreeSum_eq_two_side (S : Finset (BitVec 5)) :
    inducedDegreeSum S = 2 * (∑ x ∈ side S false, degree S x) := by
  let E := side S false
  let O := side S true
  have hu : E ∪ O = S := by
    ext x
    cases h : bitParity x <;> simp [E, O, side, h]
  have hd : Disjoint E O := disjoint_left.mpr fun _ hx hy =>
    Bool.noConfusion ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)
  have hzeroE : inducedDegreeSum E = 0 :=
    sum_eq_zero fun x hx => degree_sameSide_zero (mem_filter.mp hx).2
  have hzeroO : inducedDegreeSum O = 0 :=
    sum_eq_zero fun x hx => degree_sameSide_zero (mem_filter.mp hx).2
  have heq := degreeSum_union hd
  simp only [hu, hzeroE, hzeroO, Nat.zero_add] at heq
  rw [heq]
  congr 1
  exact sum_congr rfl fun x hx => degree_oppositeSide (mem_filter.mp hx).2

private theorem even_degreeSum_dvd_four {S : Finset (BitVec 5)}
    (heven : ∀ x ∈ S, degree S x % 2 = 0) : inducedDegreeSum S % 4 = 0 := by
  rw [degreeSum_eq_two_side]
  have hsum {T : Finset (BitVec 5)} (h : ∀ x ∈ T, degree S x % 2 = 0) :
      (∑ x ∈ T, degree S x) % 2 = 0 := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert x T hxt ih =>
      rw [sum_insert hxt]
      have hx := h x (mem_insert_self _ _)
      have ht := ih (fun y hy => h y (mem_insert_of_mem hy))
      omega
  have h := hsum (T := side S false) fun x hx => heven x (mem_filter.mp hx).1
  omega

/-- A twelve-point subset with odd induced degrees has at most nineteen induced edges. -/
theorem degree_sum_le_thirty_eight_of_card_twelve_of_odd {S : Finset (BitVec 5)}
    (hS : S.card = 12) (hodd : ∀ x ∈ S, degree S x % 2 = 1) :
    inducedDegreeSum S ≤ 38 := by
  have hupper := degree_sum_le_forty_of_card_twelve hS
  obtain ⟨i, h0, h1⟩ := varying_bit (show 2 ≤ S.card by omega)
  have hsplit (b : Bool) (hb : (slice S i b).card ≤ (slice S i (!b)).card) :
      inducedDegreeSum S ≤ 38 := by
    let A := slice S i b
    let B := slice S i (!b)
    obtain ⟨hd, hu⟩ := slice_split S i b
    change Disjoint A B at hd
    change A ∪ B = S at hu
    obtain ⟨hn, he, ha, hz, hc⟩ := split_bounds S i b (by omega)
    change A.card + B.card = S.card at hn
    change inducedDegreeSum S = inducedDegreeSum A + inducedDegreeSum B +
      2 * (∑ x ∈ A, degree B x) at he
    change inducedDegreeSum A ≤ 2 * edgeBound A.card at ha
    change inducedDegreeSum B ≤ 2 * edgeBound B.card at hz
    change (∑ x ∈ A, degree B x) ≤ min A.card B.card at hc
    change A.card ≤ B.card at hb
    rw [min_eq_left hb] at hc
    have hA : 0 < A.card := by
      cases b
      · exact card_pos.mpr h0
      · exact card_pos.mpr h1
    have hB : 0 < B.card := by
      cases b
      · exact card_pos.mpr h1
      · exact card_pos.mpr h0
    have htv : ∀ a z : Fin 13, 0 < a.val → a.val ≤ z.val → a.val + z.val = 12 →
        20 ≤ edgeBound a.val + edgeBound z.val + a.val →
        (a.val = 4 ∧ z.val = 8) ∨ (a.val = 6 ∧ z.val = 6) := by decide
    by_contra! hgt
    have hs40 : inducedDegreeSum S = 40 := by
      have h := degreeSum_eq_two_side S
      omega
    have hsum : A.card + B.card = 12 := hn.trans hS
    have ht : 20 ≤ edgeBound A.card + edgeBound B.card + A.card := by omega
    have hcases : (A.card = 4 ∧ B.card = 8) ∨ (A.card = 6 ∧ B.card = 6) :=
      htv ⟨A.card, by omega⟩ ⟨B.card, by omega⟩ hA hb hsum ht
    obtain ⟨h4, h8⟩ | ⟨h6, h6'⟩ := hcases
    · rw [h4] at ha hc
      rw [h8] at hz
      change inducedDegreeSum A ≤ 8 at ha
      change inducedDegreeSum B ≤ 24 at hz
      have hm : inducedDegreeSum B = 24 := by omega
      have hsat : (∑ x ∈ A, degree B x) = A.card := by omega
      obtain ⟨x, hx⟩ := card_pos.mp hA
      have hc₁ := saturated_cross hsat hx
      have hflip : x ^^^ BitVec.twoPow 5 i.val ∈ S := by
        have hb := (mem_filter.mp hx).2
        have h := degree_cross_slice S i x
        rw [hb, hc₁] at h
        split at h <;> simp_all
      let y := x ^^^ BitVec.twoPow 5 i.val
      have hy : y ∈ B := mem_filter.mpr ⟨hflip, by
        change (x ^^^ BitVec.twoPow 5 i.val).getLsbD i.val = !b
        rw [bit_flip, (mem_filter.mp hx).2]
        simp⟩
      have hdy := degree_three_of_eight_maximal h8 hm y hy
      have hcy : degree A y = 1 := by
        have h := degree_cross_slice S i y
        rw [(mem_filter.mp hy).2, Bool.not_not] at h
        change degree A y = if y ^^^ BitVec.twoPow 5 i.val ∈ S then 1 else 0 at h
        simpa only [y, xor_cancel, ite_eq_left (mem_filter.mp hx).1] using h
      have hodd' := hodd y (mem_filter.mp hy).1
      rw [← hu, degree_union hd, hdy, hcy] at hodd'
      omega
    · rw [h6] at ha hc
      rw [h6'] at hz
      change inducedDegreeSum A ≤ 14 at ha
      change inducedDegreeSum B ≤ 14 at hz
      have hm : inducedDegreeSum A = 14 := by omega
      have hsat : (∑ x ∈ A, degree B x) = A.card := by omega
      have hE : ∀ x ∈ A, degree A x % 2 = 0 := by
        intro x hx
        have h := hodd x (mem_filter.mp hx).1
        rw [← hu, degree_union hd, saturated_cross hsat hx] at h
        omega
      have h := even_degreeSum_dvd_four hE
      omega
  by_cases h : (slice S i false).card ≤ (slice S i true).card
  · exact hsplit false h
  · exact hsplit true (by simpa only [Bool.not_true] using (Nat.le_of_lt (Nat.lt_of_not_ge h)))

#print axioms degree_sum_le_thirty_eight_of_card_twelve_of_odd


private theorem sum_sameLabelDegree_swap {α : Type} [DecidableEq α] (label : BitVec 5 → α)
    (S T : Finset (BitVec 5)) :
    ∑ x ∈ S, sameLabelDegree T label x = ∑ y ∈ T, sameLabelDegree S label y := by
  simp only [sameLabelDegree, degree_filter, filter_filter]
  apply sum_relation_swap
  intro x y
  exact and_congr eq_comm (adjacent_comm x y)

/-- Twelve singleton suffixes cannot meet the local degree equations with one balanced
suffix, at most two inactive singletons, and distinct inactive labels. The balanced
suffix has six singleton neighbors minus twice the number of inactive singletons. -/
theorem twelve_singletons_impossible {α : Type} [DecidableEq α]
    {S : Finset (BitVec 5)} {v : BitVec 5} {label : BitVec 5 → α} {active : BitVec 5 → Bool}
    (hS : S.card = 12) (hpar : ∀ x, decide (x ∈ S) = neighborParity S x)
    (hlocal : ∀ x ∈ S, degree S x + 2 * sameLabelDegree S label x + 2 * degree {v} x =
      if active x then 5 else 9)
    (hactive : ∀ x ∈ S, ∀ y ∈ S, adjacent x y → active x = true → active y = true →
      label x ≠ label y)
    (hinactive : (S.filter fun x => active x = false).card ≤ 2)
    (hdistinct : Set.InjOn label ↑(S.filter fun x => active x = false))
    (hbalanced : degree S v + 2 * (S.filter fun x => active x = false).card = 6) :
    False := by
  let A := S.filter fun x => active x = true
  let I := S.filter fun x => active x = false
  let t := sameLabelDegree S label
  let q := degree {v}
  have hAI : Disjoint A I := disjoint_left.mpr fun _ hx hy =>
    Bool.noConfusion ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)
  have hu : A ∪ I = S := by
    ext x
    cases hx : active x <;> simp [A, I, hx]
  have hodd (x : BitVec 5) (hx : x ∈ S) : degree S x % 2 = 1 := by
    rw [degree_mod_two, ← hpar x]
    simp [hx]
  have hi (x : BitVec 5) (hx : x ∈ I) : 3 ≤ degree S x := by
    obtain ⟨hs, ha⟩ := mem_filter.mp hx
    have hq : q x ≤ 1 := by
      rw [show q x = degree {v} x from rfl, degree_filter, ← card_singleton v]
      exact card_le_card (filter_subset _ _)
    have ht := sameLabelDegree_le S label x
    have hd := hodd x hs
    have he := hlocal x hs
    change active x = false at ha
    simp only [ha, Bool.false_eq_true, ite_false] at he
    change degree S x + 2 * t x + 2 * q x = 9 at he
    change t x ≤ degree S x at ht
    omega
  have hsplit (x : BitVec 5) : t x = sameLabelDegree A label x + sameLabelDegree I label x := by
    have hd : Disjoint (A.filter fun y => label y = label x) (I.filter fun y => label y = label x) :=
      hAI.mono (filter_subset _ _) (filter_subset _ _)
    have hf := filter_union (p := fun y => label y = label x) A I
    rw [hu] at hf
    change degree (S.filter fun y => label y = label x) x = _
    rw [hf, degree_union hd]
    rfl
  have hzeroA (x : BitVec 5) (hx : x ∈ A) : sameLabelDegree A label x = 0 := by
    apply sameLabelDegree_zero
    intro y hy ha
    exact (hactive x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 ha
      (mem_filter.mp hx).2 (mem_filter.mp hy).2).symm
  have hzeroI (x : BitVec 5) (hx : x ∈ I) : sameLabelDegree I label x = 0 := by
    apply sameLabelDegree_zero
    intro y hy ha hl
    have he := hdistinct (show y ∈ I from hy) (show x ∈ I from hx) hl
    subst y
    simp [adjacent, BitVec.xor_self] at ha
  have hsame : (∑ x ∈ S, t x) = 2 * (∑ x ∈ I, t x) := by
    rw [← hu, sum_union hAI]
    have h1 : (∑ x ∈ A, t x) = ∑ x ∈ A, sameLabelDegree I label x :=
      sum_congr rfl fun x hx => by rw [hsplit, hzeroA x hx, Nat.zero_add]
    have h2 : (∑ x ∈ I, t x) = ∑ x ∈ I, sameLabelDegree A label x :=
      sum_congr rfl fun x hx => by rw [hsplit, hzeroI x hx, Nat.add_zero]
    rw [h1, sum_sameLabelDegree_swap label A I, ← h2]
    omega
  have hq : (∑ x ∈ S, q x) + 2 * I.card = 6 := by
    change (∑ x ∈ S, degree {v} x) + 2 * I.card = 6
    rw [sum_degree_swap, sum_singleton]
    exact hbalanced
  have hcount (T : Finset (BitVec 5)) (a : Bool)
      (hT : ∀ x ∈ T, x ∈ S ∧ active x = a) :
      (∑ x ∈ T, degree S x) + 2 * (∑ x ∈ T, t x) + 2 * (∑ x ∈ T, q x) =
        T.card * (if a then 5 else 9) := by
    have hh : ∀ x ∈ T, degree S x + 2 * t x + 2 * q x = if a then 5 else 9 := by
      intro x hx
      simpa only [(hT x hx).2] using hlocal x (hT x hx).1
    simpa only [sum_add_distrib, mul_sum] using sum_const_nat hh
  have ha := hcount A true fun x hx => mem_filter.mp hx
  have hι := hcount I false fun x hx => mem_filter.mp hx
  have hcard : A.card + I.card = 12 := by rw [← card_union_of_disjoint hAI, hu, hS]
  have hsum_union (f : BitVec 5 → Nat) :
      (∑ x ∈ S, f x) = (∑ x ∈ A, f x) + ∑ x ∈ I, f x := by
    rw [← hu, sum_union hAI]
  have hsum : inducedDegreeSum S + 2 * (∑ x ∈ S, t x) + 2 * (∑ x ∈ S, q x) =
      5 * A.card + 9 * I.card := by
    unfold inducedDegreeSum
    rw [hsum_union (degree S), hsum_union t, hsum_union q]
    simp only [ite_true, Bool.false_eq_true, ite_false] at ha hι
    omega
  have hlow : 3 * I.card ≤ ∑ x ∈ I, degree S x := by
    rw [Nat.mul_comm, ← sum_const_nat (m := 3) (s := I) (fun _ _ => rfl)]
    exact sum_le_sum hi
  have hI : I.card ≤ 2 := hinactive
  have hbound := degree_sum_le_thirty_eight_of_card_twelve_of_odd hS hodd
  simp only [hsame] at hsum
  simp only [Bool.false_eq_true, ite_false] at hι
  omega

#print axioms twelve_singletons_impossible

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SingletonCutObstructions
