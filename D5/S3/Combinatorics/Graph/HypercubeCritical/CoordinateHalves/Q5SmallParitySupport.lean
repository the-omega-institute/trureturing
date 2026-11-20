import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.SymmDiff

/-! A parity support in the five-cube is determined by either coordinate half.
For a half with at most three sites, its opposite is a symmetric difference
of at most three closed radius-one balls in the four-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport

open Finset
open scoped symmDiff

private def occupied {α : Type} [DecidableEq α] (S : Finset α) (x : α) : Bool :=
  decide (x ∈ S)

/-- XOR of the five neighbor indicators in little-endian bit order. -/
def neighborParity (S : Finset (BitVec 5)) (x : BitVec 5) : Bool :=
  decide ((x ^^^ 1) ∈ S) ^^ decide ((x ^^^ 2) ∈ S) ^^ decide ((x ^^^ 4) ∈ S) ^^
    decide ((x ^^^ 8) ∈ S) ^^ decide ((x ^^^ 16) ∈ S)

private def words4 : Finset (BitVec 4) :=
  (univ : Finset (Fin 16)).map ⟨BitVec.ofFin, fun _ _ h => congrArg BitVec.toFin h⟩

@[simp] private theorem mem_words4 (x : BitVec 4) : x ∈ words4 :=
  mem_map.mpr ⟨x.toFin, mem_univ _, rfl⟩

private def half (S : Finset (BitVec 5)) (b : Bool) : Finset (BitVec 4) :=
  words4.filter fun x => BitVec.cons b x ∈ S

@[simp] private theorem mem_half {S : Finset (BitVec 5)} {b : Bool} {x : BitVec 4} :
    x ∈ half S b ↔ BitVec.cons b x ∈ S := by
  simp [half]

private theorem card_halves (S : Finset (BitVec 5)) (b : Bool) :
    (half S b).card + (half S (!b)).card = S.card := by
  have hcard (c : Bool) : (half S c).card = (S.filter fun x => x.msb = c).card := by
    refine card_bij' (fun x _ => BitVec.cons c x) (fun x _ => x.setWidth 4) ?_ ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x hx
      have ⟨hxS, hc⟩ := mem_filter.mp hx
      rw [mem_half, ← hc, BitVec.cons_msb_setWidth]
      exact hxS
    · intro x _
      simp
    · intro x hx
      rw [← (mem_filter.mp hx).2, BitVec.cons_msb_setWidth]
  have hcompl : (S.filter fun x => x.msb = !b) = S.filter (fun x => x.msb ≠ b) := by
    ext x
    simp only [mem_filter, Bool.eq_not]
  rw [hcard b, hcard (!b), hcompl]
  exact card_filter_add_card_filter_not (s := S) _

private def closedParity (f : BitVec 4 → Bool) (x : BitVec 4) : Bool :=
  f x ^^ (f (x ^^^ 1) ^^ f (x ^^^ 2) ^^ f (x ^^^ 4) ^^ f (x ^^^ 8))

private def opposite (A : Finset (BitVec 4)) : Finset (BitVec 4) :=
  words4.filter fun x => closedParity (occupied A) x = true

private theorem opposite_half {S : Finset (BitVec 5)}
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) (b : Bool) :
    half S (!b) = opposite (half S b) := by
  ext x
  have hrow := hpar (BitVec.cons b x)
  unfold neighborParity at hrow
  change decide (BitVec.cons b x ∈ S) =
    (decide ((BitVec.cons b x ^^^ BitVec.cons false 1) ∈ S) ^^
    decide ((BitVec.cons b x ^^^ BitVec.cons false 2) ∈ S) ^^
    decide ((BitVec.cons b x ^^^ BitVec.cons false 4) ∈ S) ^^
    decide ((BitVec.cons b x ^^^ BitVec.cons false 8) ∈ S) ^^
    decide ((BitVec.cons b x ^^^ BitVec.cons true 0) ∈ S)) at hrow
  simp only [BitVec.cons_xor_cons, Bool.xor_false, Bool.xor_true] at hrow
  have cancel : ∀ a t c : Bool, a = (t ^^ c) → c = (a ^^ t) := by decide
  have h := cancel _ _ _ hrow
  simpa [opposite, closedParity, occupied] using congrArg (· = true) h

private theorem opposite_empty : opposite ∅ = ∅ := by
  ext x
  simp [opposite, closedParity, occupied]

private theorem opposite_symmDiff (A B : Finset (BitVec 4)) :
    opposite (A ∆ B) = opposite A ∆ opposite B := by
  have hocc (x : BitVec 4) : occupied (A ∆ B) x = (occupied A x ^^ occupied B x) := by
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
      simp [occupied, mem_symmDiff, ha, hb]
  have hadd (x : BitVec 4) :
      closedParity (occupied (A ∆ B)) x =
        (closedParity (occupied A) x ^^ closedParity (occupied B) x) := by
    simp only [closedParity, hocc, Bool.xor_assoc, Bool.xor_left_comm]
  ext x
  simp only [opposite, mem_symmDiff, mem_filter, mem_words4, true_and, hadd]
  generalize closedParity (occupied A) x = a
  generalize closedParity (occupied B) x = b
  cases a <;> cases b <;> decide

private theorem singleton_symmDiff {α : Type} [DecidableEq α] (A : Finset α) {a : α}
    (ha : a ∉ A) : {a} ∆ A = insert a A := by
  ext x
  by_cases hx : x = a
  · subst x
    simp [mem_symmDiff, ha]
  · simp [mem_symmDiff, hx]

private def ball (a : BitVec 4) : Finset (BitVec 4) :=
  opposite {a}

private theorem mem_ball (a x : BitVec 4) :
    x ∈ ball a ↔ (x ^^^ a) ∈ ({0, 1, 2, 4, 8} : Finset (BitVec 4)) := by
  exact (show ∀ a x : Fin 16,
    BitVec.ofFin x ∈ ball (BitVec.ofFin a) ↔
      (BitVec.ofFin x ^^^ BitVec.ofFin a) ∈ ({0, 1, 2, 4, 8} : Finset (BitVec 4)) by
    decide) a.toFin x.toFin

private theorem xor_cancel {n : Nat} (x a : BitVec n) : x ^^^ a ^^^ a = x := by
  simp [BitVec.xor_assoc]

private theorem xor_involutive {n : Nat} (a : BitVec n) :
    Function.Involutive (fun x => x ^^^ a) := fun x => xor_cancel x a

private def translate {n : Nat} (a : BitVec n) (A : Finset (BitVec n)) : Finset (BitVec n) :=
  A.map ⟨(· ^^^ a), (xor_involutive a).injective⟩

private theorem mem_translate {n : Nat} {a x : BitVec n} {A : Finset (BitVec n)} :
    x ∈ translate a A ↔ (x ^^^ a) ∈ A := by
  rw [translate, mem_map]
  change (∃ y ∈ A, y ^^^ a = x) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [xor_involutive a y] using hy
  · intro h
    exact ⟨x ^^^ a, h, xor_involutive a x⟩

private theorem translate_ball (a b : BitVec 4) :
    translate a (ball b) = ball (b ^^^ a) := by
  ext x
  simp only [mem_translate, mem_ball, BitVec.xor_assoc, BitVec.xor_comm a b]

private theorem translate_symmDiff (a : BitVec 4) (A B : Finset (BitVec 4)) :
    translate a (A ∆ B) = translate a A ∆ translate a B := by
  ext x
  simp only [mem_translate, mem_symmDiff]

private theorem card_translate {n : Nat} (a : BitVec n) (A : Finset (BitVec n)) :
    (translate a A).card = A.card := card_map _

private theorem translated_center_ne_zero {n : Nat} {a b : BitVec n} (hab : a ≠ b) :
    b ^^^ a ≠ 0 := by
  intro h
  apply hab
  apply (xor_involutive a).injective
  change a ^^^ a = b ^^^ a
  simpa using h.symm

-- Translation fixes the first center at zero, so the kernel checks only the remaining sites.
private theorem card_two_balls {a b : BitVec 4} (hab : a ≠ b) :
    6 ≤ (ball a ∆ ball b).card := by
  have check : ∀ b : Fin 16, (BitVec.ofFin b : BitVec 4) ≠ 0 →
      6 ≤ (ball 0 ∆ ball (BitVec.ofFin b)).card := by decide
  rw [← card_translate a (ball a ∆ ball b), translate_symmDiff, translate_ball,
    translate_ball, BitVec.xor_self]
  exact check (b ^^^ a).toFin (translated_center_ne_zero hab)

private theorem card_three_balls {a b c : BitVec 4} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : 7 ≤ (ball a ∆ (ball b ∆ ball c)).card := by
  have check : ∀ b c : Fin 16, (BitVec.ofFin b : BitVec 4) ≠ 0 →
      (BitVec.ofFin c : BitVec 4) ≠ 0 → b ≠ c →
      7 ≤ (ball 0 ∆ (ball (BitVec.ofFin b) ∆ ball (BitVec.ofFin c))).card := by
    decide
  rw [← card_translate a (ball a ∆ (ball b ∆ ball c)), translate_symmDiff,
    translate_symmDiff, translate_ball, translate_ball, translate_ball, BitVec.xor_self]
  refine check (b ^^^ a).toFin (c ^^^ a).toFin
    (translated_center_ne_zero hab) (translated_center_ne_zero hac) ?_
  exact fun h => hbc ((xor_involutive a).injective (congrArg (@BitVec.ofFin 4) h))

private theorem twoPow_split : ∀ i : Fin 5,
    BitVec.twoPow 5 i.val = BitVec.cons (i == 4) (BitVec.twoPow 4 i.val) := by decide

private theorem twoPow_mem_ball_offsets : ∀ i : Fin 5,
    BitVec.twoPow 4 i.val ∈ ({0, 1, 2, 4, 8} : Finset (BitVec 4)) := by decide

private theorem singleton_center_degree {S : Finset (BitVec 5)} {b : Bool} {a : BitVec 4}
    (hsmall : half S b = {a}) (hlarge : half S (!b) = ball a) :
    BitVec.cons (!b) a ∈ S ∧
      ∀ i : Fin 5, (BitVec.cons (!b) a ^^^ BitVec.twoPow 5 i.val) ∈ S := by
  constructor
  · rw [← mem_half, hlarge, mem_ball, BitVec.xor_self]
    simp
  · intro i
    rw [twoPow_split, BitVec.cons_xor_cons]
    by_cases hi : i = 4
    · subst i
      have h : BitVec.twoPow 4 4 = 0 := by decide
      simp [h, ← mem_half, hsmall]
    · have h : (i == 4) = false := by simp [hi]
      rw [h, Bool.xor_false, ← mem_half, hlarge, mem_ball]
      simpa [BitVec.xor_comm a (BitVec.twoPow 4 i.val), BitVec.xor_assoc] using
        twoPow_mem_ball_offsets i

/-- A nonempty parity support in the five-cube with induced degree at most
three has at least eight vertices. The degree counts occupied bit flips. -/
theorem eight_le_card_of_neighborParity {S : Finset (BitVec 5)} (hne : S.Nonempty)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x)
    (hdeg : ∀ x ∈ S, ((univ : Finset (Fin 5)).filter fun i =>
      (x ^^^ BitVec.twoPow 5 i.val) ∈ S).card ≤ 3) :
    8 ≤ S.card := by
  by_contra hlt
  have chooseSide : ∃ b : Bool, (half S b).card ≤ (half S (!b)).card := by
    rcases le_total (half S false).card (half S true).card with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨b, hb⟩ := chooseSide
  have hsum := card_halves S b
  have hopp := opposite_half hpar b
  have hsize : (half S b).card = 0 ∨ (half S b).card = 1 ∨
      (half S b).card = 2 ∨ (half S b).card = 3 := by omega
  rcases hsize with hzero | hone | htwo | hthree
  · rw [card_eq_zero.mp hzero, opposite_empty] at hopp
    have h := hne.card_pos
    rw [hopp, card_empty] at hsum
    omega
  · obtain ⟨a, ha⟩ := card_eq_one.mp hone
    have hball : half S (!b) = ball a := by simpa only [ha, ball] using hopp
    obtain ⟨hmem, hstar⟩ := singleton_center_degree ha hball
    have hd := hdeg _ hmem
    have hfull : (univ : Finset (Fin 5)).filter (fun i =>
        (BitVec.cons (!b) a ^^^ BitVec.twoPow 5 i.val) ∈ S) = univ := by
      ext i
      simp [hstar i]
    rw [hfull, card_univ, Fintype.card_fin] at hd
    omega
  · obtain ⟨a, c, hac, hpair⟩ := card_eq_two.mp htwo
    have hrepl : ({a} : Finset (BitVec 4)) ∆ {c} = {a, c} :=
      singleton_symmDiff _ (by simpa using hac)
    rw [hpair, ← hrepl, opposite_symmDiff] at hopp
    have h := card_two_balls hac
    change 6 ≤ (opposite {a} ∆ opposite {c}).card at h
    rw [← hopp] at h
    omega
  · obtain ⟨a, c, d, hac, had, hcd, htriple⟩ := card_eq_three.mp hthree
    have hrepl : ({a} : Finset (BitVec 4)) ∆ ({c} ∆ {d}) = {a, c, d} := by
      rw [singleton_symmDiff {d} (by simpa using hcd)]
      exact singleton_symmDiff _ (by simp [hac, had])
    rw [htriple, ← hrepl, opposite_symmDiff, opposite_symmDiff] at hopp
    have h := card_three_balls hac had hcd
    change 7 ≤ (opposite {a} ∆ (opposite {c} ∆ opposite {d})).card at h
    rw [← hopp] at h
    omega

#print axioms eight_le_card_of_neighborParity

/-- The bipartition of the five-cube, computed as the XOR of the five coordinates. -/
def bitParity (x : BitVec 5) : Bool :=
  x.getLsbD 0 ^^ x.getLsbD 1 ^^ x.getLsbD 2 ^^ x.getLsbD 3 ^^ x.getLsbD 4

/-- The vertices with an odd number of neighbors in `E`. -/
def oddNeighborImage (E : Finset (BitVec 5)) : Finset (BitVec 5) :=
  ((univ : Finset (Fin 32)).map ⟨BitVec.ofFin, fun _ _ h => congrArg BitVec.toFin h⟩).filter
    fun x => neighborParity E x = true

@[simp] theorem mem_oddNeighborImage {E : Finset (BitVec 5)} {x : BitVec 5} :
    x ∈ oddNeighborImage E ↔ neighborParity E x = true := by
  have hx : x ∈ (univ : Finset (Fin 32)).map
      ⟨BitVec.ofFin, fun _ _ h => congrArg (BitVec.toFin (w := 5)) h⟩ :=
    mem_map.mpr ⟨x.toFin, mem_univ _, rfl⟩
  simp [oddNeighborImage, hx]

private theorem xor_swap (x a b : BitVec 5) :
    x ^^^ a ^^^ b = x ^^^ b ^^^ a := by
  simp only [BitVec.xor_assoc, BitVec.xor_comm a b]

private theorem oddNeighborImage_translate (a : BitVec 5) (E : Finset (BitVec 5)) :
    oddNeighborImage (translate a E) = translate a (oddNeighborImage E) := by
  ext x
  simp only [mem_translate, mem_oddNeighborImage, neighborParity]
  rw [xor_swap x 1 a, xor_swap x 2 a, xor_swap x 4 a, xor_swap x 8 a, xor_swap x 16 a]

private theorem bitParity_xor (x y : BitVec 5) :
    bitParity (x ^^^ y) = (bitParity x ^^ bitParity y) := by
  simp only [bitParity, BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm]

private def evenWord (i : Fin 16) : BitVec 5 :=
  BitVec.cons (bitParity ((BitVec.ofFin (w := 4) i).setWidth 5)) (BitVec.ofFin i)

private theorem evenWord_decode (x : BitVec 5) (hx : bitParity x = false) :
    evenWord (x.setWidth 4).toFin = x :=
  (show ∀ i : Fin 32, bitParity (BitVec.ofFin i) = false →
    evenWord ((BitVec.ofFin (w := 5) i).setWidth 4).toFin = BitVec.ofFin i by decide) x.toFin hx

private theorem direction_injective : Function.Injective (fun i : Fin 5 => BitVec.twoPow 5 i.val) :=
  show ∀ i j : Fin 5, BitVec.twoPow 5 i.val = BitVec.twoPow 5 j.val → i = j by decide

-- Bit x records occupancy of vertex x. XOR of neighborhoods gives their odd support.
private def vertexMask (x : BitVec 5) : BitVec 32 :=
  BitVec.twoPow 32 x.toNat

private def neighborhoodMask (x : BitVec 5) : BitVec 32 :=
  vertexMask (x ^^^ 1) ^^^ vertexMask (x ^^^ 2) ^^^ vertexMask (x ^^^ 4) ^^^
    vertexMask (x ^^^ 8) ^^^ vertexMask (x ^^^ 16)

private theorem vertexMask_bit (x y : BitVec 5) :
    (vertexMask x).getLsbD y.toNat = decide (x = y) := by
  simp [vertexMask, BitVec.getLsbD_twoPow, x.isLt, BitVec.toNat_inj]

private theorem neighborhoodMask_dir (x : BitVec 5) (i : Fin 5) :
    (neighborhoodMask x).getLsbD (x ^^^ BitVec.twoPow 5 i.val).toNat = true :=
  (show ∀ (j : Fin 32) (i : Fin 5),
    (neighborhoodMask (BitVec.ofFin j)).getLsbD
      (BitVec.ofFin j ^^^ BitVec.twoPow 5 i.val).toNat = true by decide) x.toFin i

private theorem neighborhoodMask_bit (x y : BitVec 5) :
    (neighborhoodMask x).getLsbD y.toNat = neighborParity {x} y := by
  have swap (k : BitVec 5) : (x ^^^ k = y) ↔ (y ^^^ k = x) :=
    ⟨fun h => h ▸ xor_involutive k x, fun h => h ▸ xor_involutive k y⟩
  simp only [neighborhoodMask, BitVec.getLsbD_xor, vertexMask_bit, neighborParity,
    mem_singleton, swap]

private theorem neighborParity_symmDiff (A B : Finset (BitVec 5)) (x : BitVec 5) :
    neighborParity (A ∆ B) x = (neighborParity A x ^^ neighborParity B x) := by
  have hocc (y : BitVec 5) : decide (y ∈ A ∆ B) = (decide (y ∈ A) ^^ decide (y ∈ B)) := by
    by_cases ha : y ∈ A <;> by_cases hb : y ∈ B <;> simp [mem_symmDiff, ha, hb]
  simp only [neighborParity, hocc, Bool.xor_assoc, Bool.xor_left_comm]

private def quartetMask (a b c z : BitVec 5) : BitVec 32 :=
  neighborhoodMask a ^^^ neighborhoodMask b ^^^ neighborhoodMask c ^^^ neighborhoodMask z

private theorem quartetMask_bit {a b c z : BitVec 5}
    (ha : a ∉ ({b, c, z} : Finset (BitVec 5))) (hb : b ∉ ({c, z} : Finset (BitVec 5)))
    (hc : c ≠ z) (y : BitVec 5) :
    (quartetMask a b c z).getLsbD y.toNat = neighborParity {a, b, c, z} y := by
  simp only [quartetMask, BitVec.getLsbD_xor, neighborhoodMask_bit, Bool.xor_assoc]
  rw [← singleton_symmDiff _ ha, ← singleton_symmDiff _ hb,
    ← singleton_symmDiff {z} (by simpa using hc)]
  simp only [neighborParity_symmDiff]

private theorem card_mask_bits (m : BitVec 32) (n : Nat) :
    ((univ : Finset (Fin n)).filter fun i => m.getLsbD i.val = true).card =
      m.cpopNatRec n 0 := by
  induction n with
  | zero => simp [BitVec.cpopNatRec]
  | succ n ih =>
    rw [Fin.univ_castSuccEmb, filter_cons, apply_ite Finset.card, card_cons, filter_map, card_map]
    change (if m.getLsbD n = true then (filter (fun i : Fin n =>
      m.getLsbD i.val = true) univ).card + 1 else (filter (fun i : Fin n =>
      m.getLsbD i.val = true) univ).card) = _
    rw [ih, BitVec.cpopNatRec_succ, BitVec.cpopNatRec_add (acc := 0)]
    cases m.getLsbD n <;> simp

private abbrev hasOnlyFlip (m : BitVec 32) (x : BitVec 5) (d : Fin 5) : Prop :=
  (m &&& neighborhoodMask x) = vertexMask (x ^^^ BitVec.twoPow 5 d.val)

private theorem hasOnlyFlip_decode {m : BitVec 32} {x : BitVec 5} {d : Fin 5}
    (h : hasOnlyFlip m x d) (i : Fin 5) :
    m.getLsbD (x ^^^ BitVec.twoPow 5 i.val).toNat = true ↔ i = d := by
  have hbit := congrArg (fun w : BitVec 32 =>
    w.getLsbD (x ^^^ BitVec.twoPow 5 i.val).toNat) h
  rw [BitVec.getLsbD_and, neighborhoodMask_dir, Bool.and_true, vertexMask_bit] at hbit
  rw [hbit, decide_eq_true_eq, BitVec.xor_right_inj, direction_injective.eq_iff, eq_comm]

private def translatedQuartetMask (a b c z : BitVec 5) (d : Fin 5) : BitVec 32 :=
  let k := BitVec.twoPow 5 d.val
  vertexMask (a ^^^ k) ||| vertexMask (b ^^^ k) ||| vertexMask (c ^^^ k) |||
    vertexMask (z ^^^ k)

private theorem translatedQuartetMask_bit (a b c z y : BitVec 5) (d : Fin 5) :
    (translatedQuartetMask a b c z d).getLsbD y.toNat = true ↔
      y ∈ translate (BitVec.twoPow 5 d.val) {a, b, c, z} := by
  have swap (x k : BitVec 5) : (x ^^^ k = y) ↔ (y ^^^ k = x) :=
    ⟨fun h => h ▸ xor_involutive k x, fun h => h ▸ xor_involutive k y⟩
  simp only [translatedQuartetMask, BitVec.getLsbD_or, vertexMask_bit, Bool.or_eq_true,
    decide_eq_true_eq, mem_translate, mem_insert, mem_singleton, swap]
  tauto

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks a 16 × 16 × 16 table after translating the first point to zero.
private theorem normalizedQuartet_table : ∀ i j k : Fin 16,
    i ≠ 0 → j ≠ 0 → k ≠ 0 → i ≠ j → i ≠ k → j ≠ k →
    let b := evenWord i
    let c := evenWord j
    let z := evenWord k
    let m := quartetMask 0 b c z
    m.cpopNatRec 32 0 = 4 →
    ∃ d : Fin 5, m = translatedQuartetMask 0 b c z d ∧
      hasOnlyFlip m 0 d ∧ hasOnlyFlip m b d ∧ hasOnlyFlip m c d ∧ hasOnlyFlip m z d := by
  decide

private theorem normalizedQuartet {b c z : BitVec 5}
    (hb : bitParity b = false) (hc : bitParity c = false) (hz : bitParity z = false)
    (h0b : b ≠ 0) (h0c : c ≠ 0) (h0z : z ≠ 0)
    (hbc : b ≠ c) (hbz : b ≠ z) (hcz : c ≠ z)
    (hcard : (oddNeighborImage {0, b, c, z}).card = 4) :
    ∃ d : Fin 5, oddNeighborImage {0, b, c, z} =
      translate (BitVec.twoPow 5 d.val) {0, b, c, z} ∧
      ∀ x ∈ ({0, b, c, z} : Finset (BitVec 5)), ∀ i : Fin 5,
        (x ^^^ BitVec.twoPow 5 i.val) ∈ oddNeighborImage {0, b, c, z} ↔ i = d := by
  let i := (b.setWidth 4).toFin
  let j := (c.setWidth 4).toFin
  let k := (z.setWidth 4).toFin
  have hi : evenWord i = b := evenWord_decode b hb
  have hj : evenWord j = c := evenWord_decode c hc
  have hk : evenWord k = z := evenWord_decode z hz
  have hi0 : i ≠ 0 := fun h => h0b (hi.symm.trans (congrArg evenWord h))
  have hj0 : j ≠ 0 := fun h => h0c (hj.symm.trans (congrArg evenWord h))
  have hk0 : k ≠ 0 := fun h => h0z (hk.symm.trans (congrArg evenWord h))
  have hij : i ≠ j := fun h => hbc (hi.symm.trans ((congrArg evenWord h).trans hj))
  have hik : i ≠ k := fun h => hbz (hi.symm.trans ((congrArg evenWord h).trans hk))
  have hjk : j ≠ k := fun h => hcz (hj.symm.trans ((congrArg evenWord h).trans hk))
  have hbit (y : BitVec 5) :
      (quartetMask 0 b c z).getLsbD y.toNat = neighborParity {0, b, c, z} y :=
    quartetMask_bit (by simp only [mem_insert, mem_singleton, not_or]; exact
      ⟨Ne.symm h0b, Ne.symm h0c, Ne.symm h0z⟩)
      (by simp [hbc, hbz]) hcz y
  have hcount : (quartetMask 0 b c z).cpopNatRec 32 0 = 4 := by
    rw [← card_mask_bits, ← hcard, oddNeighborImage, filter_map, card_map]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact Iff.of_eq (congrArg (· = true) (hbit (BitVec.ofFin x)))
  have h := normalizedQuartet_table i j k hi0 hj0 hk0 hij hik hjk
  dsimp only at h
  rw [hi, hj, hk] at h
  obtain ⟨d, hmask, hzero, hbflip, hcflip, hzflip⟩ := h hcount
  refine ⟨d, ?_, ?_⟩
  · ext y
    rw [mem_oddNeighborImage, ← hbit, hmask, translatedQuartetMask_bit]
  · intro x hx l
    rw [mem_oddNeighborImage, ← hbit]
    have hflip : hasOnlyFlip (quartetMask 0 b c z) x d := by
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [hzero, hbflip, hcflip, hzflip]
    exact hasOnlyFlip_decode hflip l

/-- A same-parity quartet with a four-point odd-neighbor image has a
parallel matching to that image, and these are all edges between the two sides. -/
theorem oddNeighborImage_eq_image_xor_of_card_four {E : Finset (BitVec 5)} {p : Bool}
    (hE : E.card = 4) (hp : ∀ x ∈ E, bitParity x = p)
    (hO : (oddNeighborImage E).card = 4) :
    ∃ d : Fin 5, oddNeighborImage E = E.image (fun x => x ^^^ BitVec.twoPow 5 d.val) ∧
      ∀ x ∈ E, ∀ i : Fin 5,
        (x ^^^ BitVec.twoPow 5 i.val) ∈ oddNeighborImage E ↔ i = d := by
  obtain ⟨a, b, c, z, hab, hac, haz, hbc, hbz, hcz, hEeq⟩ := card_eq_four.mp hE
  have ha : a ∈ E := by simp [hEeq]
  have evenTranslated (x : BitVec 5) (hx : x ∈ E) : bitParity (x ^^^ a) = false := by
    simp [bitParity_xor, hp x hx, hp a ha]
  have hnorm : translate a E = {0, b ^^^ a, c ^^^ a, z ^^^ a} := by
    rw [hEeq]
    simp [translate, map_insert]
  have hcount : (oddNeighborImage {0, b ^^^ a, c ^^^ a, z ^^^ a}).card = 4 := by
    rw [← hnorm, oddNeighborImage_translate, card_translate, hO]
  obtain ⟨d, htrans, hflip⟩ := normalizedQuartet
    (evenTranslated b (by simp [hEeq])) (evenTranslated c (by simp [hEeq]))
    (evenTranslated z (by simp [hEeq])) (translated_center_ne_zero hab)
    (translated_center_ne_zero hac) (translated_center_ne_zero haz)
    (fun h => hbc ((BitVec.xor_left_inj a).mp h))
    (fun h => hbz ((BitVec.xor_left_inj a).mp h))
    (fun h => hcz ((BitVec.xor_left_inj a).mp h)) hcount
  rw [← hnorm, oddNeighborImage_translate] at htrans hflip
  have hmap : translate (BitVec.twoPow 5 d.val) E =
      E.image (fun x => x ^^^ BitVec.twoPow 5 d.val) := map_eq_image _ _
  refine ⟨d, ?_, ?_⟩
  · rw [← hmap]
    ext y
    have hy := Iff.of_eq (congrArg (fun T : Finset (BitVec 5) => (y ^^^ a) ∈ T) htrans)
    simpa only [mem_translate, xor_swap y a, xor_cancel] using hy
  · intro x hx i
    have ht : x ^^^ a ∈ translate a E := mem_translate.mpr (by simpa only [xor_cancel] using hx)
    simpa only [mem_translate, xor_swap x a, xor_cancel] using hflip _ ht i

private theorem bitParity_flip (x : BitVec 5) (i : Fin 5) :
    bitParity (x ^^^ BitVec.twoPow 5 i.val) = !bitParity x := by
  have h : ∀ d : Fin 5, bitParity (BitVec.twoPow 5 d.val) = true := by decide
  rw [bitParity_xor, h i, Bool.xor_true]

private theorem neighborParity_even_filter (S : Finset (BitVec 5)) (x : BitVec 5) :
    neighborParity (S.filter fun y => bitParity y = false) x =
      if bitParity x then neighborParity S x else false := by
  have units : bitParity 1#5 = true ∧ bitParity 2#5 = true ∧ bitParity 4#5 = true ∧
      bitParity 8#5 = true ∧ bitParity 16#5 = true := by decide
  obtain ⟨h1, h2, h4, h8, h16⟩ := units
  cases hx : bitParity x <;>
    simp [neighborParity, mem_filter, bitParity_xor, hx, h1, h2, h4, h8, h16]

/-- A parity-fixed support with four vertices on each side of the bipartition
has exactly four induced edges, all in one direction. -/
theorem parallel_of_neighborParity_of_card_four_four {S : Finset (BitVec 5)}
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x)
    (hE : (S.filter fun x => bitParity x = false).card = 4)
    (hO : (S.filter fun x => bitParity x = true).card = 4) :
    ∃ d : Fin 5,
      (S.filter fun x => bitParity x = true) =
        (S.filter fun x => bitParity x = false).image (fun x => x ^^^ BitVec.twoPow 5 d.val) ∧
      ∀ x ∈ S, ∀ i : Fin 5, (x ^^^ BitVec.twoPow 5 i.val) ∈ S ↔ i = d := by
  let E := S.filter fun x => bitParity x = false
  let O := S.filter fun x => bitParity x = true
  have hOE : oddNeighborImage E = O := by
    ext x
    rw [mem_oddNeighborImage, neighborParity_even_filter, ← hpar x]
    cases hx : bitParity x <;> simp [O, hx]
  obtain ⟨d, hd, hflip⟩ := oddNeighborImage_eq_image_xor_of_card_four hE
    (fun _ hx => (mem_filter.mp hx).2) (hOE.symm ▸ hO)
  rw [hOE] at hd hflip
  refine ⟨d, hd, ?_⟩
  intro x hx i
  cases hp : bitParity x with
  | false =>
    have he : x ∈ E := mem_filter.mpr ⟨hx, hp⟩
    simpa [O, bitParity_flip, hp] using hflip x he i
  | true =>
    have ho : x ∈ O := mem_filter.mpr ⟨hx, hp⟩
    constructor
    · intro hy
      let y := x ^^^ BitVec.twoPow 5 i.val
      have he : y ∈ E := mem_filter.mpr ⟨hy, by simp [y, bitParity_flip, hp]⟩
      apply (hflip y he i).mp
      simpa only [y, xor_cancel] using ho
    · rintro rfl
      rw [hd] at ho
      obtain ⟨y, hy, rfl⟩ := mem_image.mp ho
      simpa only [xor_cancel] using (mem_filter.mp hy).1

#print axioms oddNeighborImage_eq_image_xor_of_card_four

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport
