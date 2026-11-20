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

private theorem xor_involutive (a : BitVec 4) :
    Function.Involutive (fun x => x ^^^ a) := by
  intro x
  simp [BitVec.xor_assoc]

private def translate (a : BitVec 4) (A : Finset (BitVec 4)) : Finset (BitVec 4) :=
  A.map ⟨(· ^^^ a), (xor_involutive a).injective⟩

private theorem mem_translate {a x : BitVec 4} {A : Finset (BitVec 4)} :
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

private theorem card_translate (a : BitVec 4) (A : Finset (BitVec 4)) :
    (translate a A).card = A.card := card_map _

private theorem translated_center_ne_zero {a b : BitVec 4} (hab : a ≠ b) :
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

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport
