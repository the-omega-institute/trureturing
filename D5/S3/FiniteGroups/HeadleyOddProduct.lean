/- GID: D5/S3/FiniteGroups/HeadleyOddProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyOddProduct
   mirror-E: none(waiver:pure-mathematical-odd-product)
   anchors: []
   utility: none
   digest: Inverse-pair surgery and the Gordon return construct the arbitrary odd R-star product. -/

import D5.S3.FiniteGroups.HeadleyOddRows
import D5.S3.FiniteGroups.HeadleyExtension

/-! An actual source permutation and its inverse on the difference inventory.
The inverse-pair gadget is reused from the accepted native Headley construction;
its return uses Gordon predecessor, not an additive generator of the odd group. -/

noncomputable section

namespace D5.S3.FiniteGroups.HeadleyOddProduct

open Gordon HeadleyOddRows HeadleyExtension

attribute [local instance] Classical.propDecidable

variable {X : Type*} [AddCommGroup X] [Finite X]

/-- Internal orientation of each nonzero negation pair, chosen using existing bounded rank. -/
private def positive (ds : List OddRadix) (h : Box ds) : Prop :=
  rank ds h < rank ds (-h)

private theorem positive_zero (ds : List OddRadix) : ¬ positive ds 0 := by
  simp [positive]

private theorem positive_ne_zero {ds : List OddRadix} {h : Box ds}
    (hh : positive ds h) : h ≠ 0 := by
  rintro rfl
  exact positive_zero ds hh

private theorem positive_neg {ds : List OddRadix} {h : Box ds} (hh : h ≠ 0) :
    positive ds (-h) ↔ ¬ positive ds h := by
  have hn : h ≠ -h := by
    intro he
    apply hh
    apply box_two_injective ds
    calc
      h + h = h + -h := congrArg (h + ·) he
      _ = 0 + 0 := by simp
  have hr : rank ds h ≠ rank ds (-h) := by
    intro he
    apply hn
    apply (rankEquiv ds).injective
    exact Fin.ext he
  simp only [positive, neg_neg]
  omega

private def columnTurn (r : RStar X) : Equiv.Perm X :=
  Equiv.swap r.a r.b * Equiv.swap r.a 0

private theorem turn_a (r : RStar X) : columnTurn r r.a = 0 := by
  classical
  change Equiv.swap r.a r.b (Equiv.swap r.a 0 r.a) = 0
  rw [Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne r.a_ne_zero.symm r.b_ne_zero.symm]

private theorem turn_zero (r : RStar X) : columnTurn r 0 = r.b := by
  classical
  simp [columnTurn, Equiv.Perm.mul_apply, r.a_ne_zero]

private theorem turn_b (r : RStar X) : columnTurn r r.b = r.a := by
  classical
  change Equiv.swap r.a r.b (Equiv.swap r.a 0 r.b) = r.a
  rw [Equiv.swap_apply_of_ne_of_ne r.pairwise_distinct.1.symm r.b_ne_zero,
    Equiv.swap_apply_right]

private theorem turn_other (r : RStar X) (x : X)
    (ha : x ≠ r.a) (hb : x ≠ r.b) (hz : x ≠ 0) : columnTurn r x = x := by
  classical
  simp [columnTurn, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne ha hz,
    Equiv.swap_apply_of_ne_of_ne ha hb]

private theorem turn_c (r : RStar X) : columnTurn r r.c = r.c :=
  turn_other r _ r.pairwise_distinct.2.1.symm r.pairwise_distinct.2.2.symm r.c_ne_zero

private theorem turn_inv_a (r : RStar X) : (columnTurn r).symm r.a = r.b :=
  (columnTurn r).symm_apply_eq.mpr (turn_b r).symm

private theorem turn_inv_b (r : RStar X) : (columnTurn r).symm r.b = 0 :=
  (columnTurn r).symm_apply_eq.mpr (turn_zero r).symm

private theorem turn_inv_zero (r : RStar X) : (columnTurn r).symm 0 = r.a :=
  (columnTurn r).symm_apply_eq.mpr (turn_a r).symm

private theorem turn_inv_other (r : RStar X) (x : X)
    (ha : x ≠ r.a) (hb : x ≠ r.b) (hz : x ≠ 0) : (columnTurn r).symm x = x :=
  (columnTurn r).symm_apply_eq.mpr (turn_other r x ha hb hz).symm

private theorem difference_zero (r : RStar X) : r.difference 0 = 0 := by
  rw [r.difference_spec, r.successor_zero, sub_self]

private theorem difference_a (r : RStar X) : r.difference r.a = r.c := by
  rw [r.difference_spec, r.successor_a, ← r.triple_sum]
  abel

private theorem difference_b (r : RStar X) : r.difference r.b = -r.a := by
  rw [r.difference_spec, r.successor_b, ← r.triple_sum]
  abel

/-- The source three-cycle and its inverse exactly permute the actual old labels. -/
private theorem turn_difference (r : RStar X) (x : X) :
    r.successor (columnTurn r x) - x = r.difference ((columnTurn r).symm x) := by
  classical
  by_cases ha : x = r.a
  · subst x
    rw [turn_a, turn_inv_a, r.successor_zero, difference_b, zero_sub]
  by_cases hb : x = r.b
  · subst x
    rw [turn_b, turn_inv_b, r.successor_a, difference_zero, sub_self]
  by_cases hz : x = 0
  · subst x
    rw [turn_zero, turn_inv_zero, r.successor_b, difference_a, sub_zero]
  rw [turn_other r x ha hb hz, turn_inv_other r x ha hb hz, r.difference_spec]

private def rowLift (r : RStar X) (ds : List OddRadix) (x : X) : Equiv.Perm (Box ds) :=
  if x = r.c then rowOne ds else rowZero ds

private def deltaLift (r : RStar X) (ds : List OddRadix) (x : X) : Equiv.Perm (Box ds) :=
  if x = r.c then deltaOne ds else deltaZero ds

private theorem delta_lift_spec (r : RStar X) (ds : List OddRadix) (x : X) (h : Box ds) :
    deltaLift r ds x h = rowLift r ds x h - h := by
  classical
  by_cases hx : x = r.c
  · simp only [deltaLift, rowLift, if_pos hx]
    exact delta_one_spec ds h
  · simp only [deltaLift, rowLift, if_neg hx]
    exact delta_zero_spec ds h

private def sourceTurn (r : RStar X) (ds : List OddRadix) : Equiv.Perm (X × Box ds) :=
  Equiv.prodCongrLeft (fun h => if positive ds h then columnTurn r else Equiv.refl X)

private def ordinarySuccessor (r : RStar X) (ds : List OddRadix) :
    Equiv.Perm (X × Box ds) :=
  (Equiv.prodCongrRight (rowLift r ds)).trans
    (r.successor.prodCongr (Equiv.refl _))

private def ordinaryDifference (r : RStar X) (ds : List OddRadix) :
    Equiv.Perm (X × Box ds) :=
  (Equiv.prodCongrRight (deltaLift r ds)).trans
    (r.difference.prodCongr (Equiv.refl _))

/-- Actual successor; both inverse laws follow from the displayed composed equivalences. -/
def successor (r : RStar X) (ds : List OddRadix) : Equiv.Perm (X × Box ds) :=
  (sourceTurn r ds).trans (ordinarySuccessor r ds)

/-- Actual difference permutation, using the inverse source three-cycle. -/
def difference (r : RStar X) (ds : List OddRadix) : Equiv.Perm (X × Box ds) :=
  (sourceTurn r ds).symm.trans (ordinaryDifference r ds)

private theorem successor_positive (r : RStar X) (ds : List OddRadix)
    (x : X) (h : Box ds) (hp : positive ds h) :
    successor r ds (x, h) = (r.successor (columnTurn r x), rowLift r ds (columnTurn r x) h) := by
  simp [successor, sourceTurn, ordinarySuccessor, hp]

private theorem difference_positive (r : RStar X) (ds : List OddRadix)
    (x : X) (h : Box ds) (hp : positive ds h) :
    difference r ds (x, h) = (r.difference ((columnTurn r).symm x),
      deltaLift r ds ((columnTurn r).symm x) h) := by
  simp [difference, sourceTurn, ordinaryDifference, hp]

private theorem successor_negative (r : RStar X) (ds : List OddRadix)
    (x : X) (h : Box ds) (hp : ¬ positive ds h) :
    successor r ds (x, h) = (r.successor x, rowLift r ds x h) := by
  simp [successor, sourceTurn, ordinarySuccessor, hp]

private theorem difference_negative (r : RStar X) (ds : List OddRadix)
    (x : X) (h : Box ds) (hp : ¬ positive ds h) :
    difference r ds (x, h) = (r.difference x, deltaLift r ds x h) := by
  simp [difference, sourceTurn, ordinaryDifference, hp]

/-- Every original product-coordinate edge, including seams, has its coefficient-one label. -/
theorem difference_spec (r : RStar X) (ds : List OddRadix) (v : X × Box ds) :
    difference r ds v = successor r ds v - v := by
  classical
  rcases v with ⟨x, h⟩
  by_cases hp : positive ds h
  · have htc : columnTurn r x = r.c ↔ x = r.c := by
      calc
        columnTurn r x = r.c ↔ columnTurn r x = columnTurn r r.c := by rw [turn_c]
        _ ↔ x = r.c := (columnTurn r).apply_eq_iff_eq
    have htic : (columnTurn r).symm x = r.c ↔ x = r.c := by
      rw [(columnTurn r).symm_apply_eq]
      rw [turn_c]
    rw [difference_positive r ds x h hp, successor_positive r ds x h hp]
    apply Prod.ext
    · change r.difference ((columnTurn r).symm x) = r.successor (columnTurn r x) - x
      exact (turn_difference r x).symm
    · change deltaLift r ds ((columnTurn r).symm x) h = rowLift r ds (columnTurn r x) h - h
      simp only [deltaLift, rowLift, htic, htc]
      split_ifs <;> first | exact delta_one_spec ds h | exact delta_zero_spec ds h
  · rw [difference_negative r ds x h hp, successor_negative r ds x h hp]
    exact Prod.ext (r.difference_spec x) (delta_lift_spec r ds x h)

private theorem successor_ordinary (r : RStar X) (ds : List OddRadix) (x : X)
    (ha : x ≠ r.a) (hb : x ≠ r.b) (hz : x ≠ 0) (h : Box ds) :
    successor r ds (x, h) = (r.successor x, rowLift r ds x h) := by
  classical
  by_cases hp : positive ds h <;>
    simp [successor, sourceTurn, ordinarySuccessor, Equiv.prodCongrLeft_apply,
      Equiv.prodCongrRight_apply, hp, turn_other r x ha hb hz]

private theorem successor_a_zero (r : RStar X) (ds : List OddRadix) :
    successor r ds (r.a, 0) = (r.b, 0) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, positive_zero, rowLift,
    r.pairwise_distinct.2.1, rowZero, r.successor_a]

private theorem successor_b_zero (r : RStar X) (ds : List OddRadix) :
    successor r ds (r.b, 0) = (r.c, 0) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, positive_zero, rowLift,
    r.pairwise_distinct.2.2, rowZero, r.successor_b]

private theorem successor_zero (r : RStar X) (ds : List OddRadix) :
    successor r ds 0 = 0 := by
  classical
  change successor r ds (0, 0) = (0, 0)
  simp [successor, sourceTurn, ordinarySuccessor, positive_zero, rowLift,
    r.c_ne_zero.symm, rowZero, r.successor_zero]

private theorem successor_a_pos (r : RStar X) (ds : List OddRadix)
    (h : Box ds) (hp : positive ds h) : successor r ds (r.a, h) = (0, -h) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, hp, turn_a, rowLift,
    r.c_ne_zero.symm, rowZero, r.successor_zero]

private theorem successor_a_neg (r : RStar X) (ds : List OddRadix)
    (h : Box ds) (hp : ¬ positive ds h) : successor r ds (r.a, h) = (r.b, -h) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, hp, rowLift,
    r.pairwise_distinct.2.1, rowZero, r.successor_a]

private theorem successor_b_pos (r : RStar X) (ds : List OddRadix)
    (h : Box ds) (hp : positive ds h) : successor r ds (r.b, h) = (r.b, -h) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, hp, turn_b, rowLift,
    r.pairwise_distinct.2.1, rowZero, r.successor_a]

private theorem successor_b_neg (r : RStar X) (ds : List OddRadix)
    (h : Box ds) (hp : ¬ positive ds h) : successor r ds (r.b, h) = (r.c, -h) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, hp, rowLift,
    r.pairwise_distinct.2.2, rowZero, r.successor_b]

private theorem successor_zero_pos (r : RStar X) (ds : List OddRadix)
    (h : Box ds) (hp : positive ds h) : successor r ds (0, h) = (r.c, -h) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, hp, turn_zero, rowLift,
    r.pairwise_distinct.2.2, rowZero, r.successor_b]

private theorem successor_zero_neg (r : RStar X) (ds : List OddRadix)
    (h : Box ds) (hp : ¬ positive ds h) : successor r ds (0, h) = (0, -h) := by
  classical
  simp [successor, sourceTurn, ordinarySuccessor, hp, rowLift,
    r.c_ne_zero.symm, rowZero, r.successor_zero]

private theorem edge_cycle (r : RStar X) (ds : List OddRadix)
    {u v : X × Box ds} (he : successor r ds u = v) :
    (successor r ds).SameCycle u v := by
  rw [← he]
  exact (Equiv.Perm.SameCycle.refl _ _).apply_right

private theorem gadget_cycle (r : RStar X) (ds : List OddRadix) (h : Box ds) :
    (successor r ds).SameCycle (r.a, h) (r.c, -h) := by
  by_cases hz : h = 0
  · subst h
    simpa using (edge_cycle r ds (successor_a_zero r ds)).trans
      (edge_cycle r ds (successor_b_zero r ds))
  by_cases hp : positive ds h
  · have hn : ¬ positive ds (-h) := fun hn => ((positive_neg hz).mp hn) hp
    exact (edge_cycle r ds (successor_a_pos r ds h hp)).trans
      ((edge_cycle r ds (successor_zero_neg r ds (-h) hn)).trans
        (by simpa using edge_cycle r ds (successor_zero_pos r ds h hp)))
  · have hn : positive ds (-h) := (positive_neg hz).mpr hp
    exact (edge_cycle r ds (successor_a_neg r ds h hp)).trans
      ((edge_cycle r ds (successor_b_pos r ds (-h) hn)).trans
        (by simpa using edge_cycle r ds (successor_b_neg r ds h hp)))

section FiniteBase

variable [Fintype X]

private def support : Finset X := Finset.univ.erase 0

private theorem mem_support (x : X) : x ∈ support ↔ x ≠ 0 := by
  simp [support]

private theorem base_cycle (r : RStar X) :
    r.successor.IsCycleOn (↑(support (X := X)) : Set X) := by
  have hs : (↑(support (X := X)) : Set X) = {x : X | x ≠ 0} := by
    ext x
    exact mem_support x
  rw [hs]
  exact r.nonzero_cycle

private theorem support_three (r : RStar X) : 3 ≤ (support (X := X)).card := by
  have hs : ({r.a, r.b, r.c} : Finset X) ⊆ support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (mem_support _).2 r.a_ne_zero
    · exact (mem_support _).2 r.b_ne_zero
    · exact (mem_support _).2 r.c_ne_zero
  have hcard : ({r.a, r.b, r.c} : Finset X).card = 3 := by
    simp [r.pairwise_distinct.1, r.pairwise_distinct.2.1, r.pairwise_distinct.2.2]
  simpa only [hcard] using Finset.card_le_card hs

private theorem support_card : (support (X := X)).card + 1 = Nat.card X := by
  rw [Nat.card_eq_fintype_card]
  simpa only [support, Finset.card_univ] using
    (Finset.card_erase_add_one (Finset.mem_univ (0 : X)))

private theorem tail_even (r : RStar X) : Even ((support (X := X)).card - 3) := by
  have ht := support_three r
  have hc := support_card (X := X)
  obtain ⟨k, hk⟩ := r.even_card
  refine ⟨k - 2, ?_⟩
  omega

private def column (r : RStar X) (i : ℕ) : X := (r.successor ^ i) r.a

private theorem column_zero (r : RStar X) : column r 0 = r.a := rfl
private theorem column_one (r : RStar X) : column r 1 = r.b := by
  simpa [column] using r.successor_a
private theorem column_two (r : RStar X) : column r 2 = r.c := by
  simp [column, pow_two, Equiv.Perm.mul_apply, r.successor_a, r.successor_b]
private theorem column_next (r : RStar X) (i : ℕ) :
    r.successor (column r i) = column r (i + 1) := by
  simp [column, pow_succ', Equiv.Perm.mul_apply]

private theorem column_ne_zero (r : RStar X) (i : ℕ) : column r i ≠ 0 := by
  exact (mem_support _).1 ((base_cycle r).1.mapsTo.perm_pow i ((mem_support _).2 r.a_ne_zero))

private theorem column_injective (r : RStar X) {i j : ℕ}
    (hi : i < (support (X := X)).card) (hj : j < (support (X := X)).card)
    (he : column r i = column r j) : i = j :=
  (base_cycle r).injOn_pow_apply ((mem_support _).2 r.a_ne_zero) hi hj he

private theorem column_close (r : RStar X) :
    column r (support (X := X)).card = r.a :=
  (base_cycle r).pow_card_apply ((mem_support _).2 r.a_ne_zero)

private theorem tail_step (r : RStar X) (ds : List OddRadix) (i : ℕ)
    (hi : 3 ≤ i) (hb : i < (support (X := X)).card) (h : Box ds) :
    successor r ds (column r i, h) = (column r (i + 1), rowZero ds h) := by
  have ht := support_three r
  have ha : column r i ≠ r.a := by
    intro he
    have := column_injective r hb (by omega : 0 < (support (X := X)).card)
      (he.trans (column_zero r).symm)
    omega
  have hbb : column r i ≠ r.b := by
    intro he
    have := column_injective r hb (by omega : 1 < (support (X := X)).card)
      (he.trans (column_one r).symm)
    omega
  have hc : column r i ≠ r.c := by
    intro he
    have := column_injective r hb (by omega : 2 < (support (X := X)).card)
      (he.trans (column_two r).symm)
    omega
  rw [successor_ordinary r ds _ ha hbb (column_ne_zero r i), column_next]
  simp [rowLift, hc]

/-- The entire ordinary tail, in its actual traversal order, including the M=4 tail. -/
private theorem tail_power (r : RStar X) (ds : List OddRadix) (j : ℕ)
    (hj : j ≤ (support (X := X)).card - 3) (h : Box ds) :
    (successor r ds ^ (j + 1)) (r.c, h) =
      (column r (j + 3), (rowZero ds ^ j) (rowOne ds h)) := by
  have ht := support_three r
  induction j with
  | zero =>
    change successor r ds (r.c, h) = (column r 3, (rowZero ds ^ 0) (rowOne ds h))
    rw [successor_ordinary r ds _ r.pairwise_distinct.2.1.symm
      r.pairwise_distinct.2.2.symm r.c_ne_zero]
    simp only [rowLift, if_pos rfl, pow_zero, Equiv.Perm.one_apply]
    exact Prod.ext (by simpa only [column_two] using column_next r 2) rfl
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    rw [tail_step r ds (j + 3) (by omega) (by omega)]
    simp only [pow_succ', Equiv.Perm.mul_apply]

private theorem row_zero_even (ds : List OddRadix) {n : ℕ} (hn : Even n) :
    rowZero ds ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have htwo : rowZero ds ^ 2 = 1 := by
    ext h
    simp [pow_two, Equiv.Perm.mul_apply, rowZero]
  rw [show k + k = 2 * k by omega, pow_mul, htwo, one_pow]

private theorem tail_return_power (r : RStar X) (ds : List OddRadix) (h : Box ds) :
    (successor r ds ^ ((support (X := X)).card - 3 + 1)) (r.c, h) =
      (r.a, rowOne ds h) := by
  have ht := support_three r
  have hp := tail_power r ds ((support (X := X)).card - 3) le_rfl h
  rw [row_zero_even ds (tail_even r)] at hp
  simpa only [show (support (X := X)).card - 3 + 3 = (support (X := X)).card by omega,
    column_close, Equiv.Perm.one_apply] using hp

private def gadgetLength (ds : List OddRadix) (h : Box ds) : ℕ := if h = 0 then 2 else 3

private theorem gadget_power (r : RStar X) (ds : List OddRadix) (h : Box ds) :
    (successor r ds ^ gadgetLength ds h) (r.a, h) = (r.c, -h) := by
  by_cases hz : h = 0
  · subst h
    simp [gadgetLength, pow_two, Equiv.Perm.mul_apply,
      successor_a_zero, successor_b_zero]
  by_cases hp : positive ds h
  · have hn : ¬ positive ds (-h) := fun hn => ((positive_neg hz).mp hn) hp
    simp [gadgetLength, hz, pow_succ', Equiv.Perm.mul_apply,
      successor_a_pos r ds h hp, successor_zero_neg r ds (-h) hn,
      successor_zero_pos r ds h hp]
  · have hn : positive ds (-h) := (positive_neg hz).mpr hp
    simp [gadgetLength, hz, pow_succ', Equiv.Perm.mul_apply,
      successor_a_neg r ds h hp, successor_b_pos r ds (-h) hn,
      successor_b_neg r ds h hp]

private theorem gadget_avoids_a (r : RStar X) (ds : List OddRadix) (h : Box ds)
    (i : ℕ) (hi : 0 < i) (hb : i < gadgetLength ds h) :
    ((successor r ds ^ i) (r.a, h)).1 ≠ r.a := by
  by_cases hz : h = 0
  · subst h
    have hib : i < 2 := by simpa [gadgetLength] using hb
    have hi1 : i = 1 := by omega
    subst i
    simpa [successor_a_zero] using r.pairwise_distinct.1.symm
  have hib : i < 3 := by simpa [gadgetLength, hz] using hb
  by_cases hp : positive ds h
  · have hn : ¬ positive ds (-h) := fun hn => ((positive_neg hz).mp hn) hp
    interval_cases i <;>
      simpa [pow_two, Equiv.Perm.mul_apply, successor_a_pos r ds h hp,
        successor_zero_neg r ds (-h) hn] using r.a_ne_zero.symm
  · have hn : positive ds (-h) := (positive_neg hz).mpr hp
    interval_cases i <;>
      simpa [pow_two, Equiv.Perm.mul_apply, successor_a_neg r ds h hp,
        successor_b_pos r ds (-h) hn] using r.pairwise_distinct.1.symm

private theorem tail_avoids_a (r : RStar X) (ds : List OddRadix) (h : Box ds)
    (i : ℕ) (hi : i < (support (X := X)).card - 3 + 1) :
    ((successor r ds ^ i) (r.c, h)).1 ≠ r.a := by
  have ht := support_three r
  cases i with
  | zero => simpa using r.pairwise_distinct.2.1.symm
  | succ j =>
    rw [tail_power r ds j (by omega)]
    change column r (j + 3) ≠ r.a
    intro he
    have := column_injective r (by omega : j + 3 < (support (X := X)).card)
      (by omega : 0 < (support (X := X)).card) (he.trans (column_zero r).symm)
    omega

private theorem block_length (r : RStar X) (ds : List OddRadix) (h : Box ds) :
    (support (X := X)).card - 3 + 1 + gadgetLength ds h =
      if h = 0 then Nat.card X - 1 else Nat.card X := by
  have ht := support_three r
  have hc := support_card (X := X)
  by_cases hz : h = 0 <;> simp only [gadgetLength, hz, ite_true, ite_false] <;> omega

/-- The return is the actual first positive visit to the a-column, including closure.
The block has M-1 steps on row zero and M steps on every other row. -/
theorem box_first_return (r : RStar X) (ds : List OddRadix) (h : Box ds) :
    let len := if h = 0 then Nat.card X - 1 else Nat.card X
    (successor r ds ^ len) (r.a, h) = (r.a, predecessor ds h) ∧
      ∀ i : ℕ, 0 < i → i < len → ((successor r ds ^ i) (r.a, h)).1 ≠ r.a := by
  dsimp only
  rw [← block_length r ds h]
  constructor
  · rw [pow_add, Equiv.Perm.mul_apply, gadget_power, tail_return_power]
    congr 1
    simpa [rowZero] using row_return ds h
  · intro i hi hb
    by_cases hg : i < gadgetLength ds h
    · exact gadget_avoids_a r ds h i hi hg
    · have he : i = (i - gadgetLength ds h) + gadgetLength ds h := by omega
      rw [he, pow_add, Equiv.Perm.mul_apply, gadget_power]
      exact tail_avoids_a r ds (-h) _ (by omega)

private theorem return_cycle (r : RStar X) (ds : List OddRadix) (h : Box ds) :
    (successor r ds).SameCycle (r.a, h) (r.a, predecessor ds h) := by
  exact ⟨(((if h = 0 then Nat.card X - 1 else Nat.card X) : ℕ) : ℤ),
    by simpa using (box_first_return r ds h).1⟩

private theorem anchor_cycle (r : RStar X) (ds : List OddRadix) (h : Box ds) :
    (successor r ds).SameCycle (r.a, 0) (r.a, h) := by
  obtain ⟨n, hn⟩ := ((predecessor_cycle ds).2 (Set.mem_univ 0)
    (Set.mem_univ h)).exists_nat_pow_eq
  rw [← hn]
  clear hn
  induction n with
  | zero => exact .refl _ _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (return_cycle r ds _)

private theorem gadget_coverage (r : RStar X) (ds : List OddRadix) (x : X) (h : Box ds)
    (hx : x = 0 ∨ x = r.a ∨ x = r.b ∨ x = r.c) (hne : (x, h) ≠ (0 : X × Box ds)) :
    (successor r ds).SameCycle (r.a, 0) (x, h) := by
  rcases hx with rfl | rfl | rfl | rfl
  · have hh : h ≠ 0 := by intro he; exact hne (Prod.ext rfl he)
    by_cases hp : positive ds h
    · have hn : ¬ positive ds (-h) := fun hn => ((positive_neg hh).mp hn) hp
      exact (anchor_cycle r ds h).trans
        ((edge_cycle r ds (successor_a_pos r ds h hp)).trans
          (by simpa using edge_cycle r ds (successor_zero_neg r ds (-h) hn)))
    · have hn : positive ds (-h) := (positive_neg hh).mpr hp
      exact (anchor_cycle r ds (-h)).trans
        (by simpa using edge_cycle r ds (successor_a_pos r ds (-h) hn))
  · exact anchor_cycle r ds h
  · by_cases hp : positive ds h
    · have hn : ¬ positive ds (-h) := fun hn => ((positive_neg (positive_ne_zero hp)).mp hn) hp
      exact (anchor_cycle r ds (-h)).trans
        (by simpa using edge_cycle r ds (successor_a_neg r ds (-h) hn))
    · by_cases hz : h = 0
      · subst h
        exact (anchor_cycle r ds 0).trans (edge_cycle r ds (successor_a_zero r ds))
      · have hn : positive ds (-h) := (positive_neg hz).mpr hp
        exact (anchor_cycle r ds h).trans
          ((edge_cycle r ds (successor_a_neg r ds h hp)).trans
            (by simpa using edge_cycle r ds (successor_b_pos r ds (-h) hn)))
  · exact (anchor_cycle r ds (-h)).trans (by simpa using gadget_cycle r ds (-h))

/-- Every nonzero product vertex is reached: exceptional columns and all ordinary fibers. -/
private theorem coverage (r : RStar X) (ds : List OddRadix)
    (v : X × Box ds) (hv : v ≠ 0) :
    (successor r ds).SameCycle (r.a, 0) v := by
  rcases v with ⟨x, h⟩
  by_cases hx : x = 0 ∨ x = r.a ∨ x = r.b ∨ x = r.c
  · exact gadget_coverage r ds x h hx hv
  have hz : x ≠ 0 := fun he => hx (Or.inl he)
  obtain ⟨i, hi, he⟩ := (base_cycle r).exists_pow_eq
    ((mem_support _).2 r.a_ne_zero) ((mem_support _).2 hz)
  change column r i = x at he
  have hi3 : 3 ≤ i := by
    by_contra hh
    have hilt : i < 3 := by omega
    interval_cases i
    · exact hx (Or.inr (Or.inl (he.symm.trans (column_zero r))))
    · exact hx (Or.inr (Or.inr (Or.inl (he.symm.trans (column_one r)))))
    · exact hx (Or.inr (Or.inr (Or.inr (he.symm.trans (column_two r)))))
  let j := i - 3
  let t := (rowOne ds).symm ((rowZero ds ^ j).symm h)
  have hp := tail_power r ds j (by dsimp [j]; omega) t
  have hp' : (successor r ds ^ (j + 1)) (r.c, t) = (x, h) := by
    simpa [show j + 3 = i by dsimp [j]; omega, he, t] using hp
  have hc : (successor r ds).SameCycle (r.c, t) (x, h) :=
    ⟨((j + 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact hp'⟩
  exact ((anchor_cycle r ds (-t)).trans (by simpa using gadget_cycle r ds (-t))).trans hc

/-- One cycle on the entire nonzero carrier; all seams and closure are permutation edges. -/
theorem nonzero_cycle (r : RStar X) (ds : List OddRadix) :
    (successor r ds).IsCycleOn {v : X × Box ds | v ≠ 0} := by
  refine ⟨bijOn_complement _ 0 (successor_zero r ds), ?_⟩
  intro x hx y hy
  exact (coverage r ds x hx).symm.trans (coverage r ds y hy)

/-- The complete odd-box product, with the distinguished triple retained literally. -/
def boxRStar (r : RStar X) (ds : List OddRadix) : RStar (X × Box ds) where
  successor := successor r ds
  successor_zero := successor_zero r ds
  nonzero_cycle := nonzero_cycle r ds
  difference := difference r ds
  difference_spec := difference_spec r ds
  even_card := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Box ds), box_card]
    exact r.even_card.mul_right _
  a := (r.a, 0)
  b := (r.b, 0)
  c := (r.c, 0)
  a_ne_zero he := r.a_ne_zero (congrArg Prod.fst he)
  b_ne_zero he := r.b_ne_zero (congrArg Prod.fst he)
  c_ne_zero he := r.c_ne_zero (congrArg Prod.fst he)
  pairwise_distinct := ⟨fun he => r.pairwise_distinct.1 (congrArg Prod.fst he),
    fun he => r.pairwise_distinct.2.1 (congrArg Prod.fst he),
    fun he => r.pairwise_distinct.2.2 (congrArg Prod.fst he)⟩
  successor_a := successor_a_zero r ds
  successor_b := successor_b_zero r ds
  triple_sum := Prod.ext r.triple_sum (add_zero 0)

end FiniteBase

def transportRStar {G K : Type*} [AddCommGroup G] [Finite G]
    [AddCommGroup K] [Finite K] (e : G ≃+ K) (r : RStar K) : RStar G := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype K := Fintype.ofFinite K
  exact {
    toRCycle := transportCycle e.symm r.toRCycle
    even_card := (Nat.card_congr e.toEquiv).symm ▸ r.even_card
    a := e.symm r.a
    b := e.symm r.b
    c := e.symm r.c
    a_ne_zero := by simpa using r.a_ne_zero
    b_ne_zero := by simpa using r.b_ne_zero
    c_ne_zero := by simpa using r.c_ne_zero
    pairwise_distinct := ⟨fun h => r.pairwise_distinct.1 (e.symm.injective h),
      fun h => r.pairwise_distinct.2.1 (e.symm.injective h),
      fun h => r.pairwise_distinct.2.2 (e.symm.injective h)⟩
    successor_a := by simp [transportCycle, r.successor_a]
    successor_b := by simp [transportCycle, r.successor_b]
    triple_sum := by rw [← map_add, r.triple_sum] }

/-- An even R-star base times any odd finite abelian group retains the prescribed triple.
No decomposition, generator, orthomorphism, row inventory or cycle certificate is an input. -/
theorem exists_rstar_product {H : Type*} [AddCommGroup H] [Finite H]
    (r : HeadleyExtension.RStar X) (hH : Odd (Nat.card H)) :
    ∃ rOut : HeadleyExtension.RStar (X × H),
      rOut.a = (r.a, 0) ∧ rOut.b = (r.b, 0) ∧ rOut.c = (r.c, 0) := by
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨ds, ⟨e⟩⟩ := odd_box hH
  let E : X × H ≃+ X × Box ds := (AddEquiv.refl X).prodCongr e
  refine ⟨transportRStar E (boxRStar r ds), ?_, ?_, ?_⟩ <;>
    change ((AddEquiv.refl X).prodCongr e).symm (_, 0) = (_, 0) <;>
    exact Prod.ext rfl e.symm.map_zero

end D5.S3.FiniteGroups.HeadleyOddProduct
