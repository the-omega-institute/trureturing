import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
import Mathlib.Logic.Equiv.Fin.Basic

/-! A half-size count for four independent parallel three-leaf stars in the signed seven-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7ParallelStarHalf

open Finset
open BalancedCriticalSpectrum (Q)
open Q9SignedProjection (signedRow)

private def center : Q 3 := fun _ => false

/-- The integer indicator of the zero vertex and its three single-coordinate neighbors. -/
def starIndicator (x : Q 3) : ℤ :=
  if (univ.filter fun i => x i = true).card ≤ 1 then 1 else 0

private def paritySign (x : Q 3) : ℤ :=
  (-1) ^ (univ.filter fun i => x i = true).card

private theorem signedRow_star : ∀ x : Q 3,
    signedRow starIndicator x = if x = center then 3 else starIndicator x := by
  decide

private theorem star_cases : ∀ x : Q 3, starIndicator x = 0 ∨ starIndicator x = 1 := by
  decide

private theorem center_indicator : starIndicator center = 1 := by decide
private theorem center_sign : paritySign center = 1 := by decide

private theorem leaf_sign :
    ∀ x : Q 3, x ≠ center → starIndicator x = 1 → paritySign x = -1 := by
  decide

private theorem leaf_card :
    (univ.filter fun x : Q 3 => x ≠ center ∧ starIndicator x = 1).card = 3 := by
  decide

private theorem true_star_card : ∀ i : Fin 3,
    (univ.filter fun x : Q 3 => x i = true ∧ starIndicator x = 1).card = 1 := by
  decide

private theorem left_lt_right (i : Fin 3) (j : Fin 4) :
    i.castAdd 4 < j.natAdd 3 := by
  change i.val < 3 + j.val
  exact lt_of_lt_of_le i.isLt (Nat.le_add_right 3 j.val)

private theorem left_lt_left (i j : Fin 3) : i.castAdd 4 < j.castAdd 4 ↔ i < j := Iff.rfl

private theorem flip_append_left (x : Q 3) (y : Q 4) (i : Fin 3) :
    BalancedCriticalSpectrum.flip (Fin.append x y) (i.castAdd 4) =
      Fin.append (BalancedCriticalSpectrum.flip x i) y := by
  funext k
  refine Fin.addCases (m := 3) (n := 4) ?_ ?_ k
  · intro j
    by_cases h : j = i
    · subst j
      simp [BalancedCriticalSpectrum.flip]
    · have h' : j.castAdd 4 ≠ i.castAdd 4 :=
        fun e => h (Fin.ext (congrArg (fun k : Fin 7 => k.val) e))
      simp [BalancedCriticalSpectrum.flip, h, h']
  · intro j
    simp [BalancedCriticalSpectrum.flip, (left_lt_right i j).ne.symm]

private theorem flip_append_right (x : Q 3) (y : Q 4) (i : Fin 4) :
    BalancedCriticalSpectrum.flip (Fin.append x y) (i.natAdd 3) =
      Fin.append x (BalancedCriticalSpectrum.flip y i) := by
  funext k
  refine Fin.addCases (m := 3) (n := 4) ?_ ?_ k
  · intro j
    simp [BalancedCriticalSpectrum.flip, (left_lt_right j i).ne]
  · intro j
    by_cases h : j = i
    · subst j
      simp [BalancedCriticalSpectrum.flip]
    · have h' : j.natAdd 3 ≠ i.natAdd 3 :=
        fun e => h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val e)))
      simp [BalancedCriticalSpectrum.flip, h, h']

private theorem sign_append_left (x : Q 3) (y : Q 4) (i : Fin 3) :
    truePrefixSign (Fin.append x y) (i.castAdd 4) = truePrefixSign x i := by
  simp only [truePrefixSign, card_filter]
  rw [Fin.sum_univ_add (a := 3) (b := 4)]
  simp only [Fin.append_left, Fin.append_right, left_lt_left,
    fun j => not_lt_of_ge (left_lt_right i j).le, false_and, ite_false, sum_const_zero,
    add_zero]

private theorem sign_append_right (x : Q 3) (y : Q 4) (i : Fin 4) :
    truePrefixSign (Fin.append x y) (i.natAdd 3) = paritySign x * truePrefixSign y i := by
  simp only [truePrefixSign, paritySign, card_filter]
  rw [Fin.sum_univ_add (a := 3) (b := 4)]
  simp only [Fin.append_left, Fin.append_right, left_lt_right, true_and,
    Fin.natAdd_lt_natAdd_iff, pow_add]

private theorem signedRow_append {a : Q 7 → ℤ} {ε : Q 4 → ℤ}
    (ha : ∀ x y, a (Fin.append x y) = starIndicator x * ε y)
    (x : Q 3) (y : Q 4) :
    signedRow a (Fin.append x y) =
      signedRow starIndicator x * ε y + (paritySign x * starIndicator x) * signedRow ε y := by
  simp only [signedRow]
  rw [Fin.sum_univ_add (a := 3) (b := 4), sum_mul, mul_sum]
  simp only [flip_append_left, flip_append_right, sign_append_left, sign_append_right, ha]
  congr 1
  · exact sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
  · exact sum_congr rfl fun _ _ => by ring

private theorem card_support_split (f : Q 7 → ℤ) (p : Q 3 → Prop) [DecidablePred p] :
    (univ.filter fun z : Q 7 => p (fun i => z (i.castAdd 4)) ∧ f z ≠ 0).card =
      ∑ x : Q 3, if p x then (univ.filter fun y : Q 4 => f (Fin.append x y) ≠ 0).card
        else 0 := by
  rw [card_filter]
  let join : Q 3 × Q 4 ≃ Q 7 := Fin.appendEquiv 3 4
  rw [← join.sum_comp (fun z => if p (fun i => z (i.castAdd 4)) ∧ f z ≠ 0
    then (1 : ℕ) else 0), Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  change (∑ y : Q 4, if p (fun i => Fin.append x y (i.castAdd 4)) ∧
    f (Fin.append x y) ≠ 0 then 1 else 0) = _
  simp only [Fin.append_left]
  by_cases hx : p x <;> simp [hx, card_filter]

/-- The TRUE half in each star direction has four occupied points of `a`
and eight of `b`. The doubling equation comes from two copies of the `b` fiber. -/
theorem true_half_card_of_parallel_stars {a b : Q 7 → ℤ} {ε : Q 4 → ℤ}
    (ha : ∀ x y, a (Fin.append x y) = starIndicator x * ε y)
    (hcenters : (univ.filter fun y : Q 4 => ε y ≠ 0).card = 4)
    (hindependent : ∀ y : Q 4, ε y ≠ 0 →
      ∀ j : Fin 4, ε (BalancedCriticalSpectrum.flip y j) = 0)
    (hb : ∀ z, 2 * b z = 3 * a z - signedRow a z)
    (hbcard : (univ.filter fun z : Q 7 => b z ≠ 0).card = 28)
    (i : Fin 3) :
    (univ.filter fun z : Q 7 => z (i.castAdd 4) = true ∧ a z ≠ 0).card +
      2 * (univ.filter fun z : Q 7 => z (i.castAdd 4) = true ∧ b z ≠ 0).card = 20 := by
  let centers := univ.filter fun y : Q 4 => ε y ≠ 0
  let rowSupport := univ.filter fun y : Q 4 => signedRow ε y ≠ 0
  let L := rowSupport.card
  have row_zero (y : Q 4) (hy : ε y ≠ 0) : signedRow ε y = 0 := by
    simp [signedRow, hindependent y hy]
  have disjoint : Disjoint centers rowSupport := by
    refine disjoint_left.mpr fun y hy hr => ?_
    exact (mem_filter.mp hr).2 (row_zero y (mem_filter.mp hy).2)
  have leaf_union : (centers ∪ rowSupport).card = 4 + L := by
    rw [card_union_of_disjoint disjoint, hcenters]
  have doubled (x : Q 3) (y : Q 4) :
      2 * b (Fin.append x y) = 3 * (starIndicator x * ε y) -
        ((if x = center then 3 else starIndicator x) * ε y +
          (paritySign x * starIndicator x) * signedRow ε y) := by
    rw [hb, ha, signedRow_append ha, signedRow_star]
  have count_a (x : Q 3) :
      (univ.filter fun y : Q 4 => a (Fin.append x y) ≠ 0).card =
        if starIndicator x = 1 then 4 else 0 := by
    rcases star_cases x with hx | hx <;> simp [ha, hx, hcenters]
  have count_b (x : Q 3) :
      (univ.filter fun y : Q 4 => b (Fin.append x y) ≠ 0).card =
        (if x = center then L else 0) +
          (if x ≠ center ∧ starIndicator x = 1 then 4 + L else 0) := by
    by_cases hc : x = center
    · subst x
      suffices (univ.filter fun y : Q 4 => b (Fin.append center y) ≠ 0) = rowSupport by
        simp [this, L]
      ext y
      have h := doubled center y
      simp [center_indicator, center_sign] at h
      simp only [rowSupport, mem_filter, mem_univ, true_and]
      omega
    · rcases star_cases x with hx | hx
      · have hz (y : Q 4) : b (Fin.append x y) = 0 := by
          have h := doubled x y
          simp [hc, hx] at h
          omega
        simp [hz, hc, hx]
      · suffices (univ.filter fun y : Q 4 => b (Fin.append x y) ≠ 0) =
            centers ∪ rowSupport by
          simp [this, leaf_union, hc, hx]
        ext y
        have h := doubled x y
        simp only [ite_eq_right hc, hx, leaf_sign x hc hx, one_mul, mul_one, neg_one_mul] at h
        simp only [centers, rowSupport, mem_union, mem_filter, mem_univ, true_and]
        by_cases hy : ε y = 0
        · omega
        · have hr := row_zero y hy
          omega
  have total_b : (∑ x : Q 3, ((if x = center then L else 0) +
      (if x ≠ center ∧ starIndicator x = 1 then 4 + L else 0))) = 28 := by
    simpa only [true_and, ite_true, count_b] using
      (card_support_split b (fun _ => True)).symm.trans hbcard
  have hL : L = 4 := by
    simp [sum_add_distrib, sum_ite, leaf_card] at total_b
    omega
  have half_a : (univ.filter fun z : Q 7 => z (i.castAdd 4) = true ∧ a z ≠ 0).card = 4 := by
    rw [card_support_split a (fun x => x i = true), show (∑ x : Q 3, if x i = true then
          (univ.filter fun y : Q 4 => a (Fin.append x y) ≠ 0).card else 0) =
          ∑ x : Q 3, if x i = true ∧ starIndicator x = 1 then 4 else 0 by
      apply sum_congr rfl
      intro x _
      rw [count_a]
      split_ifs <;> simp_all]
    simp [sum_ite, true_star_card]
  have half_b : (univ.filter fun z : Q 7 => z (i.castAdd 4) = true ∧ b z ≠ 0).card = 8 := by
    rw [card_support_split b (fun x => x i = true), show (∑ x : Q 3, if x i = true then
          (univ.filter fun y : Q 4 => b (Fin.append x y) ≠ 0).card else 0) =
          ∑ x : Q 3, if x i = true ∧ starIndicator x = 1 then 8 else 0 by
      apply sum_congr rfl
      intro x _
      by_cases hi : x i = true
      · have hc : x ≠ center := fun h => by simp [h, center] at hi
        simp [count_b, hi, hc, hL]
      · simp [hi]]
    simp [sum_ite, true_star_card]
  rw [half_a, half_b]

#check true_half_card_of_parallel_stars
#print axioms true_half_card_of_parallel_stars

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7ParallelStarHalf
