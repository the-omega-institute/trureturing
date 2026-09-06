/- GID: D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen
   mirror-E: none(waiver:finite-certificates-checked-by-lean-kernel)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:271aa869d74ec58b5dfeca63b727b28aa2c6ce214a15f9ff52f76685873c0173
   digest: The 17 by 17 odd-parity checkerboard has no-three-in-line optimum 26. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

namespace D5.S3.Arith.Lattices.ThinCheckerboardNoThreeInLineSeventeen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Integer lattice points. -/
abbrev Point := Prod Int Int

/-- The coefficients `(a, b, c)` of the equation `a*x + b*y = c`. -/
abbrev LineKey := Prod Int (Prod Int Int)

/-- The integer determinant of the displacement vectors `q-p` and `r-p`. -/
def det (p q r : Point) : Int :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- Membership in the odd-parity class of the 17 by 17 grid. -/
def Thin (p : Point) : Prop :=
  0 <= p.1 ∧ p.1 <= 16 ∧ 0 <= p.2 ∧ p.2 <= 16 ∧ (p.1 + p.2) % 2 = 1

/-- Every three distinct members have nonzero determinant, with no slope restriction. -/
def NTIL (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r → det p q r ≠ 0

/-- Integer incidence with a line equation. -/
def onLine (p : Point) (l : LineKey) : Prop :=
  l.1 * p.1 + l.2.1 * p.2 = l.2.2

private instance decidableOnLine (p : Point) (l : LineKey) : Decidable (onLine p l) :=
  inferInstanceAs (Decidable (_ = _))

/-- The explicit 26-point certificate; all entries are checked below by the kernel. -/
def witness : Finset Point := {
  (0, 5), (0, 9), (1, 4), (2, 1), (2, 13), (3, 12), (3, 16),
  (4, 5), (5, 2), (5, 16), (6, 1), (6, 13), (7, 14), (9, 2),
  (10, 3), (10, 15), (11, 0), (11, 14), (12, 11), (13, 0),
  (13, 4), (14, 3), (14, 15), (15, 12), (16, 7), (16, 11)}

/-- Forty line equations with nonnegative integer weights, scaled to coverage 24. -/
def weightedLines : List (Prod LineKey Nat) := [
  ((0, 1, 0), 8), ((0, 1, 1), 6), ((0, 1, 2), 3), ((0, 1, 3), 2),
  ((0, 1, 13), 2), ((0, 1, 14), 3), ((0, 1, 15), 6), ((0, 1, 16), 8),
  ((1, -1, -11), 4), ((1, -1, -9), 7), ((1, -1, -7), 9),
  ((1, -1, -5), 12), ((1, -1, -3), 14), ((1, -1, -1), 15),
  ((1, -1, 1), 15), ((1, -1, 3), 14), ((1, -1, 5), 12),
  ((1, -1, 7), 9), ((1, -1, 9), 7), ((1, -1, 11), 4),
  ((1, 0, 0), 8), ((1, 0, 1), 6), ((1, 0, 2), 3), ((1, 0, 3), 2),
  ((1, 0, 13), 2), ((1, 0, 14), 3), ((1, 0, 15), 6), ((1, 0, 16), 8),
  ((1, 1, 5), 4), ((1, 1, 7), 7), ((1, 1, 9), 9), ((1, 1, 11), 12),
  ((1, 1, 13), 14), ((1, 1, 15), 15), ((1, 1, 17), 15), ((1, 1, 19), 14),
  ((1, 1, 21), 12), ((1, 1, 23), 9), ((1, 1, 25), 7), ((1, 1, 27), 4)]

/-- The certificate has exactly 26 distinct points. -/
theorem witness_card : witness.card = 26 := by decide +kernel

/-- Every point of the certificate belongs to the thin checkerboard. -/
theorem witness_thin : ∀ p ∈ witness, Thin p := by
  unfold witness Thin
  decide +kernel

/-- Kernel enumeration checks every distinct triple of certificate points. -/
theorem witness_ntil : NTIL witness := by
  unfold NTIL witness det
  decide +kernel

private theorem weightedLines_length : weightedLines.length = 40 := by decide

/-- The line equation at a zero-based index in the certificate list. -/
def line (i : Fin 40) : LineKey :=
  (weightedLines.get (i.cast weightedLines_length.symm)).1

/-- The integer weight at the same zero-based index. -/
def weight (i : Fin 40) : Nat :=
  (weightedLines.get (i.cast weightedLines_length.symm)).2

/-- Total weight of certificate lines incident with an integer point. -/
def cover (p : Point) : Nat :=
  ∑ i : Fin 40, if onLine p (line i) then weight i else 0

/-- The forty integer weights sum to 320. -/
theorem weight_sum : (∑ i : Fin 40, weight i) = 320 := by decide +kernel

/-- Every odd-parity point of the finite grid has coverage at least 24. -/
theorem cover_grid :
    ∀ x y : Fin 17, (x.val + y.val) % 2 = 1 →
      24 <= cover (x.val, y.val) := by decide +kernel

private theorem line_nonzero : ∀ i : Fin 40, (line i).1 ≠ 0 ∨ (line i).2.1 ≠ 0 := by
  decide +kernel

private theorem det_zero_of_onLine (p q r : Point) (l : LineKey)
    (hn : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    (hp : onLine p l) (hq : onLine q l) (hr : onLine r l) : det p q r = 0 := by
  unfold onLine at hp hq hr
  have ha : l.1 * det p q r = 0 := by
    unfold det
    linear_combination (q.2 - r.2) * hp + (r.2 - p.2) * hq + (p.2 - q.2) * hr
  have hb : l.2.1 * det p q r = 0 := by
    unfold det
    linear_combination (r.1 - q.1) * hp + (p.1 - r.1) * hq + (q.1 - p.1) * hr
  rcases hn with hn | hn
  · exact (mul_eq_zero.mp ha).resolve_left hn
  · exact (mul_eq_zero.mp hb).resolve_left hn

private theorem capacity (S : Finset Point) (hs : NTIL S) (i : Fin 40) :
    (S.filter (fun p => onLine p (line i))).card <= 2 := by
  by_contra h
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (S.filter (fun p => onLine p (line i))).card by omega)
  exact hs p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    r (Finset.mem_filter.mp hr).1 hpq hpr hqr
    (det_zero_of_onLine p q r (line i) (line_nonzero i)
      (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hr).2)

private theorem cover_thin (p : Point) (hp : Thin p) : 24 <= cover p := by
  rcases hp with ⟨hx0, hx17, hy0, hy17, hpar⟩
  let x : Fin 17 := ⟨p.1.toNat, by omega⟩
  let y : Fin 17 := ⟨p.2.toNat, by omega⟩
  have hxy : (x.val + y.val) % 2 = 1 := by dsimp [x, y]; omega
  have h := cover_grid x y hxy
  simpa [x, y, Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] using h

/-- Double counting the weighted incidences bounds every admissible subset by 26. -/
theorem upper_bound (S : Finset Point) (ht : ∀ p ∈ S, Thin p) (hs : NTIL S) :
    S.card <= 26 := by
  have hcount : S.card * 24 <= 640 := calc
    S.card * 24 = ∑ p ∈ S, 24 := by simp
    _ <= ∑ p ∈ S, cover p := Finset.sum_le_sum (fun p hp => cover_thin p (ht p hp))
    _ = ∑ i : Fin 40, ∑ p ∈ S, if onLine p (line i) then weight i else 0 := by
      unfold cover
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 40, (S.filter (fun p => onLine p (line i))).card * weight i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp
    _ <= ∑ i : Fin 40, 2 * weight i :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right (weight i) (capacity S hs i))
    _ = 640 := by rw [← Finset.mul_sum, weight_sum]; decide
  omega

/-- The exact optimum on the 17 by 17 odd-parity class, for integer-determinant NTIL:
an explicit set attains 26, and every admissible set has cardinality at most 26. -/
theorem thinCheckerboard17_ntil_max_eq_26 :
    (∃ S : Finset Point, (∀ p ∈ S, Thin p) ∧ S.card = 26 ∧ NTIL S) ∧
    (∀ T : Finset Point, (∀ p ∈ T, Thin p) → NTIL T → T.card <= 26) := by
  exact ⟨⟨witness, witness_thin, witness_card, witness_ntil⟩, upper_bound⟩

example : Point := (0, 1)
example : Thin (0, 1) := by unfold Thin; decide
example : Finset Point := witness
example : (∀ p ∈ witness, Thin p) ∧ NTIL witness := ⟨witness_thin, witness_ntil⟩
example : (0 + 1 : Nat) % 2 = 1 := by decide

#print axioms witness_card
#print axioms witness_thin
#print axioms witness_ntil
#print axioms weight_sum
#print axioms cover_grid
#print axioms upper_bound
#print axioms thinCheckerboard17_ntil_max_eq_26

end D5.S3.Arith.Lattices.ThinCheckerboardNoThreeInLineSeventeen
