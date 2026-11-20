import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
import Mathlib.Algebra.BigOperators.Fin

/-! The signed neighbor equation on the nine-cube across a contiguous four-plus-five cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)

local notation "flip" => BalancedCriticalSpectrum.flip
attribute [local instance] Classical.propDecidable

/-- Concatenate the left and right blocks in coordinate order. -/
def join (x : Q 4) (y : Q 5) : Q 9 := Fin.append x y

/-- Fix the right block of an integer function on the nine-cube. -/
def fiber (z : Q 9 → ℤ) (y : Q 5) (x : Q 4) : ℤ := z (join x y)

/-- The signed neighbor sum at a vertex, using the TRUE-prefix edge signs. -/
def signedRow {n : ℕ} (g : Q n → ℤ) (x : Q n) : ℤ :=
  ∑ i : Fin n, truePrefixSign x i * g (flip x i)

/-- The parity sign contributed by all four coordinates of the left block. -/
def leftParitySign (x : Q 4) : ℤ :=
  (-1) ^ (Finset.univ.filter (fun i : Fin 4 => x i = true)).card

private theorem left_lt_right (i : Fin 4) (j : Fin 5) : i.castAdd 5 < j.natAdd 4 := by
  change i.val < 4 + j.val
  exact lt_of_lt_of_le i.isLt (Nat.le_add_right 4 j.val)

private theorem right_not_lt_left (i : Fin 4) (j : Fin 5) : ¬ j.natAdd 4 < i.castAdd 5 :=
  not_lt_of_ge (left_lt_right i j).le

private theorem left_lt_left (i j : Fin 4) : i.castAdd 5 < j.castAdd 5 ↔ i < j := Iff.rfl

private theorem right_lt_right (i j : Fin 5) : i.natAdd 4 < j.natAdd 4 ↔ i < j := by
  change 4 + i.val < 4 + j.val ↔ i.val < j.val
  omega

private theorem flip_join_left (x : Q 4) (y : Q 5) (i : Fin 4) :
    flip (join x y) (i.castAdd 5) = join (flip x i) y := by
  funext k
  refine Fin.addCases (m := 4) (n := 5) ?_ ?_ k
  · intro j
    by_cases h : j = i
    · subst j
      simp [BalancedCriticalSpectrum.flip, join]
    · have h' : j.castAdd 5 ≠ i.castAdd 5 := fun he =>
      h (Fin.ext (congrArg (fun k : Fin 9 => k.val) he))
      simp [BalancedCriticalSpectrum.flip, join, h, h']
  · intro j
    simp only [BalancedCriticalSpectrum.flip, join, Function.update_apply,
      Fin.append_left, Fin.append_right,
      (left_lt_right i j).ne.symm, ite_false]

private theorem flip_join_right (x : Q 4) (y : Q 5) (i : Fin 5) :
    flip (join x y) (i.natAdd 4) = join x (flip y i) := by
  funext k
  refine Fin.addCases (m := 4) (n := 5) ?_ ?_ k
  · intro j
    simp only [BalancedCriticalSpectrum.flip, join, Function.update_apply,
      Fin.append_left, Fin.append_right,
      (left_lt_right j i).ne, ite_false]
  · intro j
    by_cases h : j = i
    · subst j
      simp [BalancedCriticalSpectrum.flip, join]
    · have h' : j.natAdd 4 ≠ i.natAdd 4 := fun he =>
      h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he)))
      simp [BalancedCriticalSpectrum.flip, join, h, h']

private theorem sign_join_left (x : Q 4) (y : Q 5) (i : Fin 4) :
    truePrefixSign (join x y) (i.castAdd 5) = truePrefixSign x i := by
  simp only [truePrefixSign]
  rw [Finset.card_filter, Fin.sum_univ_add (a := 4) (b := 5)]
  simp only [Finset.card_filter, join, Fin.append_left, Fin.append_right, left_lt_left,
    right_not_lt_left, false_and, ite_false, Finset.sum_const_zero, add_zero]

private theorem sign_join_right (x : Q 4) (y : Q 5) (j : Fin 5) :
    truePrefixSign (join x y) (j.natAdd 4) = leftParitySign x * truePrefixSign y j := by
  simp only [truePrefixSign, leftParitySign]
  rw [Finset.card_filter, Fin.sum_univ_add (a := 4) (b := 5)]
  simp only [Finset.card_filter, join, Fin.append_left, Fin.append_right, left_lt_right,
    true_and, right_lt_right, pow_add]

/-- Split the Q9 signed row into the row within the fiber and the five moves between fibers. -/
theorem q9_signed_row_split {z : Q 9 → ℤ} (hz : ∀ u, signedRow z u = 3 * z u)
    (x : Q 4) (y : Q 5) :
    3 * fiber z y x = signedRow (fiber z y) x +
      leftParitySign x * ∑ j : Fin 5, truePrefixSign y j * fiber z (flip y j) x := by
  have h := hz (join x y)
  unfold signedRow at h
  rw [Fin.sum_univ_add (a := 4) (b := 5)] at h
  simpa only [signedRow, fiber, sign_join_left, sign_join_right, flip_join_left,
    flip_join_right, Finset.mul_sum, mul_assoc] using h.symm

/-- Outside the left projection of the support, every fiber has zero signed row. -/
theorem q9_signed_row_eq_zero_outside_projection {z : Q 9 → ℤ}
    (hz : ∀ u, signedRow z u = 3 * z u) {x : Q 4}
    (hzero : ∀ y : Q 5, fiber z y x = 0) (y : Q 5) : signedRow (fiber z y) x = 0 := by
  simpa only [hzero, mul_zero, Finset.sum_const_zero, add_zero] using
    (q9_signed_row_split hz x y).symm

/-- A balanced cubic support admits signed labels whose fiber rows vanish outside its
left projection. The labels also satisfy the ambient signed row at every vertex. -/
theorem q9_balanced_signed_projection {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      ∀ x : Q 4, (∀ y : Q 5, join x y ∉ C) → ∀ y : Q 5, signedRow (fiber z y) x = 0 := by
  obtain ⟨z, hunit, hzero, _, hz⟩ := q9_integral_true_prefix_switching hreg hb
  refine ⟨z, hunit, hzero, hz, ?_⟩
  intro x hx y
  exact q9_signed_row_eq_zero_outside_projection hz (x := x)
    (fun v => hzero (join x v) (hx v)) y

#print axioms q9_signed_row_split
#print axioms q9_balanced_signed_projection

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
