/- GID: D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset]
   utility: none
   digest: Binary cube adjacency weights modulo four follow from preimage weights. -/

module

public import D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
public import Mathlib.Data.Nat.ModEq
import all D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! Modulo-four weights for binary adjacency images and kernels of cubes. -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight

open BinaryKernelCoordinateMoment Finset
open scoped BigOperators symmDiff

variable {n : ℕ}

/-- The Hamming weight of a binary function on the cube. -/
def weight (f : Finset (Fin n) → ZMod 2) : ℕ :=
  ∑ x, (f x).val

private theorem square_mod_four (k : ℕ) : k * k ≡ k % 2 [MOD 4] := by
  have h : (k ^ 2) % 4 = k % 2 := by exact_mod_cast Int.sq_emod_four (k : ℤ)
  change k * k % 4 = (k % 2) % 4
  rw [← pow_two, h, Nat.mod_eq_of_lt (by omega : k % 2 < 4)]

private theorem twice_correlation_eq_zero (f : Finset (Fin n) → ZMod 2)
    {i j : Fin n} (hij : i ≠ j) :
    (∑ x : Finset (Fin n), 2 * ((f (x ∆ {i})).val : ZMod 4) *
      ((f (x ∆ {j})).val : ZMod 4)) = 0 := by
  let translate (x : Finset (Fin n)) := (x ∆ {i}) ∆ {j}
  have swap (x : Finset (Fin n)) : translate x ∆ {i} = x ∆ {j} := by
    dsimp [translate]
    rw [symmDiff_right_comm x {i} {j}, symmDiff_symmDiff_cancel_right]
  refine sum_involution (fun x _ => translate x) ?_ ?_ (fun _ _ => mem_univ _) ?_
  · intro x _
    have swap' : translate x ∆ {j} = x ∆ {i} := symmDiff_symmDiff_cancel_right _ _
    rw [swap, swap']
    calc
      _ = (2 + 2 : ZMod 4) * ((f (x ∆ {i})).val : ZMod 4) *
          ((f (x ∆ {j})).val : ZMod 4) := by ring
      _ = 0 := by rw [show (2 + 2 : ZMod 4) = 0 by decide, zero_mul, zero_mul]
  · intro x _ _ h
    have htoggle : x ∆ {i} = x ∆ {j} := by
      calc
        x ∆ {i} = translate x ∆ {j} :=
          (symmDiff_symmDiff_cancel_right {j} (x ∆ {i})).symm
        _ = x ∆ {j} := congrArg (fun y => y ∆ {j}) h
    have heq : ({i} : Finset (Fin n)) = {j} := by
      have h' := congrArg (fun y => x ∆ y) htoggle
      simpa only [symmDiff_symmDiff_cancel_left] using h'
    exact hij (by simpa using heq)
  · intro x _
    change translate x ∆ {i} ∆ {j} = x
    rw [swap, symmDiff_symmDiff_cancel_right]

private theorem sum_shell_squares (f : Finset (Fin n) → ZMod 2) (s : Finset (Fin n)) :
    (∑ x : Finset (Fin n), (∑ i ∈ s, ((f (x ∆ {i})).val : ZMod 4)) ^ 2) =
      (s.card : ZMod 4) * (weight f : ZMod 4) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have diagonal : (∑ x : Finset (Fin n), ((f (x ∆ {i})).val : ZMod 4) ^ 2) =
        (weight f : ZMod 4) := by
      unfold weight
      rw [Nat.cast_sum]
      let flip := Function.Involutive.toPerm (fun x : Finset (Fin n) => x ∆ {i})
        (fun x => symmDiff_symmDiff_cancel_right {i} x)
      apply Fintype.sum_equiv flip
      intro x
      change ((f (x ∆ {i})).val : ZMod 4) ^ 2 = (f (x ∆ {i})).val
      generalize f (x ∆ {i}) = b
      have hb := ZMod.val_lt b
      generalize b.val = v at *
      interval_cases v <;> decide
    have cross :
        (∑ x : Finset (Fin n),
          2 * ((f (x ∆ {i})).val : ZMod 4) * ∑ j ∈ s, ((f (x ∆ {j})).val : ZMod 4)) =
          0 := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_eq_zero
      intro j hj
      exact twice_correlation_eq_zero f (fun h => hi (h.symm ▸ hj))
    simp only [sum_insert hi, add_sq, sum_add_distrib, diagonal, cross, add_zero, ih,
      card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_comm _ _

/-- The weight of the binary adjacency image is congruent modulo four to the
dimension times the preimage weight. -/
theorem weight_adjacency_mod_four (f : Finset (Fin n) → ZMod 2) :
    weight (adjacency f) ≡ n * weight f [MOD 4] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul]
  calc
    (weight (adjacency f) : ZMod 4) =
        ∑ x : Finset (Fin n), (∑ i : Fin n, ((f (x ∆ {i})).val : ZMod 4)) ^ 2 := by
      unfold weight
      rw [Nat.cast_sum]
      apply sum_congr rfl
      intro x _
      let k := ∑ i : Fin n, (f (x ∆ {i})).val
      have hcast : (k : ZMod 2) = adjacency f x := by
        simp [k, adjacency, Nat.cast_sum]
      have hval : (adjacency f x).val = k % 2 := by rw [← hcast, ZMod.val_natCast]
      rw [hval, ← Nat.cast_sum]
      simpa only [pow_two, Nat.cast_mul] using
        ((ZMod.natCast_eq_natCast_iff _ _ 4).2 (square_mod_four k)).symm
    _ = (n : ZMod 4) * (weight f : ZMod 4) := by
      simpa only [card_univ, Fintype.card_fin] using sum_shell_squares f univ

/-- In positive even dimension the image weight residue is read from any
coordinate moment. In dimension two modulo four it is twice the parity of
every preimage. -/
theorem weight_adjacency_mod_four_eq_coordinate_moment (hn : Even n) (i : Fin n)
    (f : Finset (Fin n) → ZMod 2) :
    weight (adjacency f) % 4 =
      (n % 4) * (∑ x, coordinateBit i x * adjacency f x).val := by
  have hw : (weight f : ZMod 2) = ∑ x, f x := by
    simp [weight, Nat.cast_sum]
  have hdim : n % 4 = 0 ∨ n % 4 = 2 := by
    obtain ⟨k, hk⟩ := hn
    omega
  rw [coordinate_moment_adjacency hn i, ← hw, ZMod.val_natCast]
  change weight (adjacency f) % 4 = _
  rw [show weight (adjacency f) % 4 = (n * weight f) % 4 from weight_adjacency_mod_four f,
    Nat.mul_mod n (weight f) 4]
  rcases hdim with hd | hd
  · simp [hd]
  · simp only [hd]
    omega

/-- In positive dimensions divisible by four, every binary adjacency kernel
word has weight divisible by four. -/
theorem four_dvd_weight_of_adjacency_eq_zero (hn : 4 ∣ n) (i : Fin n)
    (f : Finset (Fin n) → ZMod 2) (hf : adjacency f = 0) : 4 ∣ weight f := by
  have heven : Even n := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 4) hn)
  obtain ⟨g, rfl⟩ := (adjacency_eq_zero_iff_exists_adjacency heven i f).mp hf
  exact Nat.dvd_of_mod_eq_zero (by
    rw [weight_adjacency_mod_four_eq_coordinate_moment heven i, Nat.mod_eq_zero_of_dvd hn,
      zero_mul])

#print axioms weight_adjacency_mod_four
#print axioms weight_adjacency_mod_four_eq_coordinate_moment
#print axioms four_dvd_weight_of_adjacency_eq_zero

end D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
