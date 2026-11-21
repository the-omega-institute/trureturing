/- GID: D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Binary cube adjacency has a coordinate contraction and an intrinsic preimage charge. -/

module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Coordinate moments and the shell span of the binary adjacency kernel.
In dimension eight, the moment gives the intrinsic preimage charge used in the
order-17 filter for the nine-cube case of Hong, Wu and Xia's Problem 2
(arXiv:2610.09483, Section 7). -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment

open Finset
open scoped BigOperators symmDiff

variable {n : ℕ}

/-- Unsigned cube adjacency over the binary field. -/
def adjacency (f : Finset (Fin n) → ZMod 2) (x : Finset (Fin n)) : ZMod 2 :=
  ∑ j : Fin n, f (x ∆ {j})

/-- The value of a vertex in coordinate `i`. -/
def coordinateBit (i : Fin n) (x : Finset (Fin n)) : ZMod 2 :=
  if i ∈ x then 1 else 0

private theorem coordinateBit_toggle (i j : Fin n) (x : Finset (Fin n)) :
    coordinateBit i (x ∆ {j}) = coordinateBit i x + if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst j
    by_cases hx : i ∈ x <;> simp [coordinateBit, mem_symmDiff, hx, ZModModule.add_self]
  · simp [coordinateBit, mem_symmDiff, h, Ne.symm h]

/-- In even dimension each coordinate moment of the adjacency image equals the
total binary charge of the preimage. -/
theorem coordinate_moment_adjacency (hn : Even n) (i : Fin n)
    (f : Finset (Fin n) → ZMod 2) :
    (∑ x, coordinateBit i x * adjacency f x) = ∑ x, f x := by
  have reindex (j : Fin n) :
      (∑ x, coordinateBit i x * f (x ∆ {j})) =
        ∑ x, coordinateBit i (x ∆ {j}) * f x := by
    let flip := Function.Involutive.toPerm (fun x : Finset (Fin n) => x ∆ {j})
      (fun x => symmDiff_symmDiff_cancel_right {j} x)
    apply Fintype.sum_equiv flip
    intro x
    change coordinateBit i x * f (x ∆ {j}) =
      coordinateBit i ((x ∆ {j}) ∆ {j}) * f (x ∆ {j})
    rw [symmDiff_symmDiff_cancel_right]
  have shell (x : Finset (Fin n)) : (∑ j : Fin n, coordinateBit i (x ∆ {j})) = 1 := by
    simp only [coordinateBit_toggle, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, hn.natCast_zmod_two, zero_mul, zero_add, sum_ite_eq', mem_univ, ite_true]
  calc
    (∑ x, coordinateBit i x * adjacency f x) =
        ∑ j : Fin n, ∑ x, coordinateBit i x * f (x ∆ {j}) := by
      simp only [adjacency, mul_sum]
      exact sum_comm
    _ = ∑ j : Fin n, ∑ x, coordinateBit i (x ∆ {j}) * f x :=
      sum_congr rfl fun j _ => reindex j
    _ = ∑ x, (∑ j : Fin n, coordinateBit i (x ∆ {j})) * f x := by
      simp only [sum_mul]
      exact sum_comm
    _ = ∑ x, f x := by simp only [shell, one_mul]

/-- Multiply by the coordinate bit and then pull back along its flip. -/
def coordinateContraction (i : Fin n) (f : Finset (Fin n) → ZMod 2)
    (x : Finset (Fin n)) : ZMod 2 :=
  coordinateBit i (x ∆ {i}) * f (x ∆ {i})

/-- The adjacency and the coordinate contraction anticommute to the identity. -/
theorem adjacency_coordinateContraction (i : Fin n) (f : Finset (Fin n) → ZMod 2) :
    adjacency (coordinateContraction i f) + coordinateContraction i (adjacency f) = f := by
  funext x
  change (∑ j : Fin n, coordinateBit i ((x ∆ {j}) ∆ {i}) * f ((x ∆ {j}) ∆ {i})) +
    coordinateBit i (x ∆ {i}) * (∑ j : Fin n, f ((x ∆ {i}) ∆ {j})) = f x
  rw [mul_sum, ← sum_add_distrib]
  calc
    _ = ∑ j : Fin n, (if j = i then 1 else 0) * f ((x ∆ {i}) ∆ {j}) := by
      apply sum_congr rfl
      intro j _
      have commute : (x ∆ {j}) ∆ {i} = (x ∆ {i}) ∆ {j} :=
        symmDiff_right_comm x {j} {i}
      rw [commute, ← add_mul, coordinateBit_toggle, add_right_comm,
        ZModModule.add_self, zero_add]
    _ = f x := by
      simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true,
        symmDiff_symmDiff_cancel_right]

/-- In even dimension binary cube adjacency squares to zero. Diagonal pairs
flip the same coordinate twice, and off-diagonal pairs cancel under swapping. -/
theorem adjacency_adjacency_eq_zero (hn : Even n) (f : Finset (Fin n) → ZMod 2) :
    adjacency (adjacency f) = 0 := by
  funext x
  let term (p : Fin n × Fin n) := f ((x ∆ {p.1}) ∆ {p.2})
  have diagonal : (∑ p ∈ univ.filter (fun p : Fin n × Fin n => p.2 = p.1), term p) = 0 := by
    rw [sum_filter, Fintype.sum_prod_type]
    simp only [term, Fintype.sum_ite_eq', symmDiff_symmDiff_cancel_right,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hn.natCast_zmod_two, zero_mul]
  have offDiagonal :
      (∑ p ∈ univ.filter (fun p : Fin n × Fin n => p.2 ≠ p.1), term p) = 0 := by
    refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      have commute : (x ∆ {p.1}) ∆ {p.2} = (x ∆ {p.2}) ∆ {p.1} :=
        symmDiff_right_comm x {p.1} {p.2}
      simp only [term, Prod.fst_swap, Prod.snd_swap, commute, ZModModule.add_self]
    · intro p hp _ hswap
      exact (mem_filter.mp hp).2 (congrArg Prod.fst hswap)
    · intro p hp
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2.symm⟩
    · intro p _
      exact Prod.swap_swap p
  change (∑ j : Fin n, ∑ k : Fin n, term (j, k)) = 0
  rw [← Fintype.sum_prod_type,
    ← sum_filter_add_sum_filter_not univ (fun p : Fin n × Fin n => p.2 = p.1) term,
    diagonal, offDiagonal, zero_add]

/-- A binary kernel word in positive even dimension is a sum of full neighbor
shells. The preimage given by the contraction selects their centers. -/
theorem adjacency_eq_zero_iff_exists_adjacency (hn : Even n) (i : Fin n)
    (f : Finset (Fin n) → ZMod 2) :
    adjacency f = 0 ↔ ∃ g : Finset (Fin n) → ZMod 2, adjacency g = f := by
  constructor
  · intro h
    refine ⟨coordinateContraction i f, ?_⟩
    funext x
    simpa [h, coordinateContraction] using congrFun (adjacency_coordinateContraction i f) x
  · rintro ⟨g, rfl⟩
    exact adjacency_adjacency_eq_zero hn g

end D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
