/- GID: D5/S3/Combinatorics/Graph/Hypercube/BinaryFaceMoments
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/BinaryFaceMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset]
   utility: none
   digest: Face moments characterize the parity eigenvalue equation for binary cube adjacency. -/

module

public import D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
import all D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Binary adjacency acts on positive-face moments by the dimension scalar
and one-coordinate deletions. The moments retain the whole cube word. -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments

open BinaryKernelCoordinateMoment Finset
open scoped BigOperators symmDiff

variable {n : ℕ}

/-- The sum of a cube word over the face with all coordinates in `S` equal to one. -/
@[expose] def faceMoment (f : Finset (Fin n) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  ∑ x, (∏ i ∈ S, coordinateBit i x) * f x

private theorem faceWeight_toggle (S x : Finset (Fin n)) (j : Fin n) :
    (∏ i ∈ S, coordinateBit i (x ∆ {j})) =
      (∏ i ∈ S, coordinateBit i x) +
        if j ∈ S then ∏ i ∈ S.erase j, coordinateBit i x else 0 := by
  by_cases hj : j ∈ S
  · have hrest : (∏ i ∈ S.erase j, coordinateBit i (x ∆ {j})) =
        ∏ i ∈ S.erase j, coordinateBit i x := by
      apply prod_congr rfl
      intro i hi
      simp [coordinateBit_toggle, Ne.symm (ne_of_mem_erase hi)]
    rw [ite_eq_left hj, ← mul_prod_erase S (fun i => coordinateBit i (x ∆ {j})) hj,
      ← mul_prod_erase S (fun i => coordinateBit i x) hj, hrest, coordinateBit_toggle]
    simp [add_mul]
  · rw [ite_eq_right hj, add_zero]
    apply prod_congr rfl
    intro i hi
    have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
    simp [coordinateBit_toggle, hji]

/-- Adjacency contributes the dimension scalar and the moments obtained by
deleting one prescribed coordinate. -/
theorem faceMoment_adjacency (f : Finset (Fin n) → ZMod 2) (S : Finset (Fin n)) :
    faceMoment (adjacency f) S =
      (n : ZMod 2) * faceMoment f S + ∑ i ∈ S, faceMoment f (S.erase i) := by
  calc
    faceMoment (adjacency f) S =
        ∑ j : Fin n, ∑ x, (∏ i ∈ S, coordinateBit i x) * f (x ∆ {j}) := by
      simp only [faceMoment, adjacency, mul_sum]
      exact sum_comm
    _ = ∑ j : Fin n, ∑ x, (∏ i ∈ S, coordinateBit i (x ∆ {j})) * f x := by
      apply sum_congr rfl
      intro j _
      let flip := Function.Involutive.toPerm (fun x : Finset (Fin n) => x ∆ {j})
        (fun x => symmDiff_symmDiff_cancel_right {j} x)
      apply Fintype.sum_equiv flip
      intro x
      change (∏ i ∈ S, coordinateBit i x) * f (x ∆ {j}) =
        (∏ i ∈ S, coordinateBit i ((x ∆ {j}) ∆ {j})) * f (x ∆ {j})
      rw [symmDiff_symmDiff_cancel_right]
    _ = ∑ j : Fin n, (faceMoment f S + if j ∈ S then faceMoment f (S.erase j) else 0) := by
      apply sum_congr rfl
      intro j _
      by_cases hj : j ∈ S <;>
        simp [faceWeight_toggle, hj, faceMoment, add_mul, sum_add_distrib]
    _ = _ := by
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← sum_filter, filter_mem_eq_inter, univ_inter]

private theorem faceMoment_eq_sum_filter (f : Finset (Fin n) → ZMod 2)
    (S : Finset (Fin n)) :
    faceMoment f S = ∑ x ∈ univ.filter (S ⊆ ·), f x := by
  rw [faceMoment, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases h : S ⊆ x
  · have hprod : (∏ i ∈ S, coordinateBit i x) = 1 :=
      prod_eq_one fun i hi => by simp [coordinateBit, h hi]
    simp [h, hprod]
  · obtain ⟨i, hi, hx⟩ := Finset.not_subset.mp h
    have hprod : (∏ j ∈ S, coordinateBit j x) = 0 :=
      prod_eq_zero hi (by simp [coordinateBit, hx])
    simp [h, hprod]

private theorem faceMoment_injective (n : ℕ) :
    Function.Injective (faceMoment (n := n)) := by
  intro f g hfg
  have hzero (S : Finset (Fin n)) : faceMoment (f - g) S = 0 := by
    simp only [faceMoment, Pi.sub_apply, mul_sub, sum_sub_distrib]
    change faceMoment f S - faceMoment g S = 0
    rw [hfg, sub_self]
  have hcard (x : Finset (Fin n)) : x.card ≤ n := by
    simpa using card_le_card (subset_univ x)
  have hdiff (x : Finset (Fin n)) : (f - g) x = 0 := by
    refine x.strongDownwardInductionOn (n := n) ?_ (hcard x)
    intro S ih _
    have hS := hzero S
    rw [faceMoment_eq_sum_filter, sum_eq_single S] at hS
    · exact hS
    · intro x hx hne
      exact ih (hcard x) (ssubset_of_subset_of_ne (mem_filter.mp hx).2 hne.symm)
    · simp
  exact sub_eq_zero.mp (funext hdiff)

/-- Every deletion sum vanishes exactly on the binary kernel in even dimension
and on the binary fixed space in odd dimension. -/
theorem adjacency_eq_dim_smul_iff (f : Finset (Fin n) → ZMod 2) :
    adjacency f = (n : ZMod 2) • f ↔
      ∀ S : Finset (Fin n), (∑ i ∈ S, faceMoment f (S.erase i)) = 0 := by
  have hsmul (S : Finset (Fin n)) :
      faceMoment ((n : ZMod 2) • f) S = (n : ZMod 2) * faceMoment f S := by
    rw [faceMoment, faceMoment, mul_sum]
    apply sum_congr rfl
    intro x _
    simp only [Pi.smul_apply, smul_eq_mul]
    ac_rfl
  constructor
  · intro hf S
    have h := faceMoment_adjacency f S
    rw [hf, hsmul] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  · intro h
    apply faceMoment_injective n
    funext S
    rw [faceMoment_adjacency, h, add_zero, hsmul]

#print axioms faceMoment_adjacency
#print axioms adjacency_eq_dim_smul_iff

end D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments
