/- GID: D5/S3/ConceptDynamics/Attribution/AxisBudgets/CoordinateRelabel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/AxisBudgets/CoordinateRelabel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Coordinate relabeling preserves feasibility of every single-coordinate seed budget. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor

open Finset
open D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel

variable {d : ℕ}

private def mapAxis (σ : Equiv.Perm (Fin d)) (i : Fin d) (A : AxisSubset d i) :
    AxisSubset d (σ i) :=
  ⟨A.val.map σ.toEmbedding, by
    intro hi
    obtain ⟨x, hx, he⟩ := mem_map.mp hi
    exact A.property (σ.injective he ▸ hx)⟩

private def unmapAxis (σ : Equiv.Perm (Fin d)) (i : Fin d) (A : AxisSubset d (σ i)) :
    AxisSubset d i :=
  ⟨A.val.map σ.symm.toEmbedding, by
    intro hi
    obtain ⟨x, hx, he⟩ := mem_map.mp hi
    have e : x = σ i := by simpa using congrArg σ he
    exact A.property (e ▸ hx)⟩

private def reindexAxis (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    AxisSubset d i ≃ AxisSubset d (σ i) where
  toFun := mapAxis σ i
  invFun := unmapAxis σ i
  left_inv A := by
    apply Subtype.ext
    simp [mapAxis, unmapAxis, map_map]
  right_inv A := by
    apply Subtype.ext
    simp [mapAxis, unmapAxis, map_map]

private theorem reindex_axis_top (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    reindexAxis σ i (axisTop i) = axisTop (σ i) := by
  apply Subtype.ext
  change (univ.erase i).map σ.toEmbedding = univ.erase (σ i)
  rw [map_erase]
  simp

private theorem reindex_axis_feasibility (σ : Equiv.Perm (Fin d)) (i : Fin d) (k b : ℕ)
    (h : axisFactorWithin k i b) : axisFactorWithin k (σ i) b := by
  obtain ⟨f, selected, loop, enough, row, col, support, cost⟩ := h
  let E := reindexAxis σ i
  let g : AxisSubset d (σ i) → AxisSubset d (σ i) → Bool :=
    fun a b => f (E.symm a) (E.symm b)
  have pivot : E (axisTop i) = axisTop (σ i) := reindex_axis_top σ i
  have card (a : AxisSubset d i) : (E a).val.card = a.val.card :=
    card_map _
  have rowSum (a : AxisSubset d i) :
      (∑ c, (g (E a) c).toNat) = ∑ c, (f a c).toNat := by
    rw [← E.sum_comp (fun c => (g (E a) c).toNat)]
    simp [g]
  have colSum (b : AxisSubset d i) :
      (∑ c, (g c (E b)).toNat) = ∑ c, (f c b).toNat := by
    rw [← E.sum_comp (fun c => (g c (E b)).toNat)]
    simp [g]
  have costs : axisCost (σ i) g = axisCost i f := by
    let score (a b : AxisSubset d (σ i)) : ℕ :=
      if a ≠ axisTop (σ i) ∧ a.val.card % 2 = 1 ∧ b.val.card % 2 = 1 then
        (g a b).toNat else 0
    unfold axisCost
    change 4 * (1 + ∑ a, ∑ b, score a b) = _
    rw [← E.sum_comp (fun a => ∑ b, score a b)]
    apply congrArg (fun x : ℕ => 4 * (1 + x))
    apply sum_congr rfl
    intro a _
    rw [← E.sum_comp (score (E a))]
    simp [score, ← pivot, card, g]
  refine ⟨g, selected, ?_, enough, ?_, ?_, ?_, costs.trans_le cost⟩
  · simpa only [← pivot, g, E.symm_apply_apply] using loop
  · intro a
    obtain ⟨a, rfl⟩ := E.surjective a
    simpa only [rowSum, ← pivot, E.injective.eq_iff] using row a
  · intro b
    obtain ⟨b, rfl⟩ := E.surjective b
    simpa only [colSum, ← pivot, E.injective.eq_iff] using col b
  · intro a b ha hab
    obtain ⟨a, rfl⟩ := E.surjective a
    obtain ⟨b, rfl⟩ := E.surjective b
    have ha' : a ≠ axisTop i := fun h => ha ((congrArg E h).trans pivot)
    have hab' : f a b = true := by simpa [g] using hab
    exact map_subset_map.mpr (support a b ha' hab')

/-- Relabeling the marked coordinate transports a feasible factor without changing its cost. -/
theorem axis_feasibility_iff (i j : Fin d) (k b : ℕ) :
    axisFactorWithin k i b ↔ axisFactorWithin k j b := by
  constructor
  · intro h
    simpa using reindex_axis_feasibility (Equiv.swap i j) i k b h
  · intro h
    simpa using reindex_axis_feasibility (Equiv.swap j i) j k b h

end D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel
