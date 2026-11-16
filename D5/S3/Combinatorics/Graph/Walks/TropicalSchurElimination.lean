/- GID: D5/S3/Combinatorics/Graph/Walks/TropicalSchurElimination
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/TropicalSchurElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Quiver.Path, mathlib/module/Mathlib.Basic.ENNReal.Basic]
   utility: none
   digest: Eliminating one vertex preserves all pivot walk distances for extended nonnegative weights. -/
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Tactic

/-! Finite-walk compression and expansion for min-plus vertex elimination. -/
set_option autoImplicit false
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination
universe u
variable {V : Type u}

/-- One directed arrow for every ordered pair; infinite weights represent missing edges. -/
abbrev completeQuiver (V : Type u) : Quiver.{0} V where
  Hom _ _ := PUnit

local instance (V : Type u) : Quiver.{0} V := completeQuiver V

/-- Finite directed walks, including the empty walk at each vertex. -/
abbrev Walk (a z : V) := @Quiver.Path V (completeQuiver V) a z

/-- The sum of the edge weights of a walk. -/
def weight (W : V → V → ℝ≥0∞) {a : V} : {z : V} → Walk a z → ℝ≥0∞
  | _, .nil => 0
  | z, @Quiver.Path.cons _ _ _ x _ p _ => weight W p + W x z

/-- The infimum over every finite walk, without assuming attainment. -/
noncomputable def distance (W : V → V → ℝ≥0∞) (a z : V) : ℝ≥0∞ :=
  ⨅ p : Walk a z, weight W p

/-- The min-plus Schur update on the vertices other than the eliminated vertex. -/
def schur (W : V → V → ℝ≥0∞) (b : V) (a z : {x : V // x ≠ b}) : ℝ≥0∞ :=
  min (W a z) (W a b + W b z)

private theorem expand (W : V → V → ℝ≥0∞) (b : V)
    {a z : {x : V // x ≠ b}} (q : Walk a z) :
    ∃ p : Walk a.val z.val, weight W p = weight (schur W b) q := by
  induction q with
  | nil => exact ⟨.nil, rfl⟩
  | @cons x z q e ih =>
    obtain ⟨p, hp⟩ := ih
    by_cases h : W x.val z.val ≤ W x.val b + W b z.val
    · refine ⟨p.cons PUnit.unit, ?_⟩
      simp only [weight, schur, min_eq_left h, hp]
    · refine ⟨(p.cons (c := b) PUnit.unit).cons PUnit.unit, ?_⟩
      simp only [weight, schur, min_eq_right (le_of_not_ge h), hp, add_assoc]

private theorem compress (W : V → V → ℝ≥0∞) (b : V)
    (a : {x : V // x ≠ b}) {z : V} (p : Walk a.val z) :
    (∀ hz : z ≠ b, ∃ q : Walk a ⟨z, hz⟩,
      weight (schur W b) q ≤ weight W p) ∧
    (z = b → ∃ x : {x : V // x ≠ b}, ∃ q : Walk a x,
      weight (schur W b) q + W x.val b ≤ weight W p) := by
  induction p with
  | nil =>
    constructor
    · intro hz
      exact ⟨.nil, le_rfl⟩
    · intro h
      exact (a.property h).elim
  | @cons x z p e ih =>
    by_cases hx : x = b
    · obtain ⟨y, q, hq⟩ := ih.2 hx
      constructor
      · intro hz
        refine ⟨q.cons PUnit.unit, ?_⟩
        calc
          weight (schur W b) (q.cons PUnit.unit) =
              weight (schur W b) q + schur W b y ⟨z, hz⟩ := rfl
          _ ≤ weight (schur W b) q + (W y.val b + W b z) :=
            add_le_add le_rfl (min_le_right _ _)
          _ = (weight (schur W b) q + W y.val b) + W b z := (add_assoc ..).symm
          _ ≤ weight W p + W x z := by
            simpa only [hx] using add_le_add hq (le_refl (W b z))
      · intro hz
        refine ⟨y, q, ?_⟩
        exact hq.trans (le_add_right le_rfl)
    · obtain ⟨q, hq⟩ := ih.1 hx
      constructor
      · intro hz
        refine ⟨q.cons PUnit.unit, ?_⟩
        exact add_le_add hq (min_le_left _ _)
      · intro hz
        refine ⟨⟨x, hx⟩, q, ?_⟩
        simpa only [weight, hz] using add_le_add hq (le_refl (W x b))

/-- Every original pivot walk has a reduced walk of no larger weight, every reduced
walk has an original expansion of exactly the same weight, and both distances agree. -/
theorem pivot_walks_and_distance (W : V → V → ℝ≥0∞) (b : V)
    (a z : {x : V // x ≠ b}) :
    (∀ p : Walk a.val z.val, ∃ q : Walk a z,
      weight (schur W b) q ≤ weight W p) ∧
    (∀ q : Walk a z, ∃ p : Walk a.val z.val,
      weight W p = weight (schur W b) q) ∧
    distance (schur W b) a z = distance W a.val z.val := by
  have hc : ∀ p : Walk a.val z.val, ∃ q : Walk a z,
      weight (schur W b) q ≤ weight W p :=
    fun p => (compress W b a p).1 z.property
  have he : ∀ q : Walk a z, ∃ p : Walk a.val z.val,
      weight W p = weight (schur W b) q := expand W b
  refine ⟨hc, he, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro p
    obtain ⟨q, hq⟩ := hc p
    exact (iInf_le (fun q : Walk a z => weight (schur W b) q) q).trans hq
  · apply le_iInf
    intro q
    obtain ⟨p, hp⟩ := he q
    exact (iInf_le (fun p : Walk a.val z.val => weight W p) p).trans_eq hp

end D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination
