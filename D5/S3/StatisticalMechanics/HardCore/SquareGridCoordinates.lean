/- GID: D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/SquareGridCoordinates
   mirror-E: none(waiver:exact-lattice-coordinate-transport)
   anchors: []
   utility: none
   digest: Actual square-grid recentering preserves independent partitions and marked ratios. -/

import D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
import D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory

/-- The infinite nearest-neighbor square grid on the already-owned integer
coordinate type. All four edges are specified explicitly. -/
def squareGrid : SimpleGraph Point where
  Adj p q :=
    (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨ (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨
    (p.2 + 1 = q.2 ∧ p.1 = q.1) ∨ (q.2 + 1 = p.2 ∧ p.1 = q.1)
  symm := ⟨by intro p q h; omega⟩
  loopless := ⟨by intro p h; omega⟩

instance : DecidableRel squareGrid.Adj := by
  intro p q
  change Decidable ((p.1 + 1 = q.1 ∧ p.2 = q.2) ∨
    (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨ (p.2 + 1 = q.2 ∧ p.1 = q.1) ∨
    (q.2 + 1 = p.2 ∧ p.1 = q.1))
  infer_instance

/-- Move an arbitrary marked root to the origin, without changing orientation. -/
def shiftTo (v : Point) : Point ≃ Point where
  toFun p := (p.1 - v.1, p.2 - v.2)
  invFun p := (p.1 + v.1, p.2 + v.2)
  left_inv := by intro p; ext <;> dsimp <;> omega
  right_inv := by intro p; ext <;> dsimp <;> omega

/-- The existing geometric recenter map is an actual bijection of grid vertices. -/
def recenterEquiv (d : Fin 3) : Point ≃ Point where
  toFun := recenter d
  invFun p := if d = 0 then (p.1 + 1, p.2)
    else if d = 1 then (p.2, -p.1 - 1) else (-p.2, p.1 + 1)
  left_inv := by
    intro p
    fin_cases d <;> ext <;> simp [recenter] <;> omega
  right_inv := by
    intro p
    fin_cases d <;> ext <;> simp [recenter] <;> omega

/-- Translation preserves and reflects every grid edge. -/
theorem shift_adj_iff (v p q : Point) :
    squareGrid.Adj (shiftTo v p) (shiftTo v q) ↔ squareGrid.Adj p q := by
  dsimp [squareGrid, shiftTo]
  omega

/-- The actual translation and quarter-turn used by memoryStep preserve and
reflect grid edges; no abstract graph-isomorphism premise is assumed. -/
theorem recenter_adj_iff (d : Fin 3) (p q : Point) :
    squareGrid.Adj (recenter d p) (recenter d q) ↔ squareGrid.Adj p q := by
  fin_cases d <;> simp [squareGrid, recenter] <;> omega

/-- The selected neighbor becomes the new origin. -/
theorem recenter_direction (d : Fin 3) : recenter d (direction d) = (0, 0) := by
  fin_cases d <;> norm_num [recenter, direction]

/-- The actual constant-activity independent-set sum on a finite grid domain. -/
abbrev gridPartition {R : Type*} [CommSemiring R] (V : Finset Point) (z : R) : R :=
  partition squareGrid V (fun _ => z)

/-- Marked vacancy ratio of actual grid partitions, over an arbitrary field.
At complex zeros field division is total; recursive cancellation below will
separately require all relevant proper-domain denominators to be nonzero. -/
def gridVacancy {K : Type*} [Field K] (V : Finset Point) (v : Point) (z : K) : K :=
  gridPartition (V.erase v) z / gridPartition V z

/-- Exact polynomial/complex partition invariance under the existing recenter map. -/
theorem partition_recenter {R : Type*} [CommSemiring R]
    (V : Finset Point) (d : Fin 3) (z : R) :
    gridPartition (V.image (recenter d)) z = gridPartition V z := by
  exact partition_relabel squareGrid squareGrid (recenterEquiv d)
    (recenter_adj_iff d) V (fun _ => z)

/-- The marked numerator and denominator both transport exactly. Equality
itself needs no nonzero hypothesis, because both sides use the same field division. -/
theorem vacancy_recenter {K : Type*} [Field K]
    (V : Finset Point) (v : Point) (d : Fin 3) (z : K) :
    gridVacancy (V.image (recenter d)) (recenter d v) z = gridVacancy V v z := by
  unfold gridVacancy
  have he := image_erase_equiv (recenterEquiv d) V v
  change (V.erase v).image (recenter d) =
    (V.image (recenter d)).erase (recenter d v) at he
  rw [← he, partition_recenter, partition_recenter]

/-- Every marked finite square-grid instance is exactly an origin-rooted
instance. The activity is constant; no unproved transport of inhomogeneous
weights or boundary conditions is hidden in this assertion. -/
theorem vacancy_shift {K : Type*} [Field K]
    (V : Finset Point) (v : Point) (z : K) :
    gridVacancy (V.image (shiftTo v)) (0, 0) z = gridVacancy V v z := by
  have hv : shiftTo v v = (0, 0) := by ext <;> simp [shiftTo]
  have he := image_erase_equiv (shiftTo v) V v
  rw [hv] at he
  unfold gridVacancy
  rw [← he]
  unfold gridPartition
  rw [partition_relabel squareGrid squareGrid (shiftTo v) (shift_adj_iff v),
    partition_relabel squareGrid squareGrid (shiftTo v) (shift_adj_iff v)]

/-- Before taking a child, the original root is always deleted. -/
theorem before_child_subset_erase (V : Finset Point) (a : Fin 6) (d : Fin 3) :
    V \ deleted a d ⊆ V.erase (0, 0) := by
  intro p hp
  obtain ⟨hpV, hpD⟩ := Finset.mem_sdiff.mp hp
  refine Finset.mem_erase.mpr ⟨?_, hpV⟩
  intro h
  subst p
  exact hpD (by simp [deleted])

/-- Every actual child domain is strictly smaller than a present-root domain.
This is the well-founded measure for the later complex nonvanishing induction. -/
theorem advance_card_lt (V : Finset Point) (h0 : (0, 0) ∈ V)
    (a : Fin 6) (d : Fin 3) : (advance V a d).card < V.card := by
  have hs := Finset.card_le_card (before_child_subset_erase V a d)
  have hi : (advance V a d).card ≤ (V \ deleted a d).card := Finset.card_image_le
  have he := Finset.card_erase_of_mem h0
  have hv : 0 < V.card := Finset.card_pos.mpr ⟨(0, 0), h0⟩
  omega

#print axioms shift_adj_iff
#print axioms recenter_adj_iff
#print axioms recenter_direction
#print axioms partition_recenter
#print axioms vacancy_recenter
#print axioms vacancy_shift
#print axioms before_child_subset_erase
#print axioms advance_card_lt

end D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
