/- GID: D5/S3/Factorization/Galois/PowerCompactness
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/PowerCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered power width realizes a verbal subgroup as a compact closed image. -/
import D5.S3.Factorization.Galois.NormalCorePower
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.List.FinRange

set_option autoImplicit false

open D5.S3.Factorization.Galois.NormalCorePower

namespace D5.S3.Factorization.Galois.PowerCompactness

variable {G : Type*} [Group G]

/-- Ordered product of `w` powers, with no commutativity assumption. -/
def powerProduct (m w : ℕ) (a : Fin w → G) : G :=
  ((List.finRange w).map (fun i => a i ^ m)).prod

/-- Algebraic width is an ordinary hypothesis, not a topological openness premise. -/
def HasPowerWidth (G : Type*) [Group G] (m w : ℕ) : Prop :=
  ∀ g ∈ powerSubgroup G m, ∃ a : Fin w → G, powerProduct m w a = g

theorem powerProduct_mem (m w : ℕ) (a : Fin w → G) :
    powerProduct m w a ∈ powerSubgroup G m := by
  apply (powerSubgroup G m).list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact pow_mem_powerSubgroup m (a i)

theorem range_powerProduct_eq (m w : ℕ) (hwidth : HasPowerWidth G m w) :
    Set.range (powerProduct (G := G) m w) = (powerSubgroup G m : Set G) := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact powerProduct_mem m w a
  · exact hwidth g

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_powerProduct (m w : ℕ) :
    Continuous (powerProduct (G := G) m w) :=
  continuous_list_prod (List.finRange w) (fun i _ => (continuous_apply i).pow m)

/-- A bounded algebraic power width realizes the verbal subgroup as a compact finite-product
image. This proves closedness in any compact Hausdorff topological group. -/
theorem isClosed_powerSubgroup_of_width [CompactSpace G] [T2Space G]
    (m w : ℕ) (hwidth : HasPowerWidth G m w) :
    IsClosed (powerSubgroup G m : Set G) := by
  rw [← range_powerProduct_eq m w hwidth]
  exact (isCompact_range (continuous_powerProduct m w)).isClosed

/-- Closedness plus an explicitly finite quotient gives openness, using Mathlib's
closed finite-index subgroup theorem. -/
theorem isOpen_powerSubgroup_of_closed_finite (m : ℕ)
    (hclosed : IsClosed (powerSubgroup G m : Set G))
    (hfinite : Finite (G ⧸ powerSubgroup G m)) :
    IsOpen (powerSubgroup G m : Set G) := by
  have := hfinite
  have : (powerSubgroup G m).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact (powerSubgroup G m).isOpen_of_isClosed_of_finiteIndex hclosed

end D5.S3.Factorization.Galois.PowerCompactness
