/- GID: D5/S3/ConceptDynamics/Coding/SymbolicCylinderShift
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/SymbolicCylinderShift
   mirror-E: none(waiver:symbolic-topological-bridge)
   anchors: []
   utility: none
   digest: Clopen cylinders and their exact pullback under the symbolic shift. -/

import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion (shift)

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace V] [DiscreteTopology V]
variable [TopologicalSpace E] [DiscreteTopology E]

/-- A finite-coordinate cylinder is closed in the actual legal history space. -/
theorem cylinder_closed (s : Finset ℤ) (x : History G) :
    IsClosed (cylinder G s x) := by
  have he : cylinder G s x = Subtype.val ⁻¹' (s : Set ℤ).pi (fun k => {x.val k}) := by
    ext y
    simp [cylinder, Set.mem_pi]
  rw [he]
  exact (isClosed_set_pi (fun k _ => isClosed_discrete _)).preimage
    continuous_subtype_val

/-- Cylinders are clopen: they are the finite symbolic coordinates of a history. -/
theorem cylinder_isClopen (s : Finset ℤ) (x : History G) :
    IsClopen (cylinder G s x) :=
  ⟨cylinder_closed G s x, cylinder_open G s x⟩

/-- Cylinders form a local basis for the subspace topology on legal histories. -/
theorem exists_cylinder_subset {U : Set (History G)} {x : History G}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ s : Finset ℤ, x ∈ cylinder G s x ∧ cylinder G s x ⊆ U := by
  obtain ⟨W, hW, hpre⟩ := isOpen_induced_iff.mp hU
  have hxW : x.val ∈ W := by
    change x ∈ Subtype.val ⁻¹' W
    rw [hpre]
    exact hx
  obtain ⟨s, I, hI, hsub⟩ := isOpen_pi_iff.mp hW x.val hxW
  refine ⟨s, ?_, ?_⟩
  · intro k hk
    rfl
  · intro y hy
    have hyW : y.val ∈ W := hsub (by
      intro k hk
      rw [hy k hk]
      exact (hI k hk).2)
    rw [← hpre]
    exact hyW

/-- The preimage of a cylinder under the left shift is exactly the cylinder on the
shifted coordinates, centered at the inverse translate of its base point. -/
theorem shift_preimage_cylinder (s : Finset ℤ) (x : History G) :
    shift G ⁻¹' cylinder G s x =
      cylinder G (s.image (fun k : ℤ => k + 1)) (translate G (-1) x) := by
  ext y
  constructor
  · intro hy k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hcoord := hy j hj
    simpa [shift, translate] using hcoord
  · intro hy k hk
    have hmem : k + 1 ∈ s.image (fun j : ℤ => j + 1) :=
      Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hcoord := hy (k + 1) hmem
    simpa [shift, translate] using hcoord

end D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms

#print axioms D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms.cylinder_closed
#print axioms D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms.cylinder_isClopen
#print axioms D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms.exists_cylinder_subset
#print axioms D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms.shift_preimage_cylinder
