/- GID: D5/S3/Observer/Sheaf/FiniteObserverSheaf
   generality: G
   mirror-B: D5/B/S3/Observer/Sheaf/FiniteObserverSheaf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite observer restrictions form a cellular zero-to-one coboundary whose kernel is the compatible-section space. -/

import D5.S3.ConceptDynamics.Gluing.SheafPairwiseEqualizer
import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic

/-!
# Finite observer sheaf cochains

The categorical sheaf equalizer already frozen in the repository identifies
global sections with compatible local families.  This module supplies a finite
computable cellular shadow for observer networks.

Every vertex carries a local observation vector in `V`, every edge carries an
overlap vector in `W`, and each endpoint has a linear restriction to the edge.
The zero-to-one coboundary is the target restriction minus the source
restriction.  Its kernel is exactly the space of compatible observer
families.

This file does not redefine a Grothendieck-topology sheaf, prove a comparison
with derived sheaf cohomology, or construct higher cochains.  It is the finite
linear interface used by the following Laplacian and obstruction layers.
-/

/- Library-search audit trail (2026-09-01):
   * `SheafPairwiseEqualizer` owns the genuine Mathlib sheaf equalizer and
     unique gluing theorem.  It is imported as the categorical owner.
   * `ToroidalCechCompletion` owns a specialized analytic gluing result.
   * Repository search found no finite observer-network coboundary whose
     kernel is the compatible local-section space.
   * Pinned Mathlib supplies linear maps and pointwise module structures. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Sheaf.FiniteObserverSheaf

universe u v w x y

/-- A finite cellular observer network with one vertex stalk type and one edge
stalk type. -/
structure ObserverNetwork
    (R : Type u) (Vertex : Type v) (Edge : Type w)
    (V : Type x) (W : Type y)
    [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] where
  source : Edge → Vertex
  target : Edge → Vertex
  sourceRestriction : Edge → (V →ₗ[R] W)
  targetRestriction : Edge → (V →ₗ[R] W)

variable {R : Type u} {Vertex : Type v} {Edge : Type w}
variable {V : Type x} {W : Type y}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Vertex-valued local observer family. -/
abbrev ZeroCochain := Vertex → V

/-- Edge-valued overlap defect family. -/
abbrev OneCochain := Edge → W

/-- Zero-to-one cellular coboundary of a finite observer network. -/
def observerCoboundary
    (network : ObserverNetwork R Vertex Edge V W) :
    ZeroCochain (Vertex := Vertex) (V := V) →ₗ[R]
      OneCochain (Edge := Edge) (W := W) where
  toFun section edge :=
    network.targetRestriction edge (section (network.target edge)) -
      network.sourceRestriction edge (section (network.source edge))
  map_add' first second := by
    funext edge
    simp
  map_smul' scalar section := by
    funext edge
    simp

/-- Pairwise compatibility of all local observer values on every overlap. -/
def Compatible
    (network : ObserverNetwork R Vertex Edge V W)
    (section : ZeroCochain (Vertex := Vertex) (V := V)) : Prop :=
  ∀ edge,
    network.targetRestriction edge (section (network.target edge)) =
      network.sourceRestriction edge (section (network.source edge))

/-- The compatible-section space is the kernel of the cellular coboundary. -/
def compatibleSections
    (network : ObserverNetwork R Vertex Edge V W) :
    Submodule R (ZeroCochain (Vertex := Vertex) (V := V)) :=
  LinearMap.ker (observerCoboundary network)

/-- Pairwise observer compatibility is exactly vanishing coboundary. -/
theorem compatible_iff_coboundary_eq_zero
    (network : ObserverNetwork R Vertex Edge V W)
    (section : ZeroCochain (Vertex := Vertex) (V := V)) :
    Compatible network section ↔ observerCoboundary network section = 0 := by
  constructor
  · intro hCompatible
    funext edge
    simp [observerCoboundary, hCompatible edge]
  · intro hZero edge
    have hEdge := congrFun hZero edge
    change
      network.targetRestriction edge (section (network.target edge)) -
          network.sourceRestriction edge (section (network.source edge)) = 0
      at hEdge
    exact sub_eq_zero.mp hEdge

/-- Membership in the compatible-section submodule is the compatibility
predicate. -/
theorem mem_compatibleSections_iff
    (network : ObserverNetwork R Vertex Edge V W)
    (section : ZeroCochain (Vertex := Vertex) (V := V)) :
    section ∈ compatibleSections network ↔ Compatible network section := by
  rw [compatibleSections, LinearMap.mem_ker,
    ← compatible_iff_coboundary_eq_zero]

/-- The zero local observer family is compatible. -/
theorem zero_compatible
    (network : ObserverNetwork R Vertex Edge V W) :
    Compatible network (0 : ZeroCochain (Vertex := Vertex) (V := V)) := by
  intro edge
  simp

/-- Compatible observer families are closed under addition. -/
theorem compatible_add
    (network : ObserverNetwork R Vertex Edge V W)
    {first second : ZeroCochain (Vertex := Vertex) (V := V)}
    (hFirst : Compatible network first)
    (hSecond : Compatible network second) :
    Compatible network (first + second) := by
  rw [compatible_iff_coboundary_eq_zero] at hFirst hSecond ⊢
  simp [hFirst, hSecond]

/-- Compatible observer families are closed under scalar multiplication. -/
theorem compatible_smul
    (network : ObserverNetwork R Vertex Edge V W)
    (scalar : R) {section : ZeroCochain (Vertex := Vertex) (V := V)}
    (hSection : Compatible network section) :
    Compatible network (scalar • section) := by
  rw [compatible_iff_coboundary_eq_zero] at hSection ⊢
  simp [hSection]

/-- With identical endpoint restrictions, every constant observer family is
compatible. -/
theorem constant_compatible_of_same_restriction
    (network : ObserverNetwork R Vertex Edge V W)
    (hSame : ∀ edge,
      network.targetRestriction edge = network.sourceRestriction edge)
    (value : V) :
    Compatible network (fun _ => value) := by
  intro edge
  rw [hSame edge]

example :
    let network : ObserverNetwork ℤ Unit Unit ℤ ℤ :=
      { source := fun _ => ()
        target := fun _ => ()
        sourceRestriction := fun _ => LinearMap.id
        targetRestriction := fun _ => LinearMap.id }
    Compatible network (fun _ => 1) := by
  intro network
  exact constant_compatible_of_same_restriction network
    (fun _ => rfl) 1

#print axioms compatible_iff_coboundary_eq_zero
#print axioms mem_compatibleSections_iff
#print axioms zero_compatible
#print axioms compatible_add
#print axioms compatible_smul
#print axioms constant_compatible_of_same_restriction

end D5.S3.Observer.Sheaf.FiniteObserverSheaf
