/- GID: D5/S1/Dynamics/Symbolic/AlphabetFactor
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous alphabet maps induce compact shift-equivariant factor subshifts. -/

import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Separation.Hausdorff

open Set Function
open SymbolicDynamics

namespace D5.S1.Dynamics.Symbolic.AlphabetFactor

universe u v w

variable {A : Type u} {B : Type v} {G : Type w}
variable [AddMonoid G] [TopologicalSpace A] [TopologicalSpace B]

/-! ### Coordinatewise maps and the shift factor law -/

/-- Apply an alphabet map independently at every coordinate of a configuration. -/
def alphabetMap (f : A → B) (x : G → A) : G → B := fun i => f (x i)

/-- A continuous alphabet map induces a continuous map of full shifts. -/
theorem continuous_alphabetMap {f : A → B} (hf : Continuous f) :
    Continuous (alphabetMap (G := G) f) := by
  unfold alphabetMap
  exact continuous_pi (fun i => hf.comp (continuous_apply i))

/-- Coordinatewise alphabet maps commute with every translation shift. -/
theorem alphabetMap_shift (f : A → B) (g : G) (x : G → A) :
    alphabetMap f (SymbolicDynamics.FullShift.shift g x) =
      SymbolicDynamics.FullShift.shift g (alphabetMap f x) := by
  ext i
  rfl

/-- The coordinatewise map is a semiconjugacy for each translation. -/
theorem alphabetMap_semiconj (f : A → B) (g : G) :
    Semiconj (alphabetMap (G := G) f)
      (SymbolicDynamics.FullShift.shift g)
      (SymbolicDynamics.FullShift.shift g) := by
  intro x
  exact alphabetMap_shift f g x

/-! ### Compact closed images and subshift factors -/

/-- The image of a closed subshift under a continuous alphabet map is closed when
the source alphabet is compact and the target alphabet is Hausdorff. -/
theorem isClosed_image_subshift [CompactSpace A] [T2Space B]
    {f : A → B} (hf : Continuous f)
    (X : SymbolicDynamics.FullShift.Subshift A G) :
    IsClosed (alphabetMap f '' X.carrier) := by
  exact (X.isClosed.isCompact.image (continuous_alphabetMap hf)).isClosed

/-- The image of a shift-invariant set under a coordinatewise alphabet map is
shift-invariant. -/
theorem mapsTo_image_subshift {f : A → B}
    (X : SymbolicDynamics.FullShift.Subshift A G) (g : G) :
    MapsTo (SymbolicDynamics.FullShift.shift g)
      (alphabetMap f '' X.carrier) (alphabetMap f '' X.carrier) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨SymbolicDynamics.FullShift.shift g x, X.mapsTo g hx, ?_⟩
  exact (alphabetMap_shift f g x).symm

/-- A continuous alphabet map sends a compact-alphabet subshift to a subshift. -/
def mapSubshift [CompactSpace A] [T2Space B]
    (f : A → B) (hf : Continuous f)
    (X : SymbolicDynamics.FullShift.Subshift A G) :
    SymbolicDynamics.FullShift.Subshift B G where
  carrier := alphabetMap f '' X.carrier
  isClosed := isClosed_image_subshift hf X
  mapsTo := mapsTo_image_subshift X

@[simp]
theorem mapSubshift_carrier [CompactSpace A] [T2Space B]
    (f : A → B) (hf : Continuous f)
    (X : SymbolicDynamics.FullShift.Subshift A G) :
    (mapSubshift f hf X).carrier = alphabetMap f '' X.carrier := rfl

#print axioms continuous_alphabetMap
#print axioms alphabetMap_shift
#print axioms alphabetMap_semiconj
#print axioms isClosed_image_subshift
#print axioms mapsTo_image_subshift
#print axioms mapSubshift

end D5.S1.Dynamics.Symbolic.AlphabetFactor
