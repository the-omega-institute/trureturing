/- GID: D5/S3/Topology/CrossedExtremalProfiles
   generality: G
   mirror-B: D5/B/S3/Topology/CrossedExtremalProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fin.VecNotation]
   utility: none
   digest: The crossed extremal incidence has a categorical partition. -/

module

public import D5.S3.Topology.FiniteCategoricalCoverCertificate
public import D5.S3.Topology.SubdivisionCategoricalCover
public import Mathlib.Data.Fin.VecNotation

import OmegaBuild.Commands

/-!
Omega original.

The twelve-point core in which the minima give a doubled matching
of intermediate points and the maxima give the complementary four-cycle.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Topology.CrossedExtremalProfiles

open D5.S3.Topology.ConnectedCategoryGraft
open D5.S3.Topology.SubdivisionCategoricalCover
open D5.S3.Topology.FiniteCategoricalCoverCertificate

/-- Lower-set masks for the crossed matching and four-cycle incidence. -/
def table (x y : Fin 12) : Bool :=
  ((![1, 2, 4, 8, 19, 35, 76, 140, 351, 671, 1135, 2223] : Fin 12 → ℕ) y).testBit x.val

private def left (x : Fin 12) : Bool := (95 : ℕ).testBit x.val
private def right (x : Fin 12) : Bool := !left x

private def leftSteps : List (Fin 12 → Fin 12) :=
  [![4, 1, 2, 3, 4, 0, 6, 0, 0, 0, 0, 0],
   ![4, 4, 2, 3, 4, 0, 6, 0, 0, 0, 0, 0],
   ![4, 4, 6, 3, 4, 0, 6, 0, 0, 0, 0, 0],
   ![4, 4, 6, 6, 4, 0, 6, 0, 0, 0, 0, 0],
   ![8, 8, 6, 6, 8, 0, 6, 0, 0, 0, 0, 0],
   ![6, 6, 6, 6, 6, 0, 6, 0, 0, 0, 0, 0]]

private def rightSteps : List (Fin 12 → Fin 12) :=
  [![0, 0, 0, 0, 0, 5, 0, 7, 8, 7, 10, 11],
   ![0, 0, 0, 0, 0, 5, 0, 11, 8, 11, 10, 11],
   ![0, 0, 0, 0, 0, 5, 0, 11, 8, 11, 5, 11],
   ![0, 0, 0, 0, 0, 11, 0, 11, 8, 11, 11, 11],
   ![0, 0, 0, 0, 0, 11, 0, 11, 0, 11, 11, 11],
   ![0, 0, 0, 0, 0, 11, 0, 11, 11, 11, 11, 11]]

/-- The relation masks define a partial order. -/
theorem valid : ValidOrder table := by decide +kernel

/-- The crossed incidence has a two-piece categorical lower cover after
two subdivisions. Each piece has an explicit contraction in the table order. -/
theorem hasCategoricalCover_double_subdivision :
    letI : PartialOrder (Fin 12) := tableOrder table valid
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains (Fin 12))) 2 := by
  let : PartialOrder (Fin 12) := tableOrder table valid
  apply SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision
    (A := {x | left x = true}) (B := {x | right x = true})
  · exact categorical_of_table valid (U := left) (c := 6) (steps := leftSteps)
      (by decide +kernel)
  · exact categorical_of_table valid (U := right) (c := 11) (steps := rightSteps)
      (by decide +kernel)
  · intro x
    by_cases hx : left x = true
    · exact Or.inl hx
    · exact Or.inr (by simpa [right] using hx)

end D5.S3.Topology.CrossedExtremalProfiles
