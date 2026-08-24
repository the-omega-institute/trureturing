/- GID: D5/S3/ConceptDynamics/DefinitionEscape/ConstructiveDiagonalEscape
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/ConstructiveDiagonalEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical twisted diagonal escapes every supplied catalog. -/

import D5.S0.Diagonal.Naturality.RelativeDiagonalEscape

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `relative_diagonal_escape` has the source's arbitrary
     carriers, fixed-point-free twist, canonical twisted diagonal, and range
     exclusion conclusion. It is imported and applied directly below.
   * `QualitativeEscape.escaped_of_fixedPointFree` is an equivalent family hit
     through the `IsEscaped` abbreviation, but the direct range theorem is the
     thinner wrapper for this source statement.
   * Pinned Mathlib has `Set.mem_range`,
     `Function.exists_fixed_point_of_surjective`, and Cantor theorems, but the
     exact-hit audit found no full-statement upstream declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.ConstructiveDiagonalEscape

open D5.S0.Diagonal
open D5.S0.Diagonal.Naturality.RelativeDiagonalEscape

/-- The fixed-point-free twist of a catalog's diagonal entries is not any row
of that catalog. -/
theorem constructive_diagonal_escape
    {A Y : Type*} (catalog : A -> A -> Y) (twist : Y -> Y)
    (fixedPointFree : forall value, twist value ≠ value) :
    EscapeCount.diagonal twist catalog ∉ Set.range catalog := by
  exact relative_diagonal_escape catalog twist fixedPointFree

#print axioms constructive_diagonal_escape

end D5.S3.ConceptDynamics.DefinitionEscape.ConstructiveDiagonalEscape
