/- GID: D5/S3/ConceptDynamics/DefinitionEscape/ConstructiveDiagonalEscape
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/ConstructiveDiagonalEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical twisted diagonal escapes every supplied catalog. -/

module
prelude
public import D5.S0.Diagonal.Naturality.RelativeDiagonalEscape

namespace D5.S3.ConceptDynamics.DefinitionEscape.ConstructiveDiagonalEscape

open Omega
open D5.S0.Diagonal.Naturality.RelativeDiagonalEscape

/-- The fixed-point-free twist of a catalog's diagonal entries is outside its range. -/
public theorem constructive_diagonal_escape {A : Type u} {Y : Type v}
    (catalog : A → A → Y) (twist : Y → Y)
    (fixedPointFree : ∀ value, Not (Eq (twist value) value)) :
    Not (Exists (fun row =>
      Eq (catalog row) (fun index => twist (catalog index index)))) :=
  relative_diagonal_escape catalog twist fixedPointFree

end D5.S3.ConceptDynamics.DefinitionEscape.ConstructiveDiagonalEscape
