/- GID: D5/S0/Computability/SyntaxSemanticsBoundary
   generality: G
   mirror-B: D5/B/S0/Computability/SyntaxSemanticsBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No same-level code type enumerates all predicates on itself. -/

module
prelude
public import OmegaMath.Logic.Function.Basic

universe u

namespace D5.S0.Computability.SyntaxSemanticsBoundary

open Omega

/-- A same-level syntax cannot enumerate its full predicate semantics. -/
public theorem same_layer_predicates_not_enumerable {Code : Type u}
    (semantics : Code → Code → Prop) :
    Not (∀ predicate : Code → Prop, Exists (fun code => Eq (semantics code) predicate)) :=
  Omega.Function.cantor_surjective semantics

end D5.S0.Computability.SyntaxSemanticsBoundary
