/- GID: D5/S0/Computability/SyntaxSemanticsBoundary
   generality: G
   mirror-B: D5/B/S0/Computability/SyntaxSemanticsBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No same-level code type enumerates all predicates on itself. -/

import Mathlib.Logic.Function.Basic

universe u

namespace D5.S0.Computability.SyntaxSemanticsBoundary

/-- A same-level syntax cannot enumerate its full predicate semantics. For
any proposed interpretation from codes to predicates on codes, some predicate
is absent from its range. This is a thin honest wrapper around Mathlib's
`Function.cantor_surjective`. -/
theorem same_layer_predicates_not_enumerable {Code : Type u}
    (semantics : Code -> Set Code) :
    Function.Surjective semantics -> False :=
  Function.cantor_surjective semantics

end D5.S0.Computability.SyntaxSemanticsBoundary
