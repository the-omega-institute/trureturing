/- GID: D5/S3/ConceptDynamics/DefinitionEscape/ComplementSelectorDiagonal
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pointwise avoidance supplies the twist required for diagonal escape. -/

import D5.S0.Diagonal.Lawvere.QualitativeEscape
import D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveNegation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.ComplementSelectorDiagonal

universe u v

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape
open D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveNegation

/-- An avoidance selector turns self-evaluation into a Lawvere diagonal escape. -/
theorem avoidanceSelector_diagonal_escape
    {Address : Type u} {Output : Type v}
    (selector : AvoidanceSelector Output)
    (catalog : Address → Address → Output) :
    IsEscaped selector.choose catalog :=
  escaped_of_fixedPointFree
    selector.choose selector.avoids catalog

/-- An involutive negation gives a reversible coherent instance of diagonal
escape. -/
theorem involutiveNegation_diagonal_escape
    {Address : Type u} {Output : Type v}
    (negation : InvolutiveNegation Output)
    (catalog : Address → Address → Output) :
    IsEscaped negation.neg catalog :=
  escaped_of_fixedPointFree
    negation.neg negation.fixedPointFree catalog

/-- Boolean complement is the canonical two-point diagonal escape. -/
theorem boolean_complement_diagonal_escape
    {Address : Type u}
    (catalog : Address → Address → Bool) :
    IsEscaped (fun value : Bool => !value) catalog :=
  escaped_of_fixedPointFree
    (fun value : Bool => !value) (by decide) catalog

/-- The relation-valued point complement becomes a function-valued diagonal
exactly after supplying an avoidance selector. -/
theorem avoidanceSelector_selects_diagonal_complement
    {Address : Type u} {Output : Type v}
    (selector : AvoidanceSelector Output)
    (catalog : Address → Address → Output) (address : Address) :
    selector.choose (catalog address address) ∈
      pointComplement (catalog address address) :=
  selector.avoids (catalog address address)

#print axioms avoidanceSelector_diagonal_escape
#print axioms involutiveNegation_diagonal_escape
#print axioms boolean_complement_diagonal_escape

end D5.S3.ConceptDynamics.DefinitionEscape.ComplementSelectorDiagonal
