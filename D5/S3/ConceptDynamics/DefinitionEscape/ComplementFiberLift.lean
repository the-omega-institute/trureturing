/- GID: D5/S3/ConceptDynamics/DefinitionEscape/ComplementFiberLift
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A section lifts base complement, and the lift square is its fiber retraction. -/

import D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveNegation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.ComplementFiberLift

universe u v

/-- The total-space fiber over the complemented value of `q x`. -/
def complementFiber
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (x : X) : Set X :=
  {y | q y = baseNegation (q x)}

/-- A point-valued lift selects one point in every complement fiber. -/
def IsComplementLift
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (lift : X → X) : Prop :=
  ∀ x, q (lift x) = baseNegation (q x)

/-- The lift condition is exactly pointwise membership in complement fibers. -/
theorem isComplementLift_iff_mem_fiber
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (lift : X → X) :
    IsComplementLift q baseNegation lift ↔
      ∀ x, lift x ∈ complementFiber q baseNegation x := by
  rfl

/-- A section chooses a canonical representative in each base fiber and hence
constructs a canonical point-valued complement lift. -/
def sectionLift
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (section : Q → X) :
    X → X :=
  fun x => section (baseNegation (q x))

/-- A right-inverse section makes the section lift project to base
complementation. -/
theorem sectionLift_isComplementLift
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (section : Q → X)
    (sectionRightInverse : Function.RightInverse section q) :
    IsComplementLift q baseNegation
      (sectionLift q baseNegation section) := by
  intro x
  exact sectionRightInverse (baseNegation (q x))

/-- When the base negation is involutive, applying the section lift twice is
the retraction onto the chosen section image. -/
theorem sectionLift_square
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (section : Q → X)
    (sectionRightInverse : Function.RightInverse section q)
    (baseInvolutive : Function.Involutive baseNegation) :
    sectionLift q baseNegation section ∘
        sectionLift q baseNegation section =
      section ∘ q := by
  funext x
  change
    section
        (baseNegation
          (q (section (baseNegation (q x))))) =
      section (q x)
  rw [sectionRightInverse (baseNegation (q x)),
    baseInvolutive (q x)]

/-- The section lift is genuinely involutive on the chosen section image. -/
theorem sectionLift_involutive_on_section
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (section : Q → X)
    (sectionRightInverse : Function.RightInverse section q)
    (baseInvolutive : Function.Involutive baseNegation)
    (value : Q) :
    sectionLift q baseNegation section
        (sectionLift q baseNegation section (section value)) =
      section value := by
  have squareAtSection :=
    congrFun
      (sectionLift_square q baseNegation section
        sectionRightInverse baseInvolutive)
      (section value)
  simpa [Function.comp_apply, sectionRightInverse value] using squareAtSection

/-- If the section is also a left inverse, no hidden fiber freedom remains and
the lifted complement is a total-space involution. -/
theorem sectionLift_involutive_of_leftInverse
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (section : Q → X)
    (sectionRightInverse : Function.RightInverse section q)
    (sectionLeftInverse : Function.LeftInverse section q)
    (baseInvolutive : Function.Involutive baseNegation) :
    Function.Involutive (sectionLift q baseNegation section) := by
  intro x
  have squareAtX :=
    congrFun
      (sectionLift_square q baseNegation section
        sectionRightInverse baseInvolutive)
      x
  simpa [Function.comp_apply, sectionLeftInverse x] using squareAtX

/-- Under a right-inverse section and involutive base negation, the section
lift is a total-space involution exactly when the section is also a left
inverse. -/
theorem sectionLift_involutive_iff_leftInverse
    {X : Type u} {Q : Type v}
    (q : X → Q) (baseNegation : Q → Q) (section : Q → X)
    (sectionRightInverse : Function.RightInverse section q)
    (baseInvolutive : Function.Involutive baseNegation) :
    Function.Involutive (sectionLift q baseNegation section) ↔
      Function.LeftInverse section q := by
  constructor
  · intro liftInvolutive x
    have squareAtX :=
      congrFun
        (sectionLift_square q baseNegation section
          sectionRightInverse baseInvolutive)
        x
    exact squareAtX.symm.trans (liftInvolutive x)
  · intro sectionLeftInverse
    exact sectionLift_involutive_of_leftInverse
      q baseNegation section sectionRightInverse sectionLeftInverse
        baseInvolutive

#print axioms sectionLift_isComplementLift
#print axioms sectionLift_square
#print axioms sectionLift_involutive_of_leftInverse
#print axioms sectionLift_involutive_iff_leftInverse

end D5.S3.ConceptDynamics.DefinitionEscape.ComplementFiberLift
