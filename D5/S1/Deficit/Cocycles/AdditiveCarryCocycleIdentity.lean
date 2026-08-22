/- GID: D5/S1/Deficit/Cocycles/AdditiveCarryCocycleIdentity
   generality: G
   mirror-B: D5/B/S1/Deficit/Cocycles/AdditiveCarryCocycleIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The kernel-valued carry of an additive section satisfies the cocycle identity. -/

import D5.S1.Deficit.Cocycles.AdditiveCarryCocycle

/- Library-search audit trail (2026-08-22):
   * Repository searches for the carry formula and cocycle equality found the frozen
     `AdditiveCarryCocycle` family module. Its `sectionCarry`, `kernelCarry`, and
     `section_carry_cocycle` declarations exactly construct and prove the source object.
   * Pinned Mathlib searches for a quotient-section carry theorem found unrelated Lie and
     homological cocycles, but no exact additive-section carry declaration.
   * The theorem below therefore imports and directly applies the existing family theorem;
     it does not redeclare the carry primitive or reprove the identity. -/

namespace D5.S1.Deficit.Cocycles.AdditiveCarryCocycleIdentity

/-- The carry constructed from a right-inverse section of an additive quotient obeys the
associative cocycle identity. -/
theorem additive_section_carry_cocycle_identity
    {X B : Type*} [AddCommGroup X] [AddCommGroup B]
    (quotient : AddMonoidHom X B) (representative : B -> X)
    (hsection : Function.RightInverse representative quotient) (a b c : B) :
    AdditiveCarryCocycle.kernelCarry quotient representative hsection a b +
        AdditiveCarryCocycle.kernelCarry quotient representative hsection (a + b) c =
      AdditiveCarryCocycle.kernelCarry quotient representative hsection b c +
        AdditiveCarryCocycle.kernelCarry quotient representative hsection a (b + c) :=
  AdditiveCarryCocycle.section_carry_cocycle
    quotient representative hsection a b c

/- The identity quotient of the integers and its identity section witness that the public
carrier and section hypotheses are jointly inhabited. -/
example :
    Function.RightInverse (fun z : Int => z) (AddMonoidHom.id Int) := by
  intro z
  rfl

#print axioms additive_section_carry_cocycle_identity

end D5.S1.Deficit.Cocycles.AdditiveCarryCocycleIdentity
