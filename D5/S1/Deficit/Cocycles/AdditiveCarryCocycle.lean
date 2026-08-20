/- GID: D5/S1/Deficit/Cocycles/AdditiveCarryCocycle
   generality: G
   mirror-B: D5/B/S1/Deficit/Cocycles/AdditiveCarryCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A set-theoretic section of an additive quotient has an associative carry defect. -/

import Mathlib

namespace D5.S1.Deficit.Cocycles.AdditiveCarryCocycle

/-- The additive carry constructed from a chosen section of a quotient map. -/
def sectionCarry {X B : Type*} [AddCommGroup X] [AddCommGroup B]
    (representative : B -> X) (a b : B) : X :=
  representative a + representative b - representative (a + b)

/-- A carry formed from a right-inverse section lies in the kernel of the quotient map. -/
theorem section_carry_mem_ker {X B : Type*} [AddCommGroup X] [AddCommGroup B]
    (quotient : AddMonoidHom X B) (representative : B -> X)
    (hsection : Function.RightInverse representative quotient) (a b : B) :
    sectionCarry representative a b ∈ quotient.ker := by
  change quotient (representative a + representative b - representative (a + b)) = 0
  rw [map_sub, map_add, hsection a, hsection b, hsection (a + b)]
  abel

/-- The carry as a residual-kernel element of the additive quotient. -/
def kernelCarry {X B : Type*} [AddCommGroup X] [AddCommGroup B]
    (quotient : AddMonoidHom X B) (representative : B -> X)
    (hsection : Function.RightInverse representative quotient) (a b : B) : quotient.ker :=
  ⟨sectionCarry representative a b,
    section_carry_mem_ker quotient representative hsection a b⟩

/-- Additive associativity makes the carry of any quotient section satisfy the
    two-cocycle identity. -/
theorem section_carry_cocycle {X B : Type*} [AddCommGroup X] [AddCommGroup B]
    (quotient : AddMonoidHom X B) (representative : B -> X)
    (hsection : Function.RightInverse representative quotient) (a b c : B) :
    kernelCarry quotient representative hsection a b +
        kernelCarry quotient representative hsection (a + b) c =
      kernelCarry quotient representative hsection b c +
        kernelCarry quotient representative hsection a (b + c) := by
  apply Subtype.ext
  simp only [kernelCarry, sectionCarry, AddSubgroup.coe_add]
  rw [add_assoc a b c]
  abel

#print axioms section_carry_cocycle

end D5.S1.Deficit.Cocycles.AdditiveCarryCocycle
