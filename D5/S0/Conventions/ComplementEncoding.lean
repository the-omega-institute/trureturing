/- GID: D5/S0/Conventions/ComplementEncoding
   generality: G
   mirror-B: D5/B/S0/Conventions/ComplementEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Subtraction complement is involutive and determines its total. -/

import Mathlib.Algebra.Group.Basic

namespace D5.S0.Conventions.ComplementEncoding

/- The ambient element `u` is the total relative to which `e` is complemented. -/
def complement {G : Type*} [AddCommGroup G] (u e : G) : G := u - e

/- The complement operation has the endpoint, involution, and uniqueness laws. -/
theorem complement_encoding {G : Type*} [AddCommGroup G] (u e : G) :
    (fun x : G => u - x) 0 = u ∧
      (fun x : G => u - x) u = 0 ∧
        (fun x : G => u - x) ((fun x : G => u - x) e) = e ∧
          ∀ v : G, (fun x : G => v - x) = (fun x : G => u - x) → v = u := by
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  · intro v h
    simpa using congrFun h 0

#print axioms complement_encoding

end D5.S0.Conventions.ComplementEncoding
