/- GID: D5/S0/Rewriting/Quotients/SplitSurjectionFactorization
   generality: G
   mirror-B: D5/B/S0/Rewriting/Quotients/SplitSurjectionFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fiber-constant map factors uniquely through a split surjection. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-23):
   * Repository search found `DynamicsDescent.dynamics_descends_iff`, which is
     restricted to a self-map with the quotient as both source and target
     codomain, and `ContinuousDescent.continuous_descent`, which adds topology.
     Neither is the arbitrary-target factorization proved here.
   * Pinned Mathlib has no exact existence-and-uniqueness theorem of this shape.
     The exact supporting hits `Function.RightInverse.surjective` and
     `Function.Surjective.injective_comp_right` are applied below. -/

namespace D5.S0.Rewriting.Quotients.SplitSurjectionFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A map constant on the fibers of a split surjection factors uniquely through it. -/
theorem split_surjection_factorization
    {X B' B : Type*} (qPrime : X -> B') (q : X -> B) (s : B' -> X)
    (hFiber : Function.FactorsThrough q qPrime)
    (hSection : Function.RightInverse s qPrime) :
    ExistsUnique fun p : B' -> B => q = Function.comp p qPrime := by
  let p : B' -> B := Function.comp q s
  have hFactor : q = Function.comp p qPrime := by
    funext x
    change q x = q (s (qPrime x))
    exact (hFiber (hSection (qPrime x))).symm
  refine ExistsUnique.intro p hFactor ?_
  intro candidate hCandidate
  apply hSection.surjective.injective_comp_right
  exact hCandidate.symm.trans hFactor

example : Bool := false

example :
    And (Function.FactorsThrough Bool.not (id : Bool -> Bool))
      (Function.RightInverse (id : Bool -> Bool) (id : Bool -> Bool)) := by
  constructor
  case left =>
    intro x y hxy
    exact congrArg Bool.not hxy
  case right =>
    intro x
    rfl

example :
    ExistsUnique fun p : Bool -> Bool => Bool.not = Function.comp p id := by
  apply split_surjection_factorization id Bool.not id
  case hFiber =>
    intro x y hxy
    exact congrArg Bool.not hxy
  case hSection =>
    intro x
    rfl

#print axioms split_surjection_factorization

end D5.S0.Rewriting.Quotients.SplitSurjectionFactorization
