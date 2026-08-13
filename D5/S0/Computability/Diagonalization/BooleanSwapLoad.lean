/- GID: D5/S0/Computability/Diagonalization/BooleanSwapLoad
   generality: G
   mirror-B: D5/B/S0/Computability/Diagonalization/BooleanSwapLoad
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean negation is exactly the operation that carries universal self-diagonal escape. -/

import Mathlib.Data.Bool.Basic

namespace D5.S0.Computability.Diagonalization.BooleanSwapLoad

/-- On the minimal binary carrier, Boolean negation is exactly the operation that disagrees
with every value encountered on every self-application diagonal. Removing the swap means using
the identity operation, which fails the same condition on a constant diagonal. -/
theorem boolean_swap_carries_diagonal_escape (sigma : Bool -> Bool) :
    ((forall (History : Type) (V : History -> History -> Bool) (h : History),
        Ne (sigma (V h h)) (V h h)) <-> sigma = Bool.not) /\
      Not (forall (History : Type) (V : History -> History -> Bool) (h : History),
        Ne (id (V h h)) (V h h)) := by
  constructor
  · constructor
    · intro hescape
      funext b
      have hdiagonal := hescape Unit (fun _ _ => b) ()
      cases b <;> cases hsigma : sigma _ <;> simp_all
    · rintro rfl History V h
      exact Bool.not_ne_self (V h h)
  · intro hidentity
    exact hidentity Unit (fun _ _ => false) () rfl

/-- The minimal binary carrier is inhabited. -/
example : Bool := false

/-- Boolean negation supplies a concrete operation satisfying the theorem's diagonal premise. -/
example :
    forall (History : Type) (V : History -> History -> Bool) (h : History),
      Ne (Bool.not (V h h)) (V h h) := by
  intro History V h
  exact Bool.not_ne_self (V h h)

end D5.S0.Computability.Diagonalization.BooleanSwapLoad
