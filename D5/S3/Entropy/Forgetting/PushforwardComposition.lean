/- GID: D5/S3/Entropy/Forgetting/PushforwardComposition
   generality: I
   mirror-B: D5/B/S3/Entropy/Forgetting/PushforwardComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic forgetting composes, over any additive commutative monoid. -/

import D5.S3.Entropy.Forgetting.CapacityMonotone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Forgetting.PushforwardComposition

open D5.S3.Entropy.Forgetting.CapacityMonotone

open scoped Classical in
/-- Summing an indicator-weighted family through two successive fibrations is the
same as summing it through the composite fibration.  The values live in an
arbitrary additive commutative monoid: no order, no subtraction, and no real
structure is used. -/
theorem sum_indicator_comp {X Y Z M : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid M] (p : X -> M) (f : X -> Y) (g : Y -> Z) (target : Z) :
    (∑ y, if g y = target then (∑ x, if f x = y then p x else 0) else 0) =
      ∑ x, if g (f x) = target then p x else 0 := by
  classical
  calc
    (∑ y, if g y = target then (∑ x, if f x = y then p x else 0) else 0) =
        ∑ y, ∑ x, if f x = y /\ g y = target then p x else 0 := by
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : g y = target
      · simp [hy]
      · simp [hy]
    _ = ∑ x, ∑ y, if f x = y /\ g y = target then p x else 0 := Finset.sum_comm
    _ = ∑ x, if g (f x) = target then p x else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro y _ hy
        simp [Ne.symm hy]
      · simp

/-- Deterministic forgetting composes: pushing a mass function through `f` and
then through `g` is pushing it through `g ∘ f`.  Nothing is assumed of the mass
function beyond its type, and `Z` need not be finite. -/
theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y]
    (p : X -> Real) (f : X -> Y) (g : Y -> Z) :
    pushforward g (pushforward f p) = pushforward (g ∘ f) p := by
  classical
  funext target
  simp only [pushforward, Function.comp_apply]
  exact sum_indicator_comp p f g target

end D5.S3.Entropy.Forgetting.PushforwardComposition
