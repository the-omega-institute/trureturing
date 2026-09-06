/- GID: D5/S3/Entropy/Forgetting/PushforwardComposition
   generality: I
   mirror-B: D5/B/S3/Entropy/Forgetting/PushforwardComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic forgetting composes, by mathlib's fiberwise summation lemma. -/

import D5.S3.Entropy.Forgetting.CapacityMonotone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Forgetting.PushforwardComposition

open D5.S3.Entropy.Forgetting.CapacityMonotone

open scoped Classical in
/-- The indicator form of `Finset.sum_fiberwise_eq_sum_filter`: summing an
indicator-weighted family through two successive fibrations is the same as summing
it through the composite fibration.  This states mathlib's lemma in the
indicator-weighted idiom this development uses, and is proved by applying it with
`t` the fiber of `g` over `target`; the content is mathlib's, not this module's. -/
theorem sum_indicator_comp {X Y Z M : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid M] (p : X -> M) (f : X -> Y) (g : Y -> Z) (target : Z) :
    (∑ y, if g y = target then (∑ x, if f x = y then p x else 0) else 0) =
      ∑ x, if g (f x) = target then p x else 0 := by
  classical
  have h := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset X)
    (Finset.univ.filter (fun y => g y = target)) f p
  simpa [Finset.sum_filter, Finset.mem_filter] using h

open scoped Classical in
/-- Pushing a mass function forward along `f` and then along `g` is the same as
pushing it forward along `g ∘ f`.  This is the real-valued instance of
`sum_indicator_comp`, and hence of mathlib's fiberwise summation lemma. -/
theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y]
    (p : X -> Real) (f : X -> Y) (g : Y -> Z) :
    pushforward g (pushforward f p) = pushforward (g ∘ f) p := by
  classical
  funext target
  simp only [pushforward, Function.comp_apply]
  exact sum_indicator_comp p f g target

end D5.S3.Entropy.Forgetting.PushforwardComposition
