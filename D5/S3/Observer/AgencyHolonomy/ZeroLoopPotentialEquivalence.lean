/- GID: D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero path-groupoid loop sums are exactly gradients of vertex potentials. -/

import Mathlib.Algebra.Group.Basic
import Mathlib.CategoryTheory.IsConnected

/- Library-search audit trail (2026-09-01):
   * Repository searches for `potential`, `cocycle`, `coboundary`, `holonomy`,
     and closed-path variants found no equal or stronger D5 theorem. The
     existing carry-coboundary and recurrent-cocycle modules have different
     carriers and conclusions; the agency-holonomy modules only characterize
     hidden transport and policy visibility.
   * Pinned Mathlib searches found the connected-groupoid path constructor
     `CategoryTheory.nonempty_hom_of_preconnected_groupoid`, but no theorem
     packaging zero loop sums as a potential difference. Lie and group
     cohomology hits concern different cochain complexes.
   * LeanSearch requests for both graph and groupoid formulations failed at
     the endpoint. Loogle rejected the dependent morphism pattern, and the
     pinned non-Mathlib dependencies contained no relevant declaration.
   * No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.ZeroLoopPotentialEquivalence

open CategoryTheory

universe u v w

/-- An additive cost on a connected path groupoid has zero value on every
closed path exactly when it is the difference of a vertex potential. -/
theorem closed_path_zero_iff_exists_potential
    {Z : Type u} [Groupoid.{v} Z] [IsConnected Z]
    {K : Type w} [AddCommGroup K]
    (C : ∀ {x y : Z}, (x ⟶ y) → K)
    (hcomp : ∀ {x y z : Z} (f : x ⟶ y) (g : y ⟶ z),
      C (f ≫ g) = C f + C g)
    (hinv : ∀ {x y : Z} (f : x ⟶ y), C (Groupoid.inv f) = -C f) :
    (∀ (z : Z) (loop : z ⟶ z), C loop = 0) ↔
      ∃ potential : Z → K, ∀ {x y : Z} (edge : x ⟶ y),
        C edge = potential y - potential x := by
  constructor
  · intro closedPathZero
    let base : Z := Classical.choice (inferInstance : Nonempty Z)
    let path : ∀ z : Z, base ⟶ z := fun z =>
      Classical.choice (nonempty_hom_of_preconnected_groupoid base z)
    refine ⟨fun z => C (path z), ?_⟩
    intro x y edge
    have loopCost : C ((path x ≫ edge) ≫ Groupoid.inv (path y)) = 0 :=
      closedPathZero base ((path x ≫ edge) ≫ Groupoid.inv (path y))
    rw [hcomp, hcomp, hinv] at loopCost
    have pathCost : C (path x) + C edge = C (path y) := by
      apply sub_eq_zero.mp
      simpa [sub_eq_add_neg] using loopCost
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using pathCost)
  · rintro ⟨potential, hpotential⟩ z loop
    simpa using hpotential loop

#print axioms closed_path_zero_iff_exists_potential

end D5.S3.Observer.AgencyHolonomy.ZeroLoopPotentialEquivalence
