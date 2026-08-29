/- GID: D5/S3/Observer/Budget/ProjectiveStrongDuality
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ProjectiveStrongDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite attained dual minima converge exactly to the full primal value. -/

import Mathlib.Topology.Instances.Real.Lemmas

/- Library-search audit trail (2026-08-29):
   * Exact D5 searches for projective strong duality, finite dual towers,
     and the two circle feasibility inequalities found no existing owner.
   * Body-shape searches for an `IsLeast` dual-value set and for an infimum
     of finite dual minima found no canonical D5 primitive to reuse.
   * Pinned Mathlib's `tendsto_atTop_ciInf` is the exact monotone-convergence
     bridge used below. `IsLeast.csInf_eq` identifies every attained finite
     minimum with the infimum of its explicitly constructed feasible values. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace D5.S3.Observer.Budget.ProjectiveStrongDuality

universe u v

/-- A nonnegative decreasing tower of finite primal values converging to the
full value has no projective duality gap when every finite stage has an
attained strong dual. The finite dual sets are constructed directly from the
circle slack inequality, the Haar-floor inequality, and the affine objective.
The second public clause exposes an optimizer satisfying both inequalities at
every stage; no optimizer for the full infinite-dimensional dual is assumed. -/
theorem projective_strong_duality
    {Point : Type u}
    (Test : Nat -> Type v)
    (circleSlack : forall N, Test N -> Point -> ℝ)
    (atZero : forall N, Test N -> ℝ)
    (weilPairing : forall N, Test N -> ℝ)
    (a C : ℝ)
    (primalValue : Nat -> ℝ)
    (fullValue : ℝ)
    (primalNonnegative : forall N, 0 <= primalValue N)
    (projectiveAntitone : Antitone primalValue)
    (projectiveConverges : Tendsto primalValue atTop (nhds fullValue))
    (finiteStrongDuality : forall N,
      IsLeast
        {value : ℝ | exists phi : Test N, exists theta : ℝ,
          0 <= theta /\
          (forall z, 0 <= circleSlack N phi z + theta) /\
          2 * a <= 2 * a * atZero N phi + theta /\
          value = weilPairing N phi + theta * C}
        (primalValue N)) :
    fullValue =
        ⨅ N, sInf
          {value : ℝ | exists phi : Test N, exists theta : ℝ,
            0 <= theta /\
            (forall z, 0 <= circleSlack N phi z + theta) /\
            2 * a <= 2 * a * atZero N phi + theta /\
            value = weilPairing N phi + theta * C} /\
      forall N, exists phi : Test N, exists theta : ℝ,
        0 <= theta /\
        (forall z, 0 <= circleSlack N phi z + theta) /\
        2 * a <= 2 * a * atZero N phi + theta /\
        sInf
            {value : ℝ | exists psi : Test N, exists eta : ℝ,
              0 <= eta /\
              (forall z, 0 <= circleSlack N psi z + eta) /\
              2 * a <= 2 * a * atZero N psi + eta /\
              value = weilPairing N psi + eta * C} =
          weilPairing N phi + theta * C := by
  have primalBoundedBelow : BddBelow (Set.range primalValue) := by
    refine ⟨0, ?_⟩
    rintro value ⟨N, rfl⟩
    exact primalNonnegative N
  have projectiveTendsToInfimum :
      Tendsto primalValue atTop (nhds (⨅ N, primalValue N)) :=
    tendsto_atTop_ciInf projectiveAntitone primalBoundedBelow
  have fullValueEqInfimum : fullValue = ⨅ N, primalValue N :=
    tendsto_nhds_unique projectiveConverges projectiveTendsToInfimum
  constructor
  · calc
      fullValue = ⨅ N, primalValue N := fullValueEqInfimum
      _ = ⨅ N, sInf
          {value : ℝ | exists phi : Test N, exists theta : ℝ,
            0 <= theta /\
            (forall z, 0 <= circleSlack N phi z + theta) /\
            2 * a <= 2 * a * atZero N phi + theta /\
            value = weilPairing N phi + theta * C} := by
        apply congrArg (fun values : Nat -> ℝ => ⨅ N, values N)
        funext N
        exact (finiteStrongDuality N).csInf_eq.symm
  · intro N
    rcases (finiteStrongDuality N).1 with
      ⟨phi, theta, thetaNonnegative, circleFeasible, floorFeasible, valueEq⟩
    refine ⟨phi, theta, thetaNonnegative, circleFeasible, floorFeasible, ?_⟩
    calc
      sInf
          {value : ℝ | exists psi : Test N, exists eta : ℝ,
            0 <= eta /\
            (forall z, 0 <= circleSlack N psi z + eta) /\
            2 * a <= 2 * a * atZero N psi + eta /\
            value = weilPairing N psi + eta * C} =
          primalValue N := (finiteStrongDuality N).csInf_eq
      _ = weilPairing N phi + theta * C := valueEq

#print axioms projective_strong_duality

end D5.S3.Observer.Budget.ProjectiveStrongDuality
