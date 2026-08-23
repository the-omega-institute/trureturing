/- GID: D5/S3/ObserverMemory/InverseLimitMorphisms/IndependentDescentCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimitMorphisms/IndependentDescentCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate inverse-limit descent from its coordinate-liftable converse. -/

/- Library-search audit trail (2026-08-22):
   * Repository searches for unique compatible-family descent and surjective coordinate lifts found
     the frozen `inverse_limit_descent_and_reverse` theorem. Its first conjunct is applied directly.
   * That predecessor assumes finite naturality theorem-wide, so it cannot supply the source's
     independent converse; the converse below uses only coordinate liftability and existence of a
     coordinate-compatible map.
   * Pinned Mathlib has no declarations over the repository's canonical `InverseStageSystem` and
     `CompatibleStageFamily` types.
-/

import D5.S3.ObserverMemory.Refinement.InverseLimitDescent

namespace D5.S3.ObserverMemory.InverseLimitMorphisms.IndependentDescentCriterion

open D5.S3.ObserverMemory.InverseLimits.CompletionIsomorphismCriterion
open D5.S3.ObserverMemory.Refinement.InverseLimitDescent

/-- Finite naturality yields a unique inverse-limit descent. Independently, coordinate liftability
and the existence of a coordinate-compatible limit map recover finite naturality. -/
theorem inverse_limit_descent_and_independent_converse
    {I : Type*} [Preorder I]
    (source target : InverseStageSystem I)
    (delta : (i : I) -> source.Stage i -> target.Stage i) :
    ((forall {i j : I} (h : i <= j) (x : source.Stage j),
        target.restrict h (delta j x) = delta i (source.restrict h x)) ->
      ∃! limitMap : CompatibleStageFamily source -> CompatibleStageFamily target,
        forall family i,
          (limitMap family).stage i = delta i (family.stage i)) /\
    (((forall i, Function.Surjective
          (fun family : CompatibleStageFamily source => family.stage i)) /\
        exists limitMap : CompatibleStageFamily source -> CompatibleStageFamily target,
          forall family i,
            (limitMap family).stage i = delta i (family.stage i)) ->
      forall {i j : I} (h : i <= j) (x : source.Stage j),
        target.restrict h (delta j x) = delta i (source.restrict h x)) := by
  constructor
  · intro hdelta
    exact (inverse_limit_descent_and_reverse source target delta hdelta).1
  · rintro ⟨hlift, limitMap, hlimitMap⟩ i j h x
    rcases hlift j x with ⟨family, hfamily⟩
    calc
      target.restrict h (delta j x) =
          target.restrict h ((limitMap family).stage j) := by
        rw [hlimitMap family j, ← hfamily]
      _ = (limitMap family).stage i := (limitMap family).compatible h
      _ = delta i (family.stage i) := hlimitMap family i
      _ = delta i (source.restrict h x) := by
        calc
          delta i (family.stage i) =
              delta i (source.restrict h (family.stage j)) :=
            congrArg (delta i) (family.compatible h).symm
          _ = delta i (source.restrict h x) :=
            congrArg (delta i) (congrArg (source.restrict h) hfamily)

private def unitSystem : InverseStageSystem Nat where
  Stage := fun _ => Unit
  restrict := fun _ value => value
  restrict_refl := by intros; rfl
  restrict_trans := by intros; rfl

private def unitFamily : CompatibleStageFamily unitSystem where
  stage := fun _ => ()
  compatible := by intros; rfl

-- The unit tower supplies an inhabited model of the forward premise.
example :
    forall {i j : Nat} (h : i <= j) (x : unitSystem.Stage j),
      unitSystem.restrict h x = x := by
  intros
  rfl

-- The same tower independently supplies coordinate lifts and a compatible limit map.
example :
    (forall i, Function.Surjective
      (fun family : CompatibleStageFamily unitSystem => family.stage i)) /\
    exists limitMap : CompatibleStageFamily unitSystem -> CompatibleStageFamily unitSystem,
      forall family i, (limitMap family).stage i = family.stage i := by
  constructor
  · intro i x
    refine ⟨unitFamily, ?_⟩
    change () = x
    cases x
    rfl
  · exact ⟨id, by intros; rfl⟩

#print axioms inverse_limit_descent_and_independent_converse

end D5.S3.ObserverMemory.InverseLimitMorphisms.IndependentDescentCriterion
