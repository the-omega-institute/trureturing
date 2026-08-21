/- GID: D5/S3/ObserverMemory/Refinement/InverseLimitDescent
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/InverseLimitDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the unique map between compatible inverse-limit families and recover finite naturality from surjective coordinates. -/

import D5.S3.ObserverMemory.InverseLimits.CompletionIsomorphismCriterion

namespace D5.S3.ObserverMemory.Refinement.InverseLimitDescent

open D5.S3.ObserverMemory.InverseLimits.CompletionIsomorphismCriterion

def inducedMap {I : Type*} [Preorder I]
    (source target : InverseStageSystem I)
    (delta : (i : I) -> source.Stage i -> target.Stage i)
    (hdelta : forall {i j : I} (h : i <= j) (x : source.Stage j),
      target.restrict h (delta j x) = delta i (source.restrict h x)) :
    CompatibleStageFamily source -> CompatibleStageFamily target :=
  fun family =>
    { stage := fun i => delta i (family.stage i)
      compatible := by
        intro i j h
        rw [hdelta h]
        exact congrArg (delta i) (family.compatible h) }

theorem inverse_limit_descent_and_reverse {I : Type*} [Preorder I]
    (source target : InverseStageSystem I)
    (delta : (i : I) -> source.Stage i -> target.Stage i)
    (hdelta : forall {i j : I} (h : i <= j) (x : source.Stage j),
      target.restrict h (delta j x) = delta i (source.restrict h x)) :
    (∃! Delta : CompatibleStageFamily source -> CompatibleStageFamily target,
      forall family i, (Delta family).stage i = delta i (family.stage i)) /\
    (forall Delta : CompatibleStageFamily source -> CompatibleStageFamily target,
      (forall family i, (Delta family).stage i = delta i (family.stage i)) ->
      (forall i, Function.Surjective (fun family : CompatibleStageFamily source =>
        family.stage i)) ->
      forall {i j : I} (h : i <= j) (x : source.Stage j),
        target.restrict h (delta j x) = delta i (source.restrict h x)) := by
  constructor
  · refine ⟨inducedMap source target delta hdelta, ?_, ?_⟩
    · intro family i
      rfl
    · intro Delta hDelta
      funext family
      apply CompatibleStageFamily.ext
      funext i
      exact hDelta family i
  · intro Delta hDelta hsurj i j h x
    rcases hsurj j x with ⟨family, hfamily⟩
    calc
      target.restrict h (delta j x) = target.restrict h ((Delta family).stage j) := by
        rw [hDelta family j, ← hfamily]
      _ = (Delta family).stage i := (Delta family).compatible h
      _ = delta i (family.stage i) := hDelta family i
      _ = delta i (source.restrict h x) := by
        calc
          delta i (family.stage i) = delta i (source.restrict h (family.stage j)) :=
            congrArg (delta i) (family.compatible h).symm
          _ = delta i (source.restrict h x) :=
            congrArg (delta i) (congrArg (source.restrict h) hfamily)

end D5.S3.ObserverMemory.Refinement.InverseLimitDescent
