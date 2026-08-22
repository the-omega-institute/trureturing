/- GID: D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A zero-error answer is covered by the canonical safe answer on inhabited fibers. -/

import Mathlib.Data.Set.Subsingleton

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'safe_answer_coverage_maximality' D5 Golden/Frozen/accepted` and the
     required `safe_answer|answerable|zero_error|abstain` searches found no duplicate;
     the only latter hit was an unrelated `abstainFailure` in a public-good example.
   * `rg -l 'Answering|SafeAnswer' D5/` returned no files, confirming that this is the
     first repository module for the safe-answer construction.
   * Pinned Mathlib provides `Set.Subsingleton.eq_singleton_of_mem` in
     `Mathlib.Data.Set.Subsingleton`; the maximality proof reuses it to turn the
     constructed nonempty, at-most-one target fiber into the required singleton.
   * No upstream declaration packages the domain-specific Option-valued answerer;
     the remaining proof uses equality, existential elimination, and classical choice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.SafeAnswerCoverageMaximality

/-- Target values attained by admitted inputs in the concept fiber over `b`. -/
def fiberTargets {X B Y : Type*} (A : X -> Prop) (C : X -> B) (T : X -> Y)
    (b : B) : Set Y :=
  {y | exists x, A x ∧ C x = b ∧ T x = y}

/-- An answerer has zero error when every answer on an admitted input is its target. -/
def ZeroError {X B Y : Type*} (A : X -> Prop) (C : X -> B) (T : X -> Y)
    (g : B -> Option Y) : Prop :=
  forall x, A x -> forall y, g (C x) = some y -> T x = y

/-- The canonical safe answer is the unique attained target on a singleton fiber and
abstains both on empty fibers and on fibers with conflicting target values. -/
noncomputable def canonicalSafeAnswer {X B Y : Type*} (A : X -> Prop)
    (C : X -> B) (T : X -> Y) (b : B) : Option Y := by
  classical
  exact if h : ∃! y, y ∈ fiberTargets A C T b then some h.choose else none

/-- The canonical safe answer itself has zero error on every admitted input. -/
theorem canonical_safe_answer_zero_error {X B Y : Type*} (A : X -> Prop)
    (C : X -> B) (T : X -> Y) :
    ZeroError A C T (canonicalSafeAnswer A C T) := by
  intro x hx y hAnswer
  unfold canonicalSafeAnswer at hAnswer
  split at hAnswer
  · rename_i hUnique
    have hTarget : T x ∈ fiberTargets A C T (C x) :=
      ⟨x, hx, rfl, rfl⟩
    have hChosen : hUnique.choose = y := Option.some.inj hAnswer
    exact (hUnique.unique hTarget hUnique.choose_spec.left).trans hChosen
  · contradiction

/-- On an inhabited fiber, every answer made by a zero-error answerer is made with the
same value by the canonical answerer. Fiber inhabitation is necessary because zero
error constrains an answerer only at readouts of admitted inputs. -/
theorem safe_answer_coverage_maximality {X B Y : Type*} (A : X -> Prop)
    (C : X -> B) (T : X -> Y) (g : B -> Option Y) (b : B) (y : Y)
    (hzero : ZeroError A C T g) (hFiber : exists x, A x ∧ C x = b)
    (hAnswer : g b = some y) :
    canonicalSafeAnswer A C T b = some y := by
  rcases hFiber with ⟨x, hx, hCx⟩
  have hAtX : g (C x) = some y := by
    rw [hCx]
    exact hAnswer
  have hTx : T x = y := hzero x hx y hAtX
  have hy : y ∈ fiberTargets A C T b := ⟨x, hx, hCx, hTx⟩
  have hSubsingleton : (fiberTargets A C T b).Subsingleton := by
    intro y₁ hy₁ y₂ hy₂
    rcases hy₁ with ⟨x₁, hx₁, hCx₁, hTx₁⟩
    rcases hy₂ with ⟨x₂, hx₂, hCx₂, hTx₂⟩
    have hAnswer₁ : g (C x₁) = some y := by
      rw [hCx₁]
      exact hAnswer
    have hAnswer₂ : g (C x₂) = some y := by
      rw [hCx₂]
      exact hAnswer
    calc
      y₁ = T x₁ := hTx₁.symm
      _ = y := hzero x₁ hx₁ y hAnswer₁
      _ = T x₂ := (hzero x₂ hx₂ y hAnswer₂).symm
      _ = y₂ := hTx₂
  have hSingleton : fiberTargets A C T b = {y} :=
    hSubsingleton.eq_singleton_of_mem hy
  have hUnique : ∃! z, z ∈ fiberTargets A C T b := by
    refine ⟨y, hy, ?_⟩
    intro z hz
    rw [hSingleton] at hz
    simpa using hz
  unfold canonicalSafeAnswer
  split
  · rename_i hCanonicalUnique
    exact congrArg some (hCanonicalUnique.unique hCanonicalUnique.choose_spec.left hy)
  · rename_i hNotUnique
    exact (hNotUnique hUnique).elim

/-- A concrete inhabited fiber has its sole target answered canonically. -/
example :
    canonicalSafeAnswer (fun _ : Fin 1 => True) (fun _ => false)
      (fun _ => false) false = some false := by
  apply safe_answer_coverage_maximality (g := fun _ : Bool => some false)
  · intro _ _ y hAnswer
    exact Option.some.inj hAnswer
  · exact ⟨0, trivial, rfl⟩
  · rfl

/-- The inhabitation premise cannot be dropped: a zero-error answerer may answer on an
empty fiber while the canonical answerer, by definition, abstains there. -/
theorem empty_fiber_counterexample :
    exists (A : Fin 1 -> Prop) (C : Fin 1 -> Bool) (T : Fin 1 -> Bool)
      (g : Bool -> Option Bool) (b y : Bool),
      ZeroError A C T g ∧
        (¬ exists x, A x ∧ C x = b) ∧
        g b = some y ∧ canonicalSafeAnswer A C T b = none := by
  refine ⟨(fun _ => True), (fun _ => false), (fun _ => false),
    (fun observed => some observed), true, true, ?_⟩
  constructor
  · intro _ _ y hAnswer
    exact Option.some.inj hAnswer
  constructor
  · rintro ⟨_, _, hReadout⟩
    exact Bool.false_ne_true hReadout
  constructor
  · rfl
  · simp [canonicalSafeAnswer, fiberTargets]

#print axioms safe_answer_coverage_maximality

end D5.S3.ConceptDynamics.Answering.SafeAnswerCoverageMaximality
