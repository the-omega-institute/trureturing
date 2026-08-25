/- GID: D5/S1/FixedPoints/Reachability/SafetyDichotomy
   generality: G
   mirror-B: D5/B/S1/FixedPoints/Reachability/SafetyDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Least-fixed-point safety and finite bad paths form the reachability dichotomy. -/

import D5.S1.FixedPoints.RelationalReachExpansion

/- Library-search audit trail (2026-08-24):
   * Exact repository hit `finite_step_expansion` identifies the source's
     relation-generated least fixed point with its finite stages; it is
     applied below.
   * Exact pinned-Mathlib hits `SetRel.mem_image` and the constructors of
     `Relation.ReflTransGen` supply the one-step and finite-path bridges and
     are applied below.
   * Repository and pinned-Mathlib searches found no exact theorem combining
     least-fixed-point safety with extraction of a finite bad path.
   * `loogle` and `leansearch` executables were absent from PATH. -/

namespace D5.S1.FixedPoints.Reachability.SafetyDichotomy

open D5.S1.FixedPoints.RelationalReachExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem stage_member_has_finite_path
    {X : Type*} (relation : SetRel X X) (initial : Set X) :
    ∀ (n : Nat) {target : X},
      target ∈ (reachStep relation initial)^[n] ∅ →
        ∃ start ∈ initial,
          Relation.ReflTransGen
            (fun prior next => (prior, next) ∈ relation) start target := by
  intro n
  induction n with
  | zero =>
      intro target htarget
      have : False := by simpa using htarget
      exact this.elim
  | succ n ih =>
      intro target htarget
      rw [Function.iterate_succ_apply'] at htarget
      change target ∈ initial ∪
        relation.image ((reachStep relation initial)^[n] ∅) at htarget
      rcases htarget with hinitial | ⟨prior, hprior, hrelation⟩
      · exact ⟨target, hinitial, Relation.ReflTransGen.refl⟩
      · rcases ih hprior with ⟨start, hstart, hpath⟩
        exact ⟨start, hstart, hpath.tail hrelation⟩

private theorem finite_path_has_stage
    {X : Type*} (relation : SetRel X X) (initial : Set X)
    {start target : X} (hstart : start ∈ initial)
    (path : Relation.ReflTransGen
      (fun prior next => (prior, next) ∈ relation) start target) :
    ∃ n : Nat, target ∈ (reachStep relation initial)^[n] ∅ := by
  induction path with
  | refl =>
      refine ⟨1, ?_⟩
      rw [Function.iterate_succ_apply']
      change start ∈ initial ∪ relation.image ((reachStep relation initial)^[0] ∅)
      exact Or.inl hstart
  | tail path hrelation ih =>
      rcases ih with ⟨n, hprior⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      change _ ∈ initial ∪ relation.image ((reachStep relation initial)^[n] ∅)
      exact Or.inr ⟨_, hprior, hrelation⟩

private theorem finite_path_mem_lfp
    {X : Type*} (relation : SetRel X X) (initial : Set X)
    {start target : X} (hstart : start ∈ initial)
    (path : Relation.ReflTransGen
      (fun prior next => (prior, next) ∈ relation) start target) :
    target ∈ (reachStep relation initial).lfp := by
  rw [(finite_step_expansion relation initial (fun _ : Unit => ∅)).2]
  rcases finite_path_has_stage relation initial hstart path with ⟨n, htarget⟩
  exact Set.mem_iUnion.2 ⟨n, htarget⟩

/-- If the relation-generated least fixed point stays inside the safe set,
every finite path from an initial state is safe. If that fixed point contains
a bad state, one of its finite stages constructs a finite path to such a
state. -/
theorem reachability_safety_and_bad_path
    {X : Type*} (relation : SetRel X X) (initial safe : Set X) :
    ((reachStep relation initial).lfp ⊆ safe →
      ∀ {start target}, start ∈ initial →
        Relation.ReflTransGen
          (fun prior next => (prior, next) ∈ relation) start target →
        target ∈ safe) ∧
      (((reachStep relation initial).lfp ∩ safeᶜ).Nonempty →
        ∃ start ∈ initial, ∃ target,
          Relation.ReflTransGen
              (fun prior next => (prior, next) ∈ relation) start target ∧
            target ∉ safe) := by
  constructor
  · intro hsafe start target hstart path
    exact hsafe (finite_path_mem_lfp relation initial hstart path)
  · intro hbad
    rcases hbad with ⟨target, hreach, htarget⟩
    rw [(finite_step_expansion relation initial (fun _ : Unit => ∅)).2] at hreach
    rcases Set.mem_iUnion.1 hreach with ⟨n, hstage⟩
    rcases stage_member_has_finite_path relation initial n hstage with
      ⟨start, hstart, path⟩
    exact ⟨start, hstart, target, path, htarget⟩

/-- The source primitives admit a concrete one-edge transition system. -/
example : SetRel Bool Bool × Set Bool × Set Bool :=
  ({(false, true)}, {false}, {false, true})

#print axioms reachability_safety_and_bad_path

end D5.S1.FixedPoints.Reachability.SafetyDichotomy
