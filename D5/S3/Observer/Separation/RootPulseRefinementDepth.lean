/- GID: D5/S3/Observer/Separation/RootPulseRefinementDepth
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/RootPulseRefinementDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Root-pulse refinement raises then lowers completion depth and saturates the bound. -/

import D5.S3.Observer.Separation.RootPulseSharpness
import Mathlib.Order.Lattice.Nat

/- Library-search audit trail (2026-08-20):
   * Repository search found the exact root-pulse depth and bound theorem
     `root_pulse_sharpness`; it is imported and applied below.
   * Pinned Mathlib searches found exact hits `Nat.sInf_eq_zero`,
     `Fintype.card_congr`, `Fintype.card_fin`, `Fintype.card_bool`, and
     `Fintype.card_punit`; they are applied below.
   * Repository and pinned-Mathlib searches found no theorem packaging all
     constant/root/identity depths, quotient cardinalities, refinement maps,
     and image-cardinality sharpness clauses. -/

noncomputable section

namespace D5.S3.Observer.Separation.RootPulseRefinementDepth

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.Observer.Separation.RootPulseSharpness
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/-- The source's coarse readout is constant on the state chain. -/
def constantReadout {n : Nat} (_ : Fin n) : PUnit.{1} :=
  PUnit.unit

/-- The source's finest readout exposes the state itself. -/
def identityReadout {n : Nat} (i : Fin n) : Fin n :=
  i

/-- Equality of every future readout, constructed from the repository's
infinite future relation. -/
def completedObservationSetoid {Y O : Type*} (update : Y -> Y)
    (readout : Y -> O) : Setoid Y where
  r y y' := (y, y') ∈ infiniteFutureRelation update readout
  iseqv := infinite_relation_equivalence update readout

/-- The source completion state is the quotient by equality of all future
readout coordinates. -/
abbrev CompletionState {Y O : Type*} (update : Y -> Y)
    (readout : Y -> O) :=
  Quotient (completedObservationSetoid update readout)

noncomputable instance completionStateFintype
    {Y O : Type*} [Fintype Y] (update : Y -> Y) (readout : Y -> O) :
    Fintype (CompletionState update readout) :=
  Fintype.ofFinite _

private noncomputable def completion_equiv_of_separating
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (hseparating : ∀ y y' : Y,
      (∀ k, observedAt update readout k y = observedAt update readout k y') ->
        y = y') :
    CompletionState update readout ≃ Y where
  toFun := Quotient.lift id (by
    intro y y' hfuture
    exact hseparating y y' hfuture)
  invFun := fun y => Quotient.mk (completedObservationSetoid update readout) y
  left_inv state := by
    induction state using Quotient.inductionOn with
    | _ y => rfl
  right_inv _ := rfl

private noncomputable def constant_completion_equiv (n : Nat) (hn : 0 < n) :
    CompletionState (@rootPulseUpdate n) (@constantReadout n) ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := Quotient.mk (completedObservationSetoid
    (@rootPulseUpdate n) (@constantReadout n)) (show Fin n from ⟨0, hn⟩)
  left_inv state := by
    induction state using Quotient.inductionOn with
    | _ i =>
        apply Quotient.sound
        intro k
        rfl
  right_inv value := by
    cases value
    rfl

private theorem root_profiles_separate (n : Nat) (hn : 3 ≤ n) :
    ∀ i j : Fin n,
      (∀ k, observedAt (@rootPulseUpdate n) (@rootPulseReadout n) k i =
        observedAt (@rootPulseUpdate n) (@rootPulseReadout n) k j) ->
      i = j := by
  intro i j hfuture
  by_contra hij
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have htime := (root_pulse_sharpness n (by omega)).1 i j (by simpa using hlt)
    have hnone : ¬ ∃ k,
        observedAt (@rootPulseUpdate n) (@rootPulseReadout n) k i ≠
          observedAt (@rootPulseUpdate n) (@rootPulseReadout n) k j := by
      push Not
      exact hfuture
    have hi : i.val = 0 := by
      simpa [separationTime, hnone] using htime.symm
    have hj_ne : j.val ≠ 0 := by
      omega
    have hcurrent := hfuture 0
    simp [observedAt, rootPulseReadout, hi, hj_ne] at hcurrent
  · have htime := (root_pulse_sharpness n (by omega)).1 j i (by simpa using hgt)
    have hnone : ¬ ∃ k,
        observedAt (@rootPulseUpdate n) (@rootPulseReadout n) k j ≠
          observedAt (@rootPulseUpdate n) (@rootPulseReadout n) k i := by
      push Not
      intro k
      exact (hfuture k).symm
    have hj : j.val = 0 := by
      simpa [separationTime, hnone] using htime.symm
    have hi_ne : i.val ≠ 0 := by
      omega
    have hcurrent := hfuture 0
    simp [observedAt, rootPulseReadout, hj, hi_ne] at hcurrent

private theorem identity_profiles_separate (n : Nat) :
    ∀ i j : Fin n,
      (∀ k, observedAt (@rootPulseUpdate n) (@identityReadout n) k i =
        observedAt (@rootPulseUpdate n) (@identityReadout n) k j) ->
      i = j := by
  intro i j hfuture
  simpa [observedAt, identityReadout] using hfuture 0

private theorem constant_depth_zero (n : Nat) :
    observationStabilityDepth (@rootPulseUpdate n) (@constantReadout n) = 0 := by
  rw [observationStabilityDepth, Nat.sInf_eq_zero]
  left
  apply Setoid.ext
  intro i j
  constructor <;> intro _ <;> funext k <;> rfl

private theorem identity_depth_zero (n : Nat) :
    observationStabilityDepth (@rootPulseUpdate n) (@identityReadout n) = 0 := by
  rw [observationStabilityDepth, Nat.sInf_eq_zero]
  left
  apply Setoid.ext
  intro i j
  constructor
  · intro hword
    have hcurrent := congrFun hword (0 : Fin 1)
    have hij : i = j := by
      simpa [futureReadoutWord, observedAt, identityReadout] using hcurrent
    subst j
    rfl
  · intro hword
    have hcurrent := congrFun hword (0 : Fin 2)
    have hij : i = j := by
      simpa [futureReadoutWord, observedAt, identityReadout] using hcurrent
    subst j
    rfl

private theorem root_readout_surjective (n : Nat) (hn : 3 ≤ n) :
    Function.Surjective (@rootPulseReadout n) := by
  intro value
  cases value with
  | false => exact ⟨⟨1, by omega⟩, by simp [rootPulseReadout]⟩
  | true => exact ⟨⟨0, by omega⟩, by simp [rootPulseReadout]⟩

private noncomputable def root_readout_range_equiv (n : Nat) (hn : 3 ≤ n) :
    Set.range (@rootPulseReadout n) ≃ Bool :=
  Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, by
      intro value
      obtain ⟨i, hi⟩ := root_readout_surjective n hn value
      exact ⟨⟨value, i, hi⟩, rfl⟩⟩

/-- The source chain gives both directions of depth nonmonotonicity under
observation refinement and attains the finite-state bound exactly. -/
theorem root_pulse_refinement_depth_counterexample (n : Nat) (hn : 3 ≤ n) :
    observationStabilityDepth (@rootPulseUpdate n) (@constantReadout n) = 0 ∧
    observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) = n - 2 ∧
    observationStabilityDepth (@rootPulseUpdate n) (@identityReadout n) = 0 ∧
    Fintype.card (CompletionState (@rootPulseUpdate n) (@constantReadout n)) = 1 ∧
    Fintype.card (CompletionState (@rootPulseUpdate n) (@rootPulseReadout n)) = n ∧
    Fintype.card (CompletionState (@rootPulseUpdate n) (@identityReadout n)) = n ∧
    ((∃ h : Bool -> PUnit,
        (@constantReadout n) = h ∘ (@rootPulseReadout n)) ∧
      observationStabilityDepth (@rootPulseUpdate n) (@constantReadout n) = 0 ∧
      observationStabilityDepth (@rootPulseUpdate n) (@constantReadout n) <
        observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) ∧
      observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) = n - 2) ∧
    ((∃ h : Fin n -> Bool,
        (@rootPulseReadout n) = h ∘ (@identityReadout n)) ∧
      observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) = n - 2 ∧
      observationStabilityDepth (@rootPulseUpdate n) (@identityReadout n) = 0 ∧
      observationStabilityDepth (@rootPulseUpdate n) (@identityReadout n) <
        observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n)) ∧
    (observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) = n - 2 ∧
      n - 2 = Fintype.card (Fin n) -
        Fintype.card (Set.range (@rootPulseReadout n))) := by
  rcases root_pulse_sharpness n (by omega) with
    ⟨_, _, _, hrootDepth, _, _, hboundSharp⟩
  have hconstantDepth := constant_depth_zero n
  have hidentityDepth := identity_depth_zero n
  have hconstantCard :
      Fintype.card (CompletionState (@rootPulseUpdate n) (@constantReadout n)) = 1 := by
    rw [Fintype.card_congr (constant_completion_equiv n (by omega))]
    exact Fintype.card_punit
  have hrootCard :
      Fintype.card (CompletionState (@rootPulseUpdate n) (@rootPulseReadout n)) = n := by
    rw [Fintype.card_congr
      (completion_equiv_of_separating _ _ (root_profiles_separate n hn))]
    exact Fintype.card_fin n
  have hidentityCard :
      Fintype.card (CompletionState (@rootPulseUpdate n) (@identityReadout n)) = n := by
    rw [Fintype.card_congr
      (completion_equiv_of_separating _ _ (identity_profiles_separate n))]
    exact Fintype.card_fin n
  have hrangeCard : Fintype.card (Set.range (@rootPulseReadout n)) = 2 := by
    rw [Fintype.card_congr (root_readout_range_equiv n hn)]
    exact Fintype.card_bool
  have hsharp : n - 2 = Fintype.card (Fin n) -
      Fintype.card (Set.range (@rootPulseReadout n)) := by
    rw [hrangeCard, Fintype.card_fin]
  refine ⟨hconstantDepth, hrootDepth, hidentityDepth,
    hconstantCard, hrootCard, hidentityCard, ?_, ?_, hrootDepth, hsharp⟩
  · refine ⟨⟨fun _ => PUnit.unit, ?_⟩, hconstantDepth, ?_, hrootDepth⟩
    · funext i
      rfl
    · rw [hconstantDepth, hrootDepth]
      omega
  · refine ⟨⟨@rootPulseReadout n, ?_⟩, hrootDepth, hidentityDepth, ?_⟩
    · funext i
      rfl
    · rw [hidentityDepth, hrootDepth]
      omega

/-- The source size restriction is satisfiable. -/
example : 3 ≤ 3 := by omega

/-- The source state carrier is inhabited under the size restriction. -/
example : Fin 3 := ⟨0, by omega⟩

#print axioms root_pulse_refinement_depth_counterexample

end D5.S3.Observer.Separation.RootPulseRefinementDepth
