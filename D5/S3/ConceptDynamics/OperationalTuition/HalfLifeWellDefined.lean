/- GID: D5/S3/ConceptDynamics/OperationalTuition/HalfLifeWellDefined
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalTuition/HalfLifeWellDefined
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite capture histories have a computable half-life and admit an unconverged witness. -/

import D5.S3.ConceptDynamics.OperationalTuition.InstitutionalMappingAndCaptureFiltration
import Mathlib.Data.List.Infix

/- Library-search audit trail (2026-08-31):
   * Exact repository and pinned-Mathlib searches for `halfLife`,
     `half_life`, stable gate capture, and the ink-not-dry witness found no
     covering declaration.
   * The frozen OTT carrier supplies `OperationalTrajectory`, `classMaturity`,
     `CaptureLevel`, and the `wall < gate < author` order; they are imported
     rather than redeclared.
   * Pinned Lean/Mathlib supplies `List.tails`, `List.getElem_tails`, and
     `List.findIdx?_eq_some_iff_getElem`.  The theorem below applies those
     executable finite-list results to the independently stated stability
     predicate.

   Clause echo:
   * Definition 3.2's `h(c)` is `gateHalfLife trajectory errorClass`, measured
     by event count as explicitly permitted by the source.  `some n` means the
     nonempty same-class suffix at index `n` is wholly gate-or-higher and every
     earlier suffix fails that condition; `none` means no such suffix exists.
   * T-C's finite trajectory is the frozen carrier's `events : List _`; the
     computation is `List.tails.findIdx?`, so no unbounded choice is involved.
   * `inkNotDryTrajectory` contains the attested three same-class wall captures.
     Its maturity list and `none` half-life are theorem conjuncts, witnessing
     that the executable definition does not report convergence vacuously. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalTuition.HalfLifeWellDefined

open D5.S3.ConceptDynamics.OperationalTuition.InstitutionalMappingAndCaptureFiltration

/-- Whether a nonempty capture suffix is entirely at gate level or above. -/
def stableGateSuffix (levels : List CaptureLevel) : Bool :=
  match levels with
  | [] => false
  | _ :: _ => levels.all fun level => decide (gate <= level)

/-- The source-semantic statement that stability begins at a given event index. -/
def StableAtGate (levels : List CaptureLevel) (index : Nat) : Prop :=
  index < levels.length /\
    forall level, level ∈ levels.drop index -> gate <= level

/-- Executable half-life on a finite capture history.  The empty tail is tested
but rejected by `stableGateSuffix`, so a trailing wall event yields `none`. -/
def gateHalfLifeOfLevels (levels : List CaptureLevel) : Option Nat :=
  levels.tails.findIdx? stableGateSuffix

/-- Executable half-life for one error class in the frozen OTT trajectory. -/
def gateHalfLife {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    (trajectory : OperationalTrajectory ErrorClass Institution)
    (errorClass : ErrorClass) : Option Nat :=
  gateHalfLifeOfLevels (classMaturity trajectory errorClass)

private theorem stable_gate_suffix_true_iff (levels : List CaptureLevel) :
    stableGateSuffix levels = true <->
      Not (levels = []) /\ forall level, level ∈ levels -> gate <= level := by
  cases levels with
  | nil => simp [stableGateSuffix]
  | cons head tail => simp [stableGateSuffix]

private theorem gate_half_life_of_levels_eq_some_iff
    (levels : List CaptureLevel) (index : Nat) :
    gateHalfLifeOfLevels levels = some index <->
      StableAtGate levels index /\
        forall earlier, earlier < index -> Not (StableAtGate levels earlier) := by
  unfold gateHalfLifeOfLevels
  rw [List.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨indexInTails, stableHere, noEarlier⟩
    have stableDrop : stableGateSuffix (levels.drop index) = true := by
      simpa only [List.getElem_tails] using stableHere
    have stableDescription :=
      (stable_gate_suffix_true_iff (levels.drop index)).mp stableDrop
    have indexInLevels : index < levels.length :=
      List.length_lt_of_drop_ne_nil stableDescription.1
    refine ⟨⟨indexInLevels, stableDescription.2⟩, ?_⟩
    intro earlier earlierBefore
    have earlierInTails : earlier < levels.tails.length := by
      rw [List.length_tails]
      exact Nat.lt_trans (Nat.lt_trans earlierBefore indexInLevels)
        (Nat.lt_add_one levels.length)
    have notStableEarlier :
        Not (stableGateSuffix (levels.drop earlier) = true) := by
      simpa only [List.getElem_tails] using noEarlier earlier earlierBefore
    intro earlierStable
    apply notStableEarlier
    apply (stable_gate_suffix_true_iff (levels.drop earlier)).mpr
    refine ⟨?_, earlierStable.2⟩
    intro droppedEmpty
    exact Nat.not_le_of_gt earlierStable.1
      (List.drop_eq_nil_iff.mp droppedEmpty)
  · rintro ⟨⟨indexInLevels, stableHere⟩, noEarlier⟩
    have indexInTails : index < levels.tails.length := by
      rw [List.length_tails]
      exact Nat.lt_trans indexInLevels (Nat.lt_add_one levels.length)
    refine ⟨indexInTails, ?_, ?_⟩
    · simpa only [List.getElem_tails] using
        (stable_gate_suffix_true_iff (levels.drop index)).mpr
          ⟨fun droppedEmpty =>
              Nat.not_le_of_gt indexInLevels
                (List.drop_eq_nil_iff.mp droppedEmpty),
            stableHere⟩
    · intro earlier earlierBefore
      have earlierInLevels : earlier < levels.length :=
        Nat.lt_trans earlierBefore indexInLevels
      have notStableEarlier :
          Not (stableGateSuffix (levels.drop earlier) = true) := by
        intro stableEarlier
        apply noEarlier earlier earlierBefore
        exact ⟨earlierInLevels,
          ((stable_gate_suffix_true_iff (levels.drop earlier)).mp stableEarlier).2⟩
      simpa only [List.getElem_tails] using notStableEarlier

private def inkNotDryWallEvent : Event Unit where
  errorClass := ()
  capture := wall
  registersInstitution := false
  institutionalDefect := false

/-- The attested ink-not-dry recurrence: three occurrences of one class are all
still caught only after collision with the wall. -/
def inkNotDryTrajectory : OperationalTrajectory Unit Unit where
  events := [inkNotDryWallEvent, inkNotDryWallEvent, inkNotDryWallEvent]
  institution := fun _ => ()

/-- T-C: the finite algorithm returns exactly the least stable gate suffix, and
the three-wall ink-not-dry trace remains unconverged. -/
theorem half_life_computable_and_ink_not_dry_nontrivial
    {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    (trajectory : OperationalTrajectory ErrorClass Institution)
    (errorClass : ErrorClass) (index : Nat) :
    (gateHalfLife trajectory errorClass = some index <->
      StableAtGate (classMaturity trajectory errorClass) index /\
        forall earlier, earlier < index ->
          Not (StableAtGate (classMaturity trajectory errorClass) earlier)) /\
      classMaturity inkNotDryTrajectory () = [wall, wall, wall] /\
      gateHalfLife inkNotDryTrajectory () = none := by
  exact ⟨gate_half_life_of_levels_eq_some_iff
      (classMaturity trajectory errorClass) index, rfl, rfl⟩

#print axioms half_life_computable_and_ink_not_dry_nontrivial

-- The domain and the stable predicate both have concrete finite inhabitants.
example : OperationalTrajectory Unit Unit := inkNotDryTrajectory

example : gateHalfLifeOfLevels [wall, gate, author] = some 1 := by
  decide

-- The counterexample conjunct is a checked term, not prose-only evidence.
example : gateHalfLife inkNotDryTrajectory () = none := by
  exact (half_life_computable_and_ink_not_dry_nontrivial
    inkNotDryTrajectory () 0).2.2

end D5.S3.ConceptDynamics.OperationalTuition.HalfLifeWellDefined
