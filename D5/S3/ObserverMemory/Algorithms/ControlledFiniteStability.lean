/- GID: D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ControlledFiniteStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite controlled observations stabilize at the maximal common invariant relation. -/

import D5.S1.Dynamics.KnasterTarski
import D5.S3.ObserverMemory.Algorithms.ControlledRelationRecursion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Lattice.Nat

/- Library-search audit trail (2026-08-21):
   * Repository exact hits `controlled_behavior_relation_recursion`,
     `controlled_signature_algorithm_correctness`, `ControlledCompletion`, and
     `completionProjection` are imported and applied below.
   * Pinned Mathlib exact hits `Fintype.card_le_of_surjective`,
     `Fintype.bijective_iff_surjective_and_card`, and `Nat.sInf_mem` support
     the finite quotient and least-stability arguments.
   * No single repository or Mathlib theorem packages branching controlled
     fixed-point maximality together with the finite quotient bound. -/

namespace D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization
open D5.S3.ObserverMemory.Algorithms.ControlledRelationRecursion

universe u

noncomputable section

/-- The complete controlled relation, built from every finite input word. -/
def controlledLimitRelation {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) : Set (Y × Y) :=
  {pair | controlledBehavior update readout pair.1 =
      controlledBehavior update readout pair.2}

/-- The source's common-invariant refinement operator. -/
def controlledRefinementOperator {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    Set (Y × Y) →o Set (Y × Y) where
  toFun relation :=
    readoutKernel readout ∩
      ⋂ input : U,
        (Prod.map (update input) (update input)) ⁻¹' relation
  monotone' := by
    intro first second h pair hp
    refine ⟨hp.1, ?_⟩
    exact Set.mem_iInter.mpr fun input => h (Set.mem_iInter.mp hp.2 input)

/-- Quotient classes at a bounded controlled depth. -/
abbrev controlledDepthSetoid {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) : Setoid Y :=
  Setoid.ker (controlledSignature update readout depth)

/-- Quotient classes of complete controlled behaviors. -/
abbrev controlledLimitSetoid {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) : Setoid Y :=
  Setoid.ker (controlledBehavior update readout)

/-- A bounded relation is exactly equality of the corresponding recursive labels. -/
private theorem controlled_depth_setoid_rel_iff
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) (y y' : Y) :
    controlledDepthSetoid update readout depth y y' ↔
      (y, y') ∈ controlledDepthRelation update readout depth := by
  change controlledSignature update readout depth y =
      controlledSignature update readout depth y' ↔ _
  exact (controlled_signature_algorithm_correctness update readout hreadout).1
    depth y y'

private theorem controlled_depth_succ_le
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    controlledDepthSetoid update readout (depth + 1) ≤
      controlledDepthSetoid update readout depth := by
  intro y y' h
  have hbounded : (y, y') ∈ controlledDepthRelation update readout (depth + 1) :=
    (controlled_depth_setoid_rel_iff update readout hreadout (depth + 1) y y').mp h
  apply (controlled_depth_setoid_rel_iff update readout hreadout depth y y').mpr
  intro word hlength
  exact hbounded word (hlength.trans (Nat.le_add_right _ _))

/-- The finite quotient at a bounded controlled depth is inhabited and finite. -/
noncomputable instance controlledDepthQuotientFintype
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) :
    Fintype (Quotient (controlledDepthSetoid update readout depth)) := by
  classical
  exact Fintype.ofSurjective (Quotient.mk _) Quotient.mk_surjective

def controlledClassCount {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) : Nat :=
  Fintype.card (Quotient (controlledDepthSetoid update readout depth))

def controlledLimitClassCount {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) : Nat :=
  Fintype.card (Quotient (controlledLimitSetoid update readout))

noncomputable def controlledForget
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    Quotient (controlledDepthSetoid update readout (depth + 1)) ->
      Quotient (controlledDepthSetoid update readout depth) :=
  Quotient.lift (Quotient.mk _) (by
    intro y y' h
    apply Quotient.sound
    exact controlled_depth_succ_le update readout hreadout depth h)

private theorem controlledForget_surjective
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    Function.Surjective (controlledForget update readout hreadout depth) := by
  intro state
  obtain ⟨y, rfl⟩ := Quotient.exists_rep state
  exact ⟨Quotient.mk _ y, rfl⟩

private theorem controlledClassCount_mono
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    controlledClassCount update readout depth ≤
      controlledClassCount update readout (depth + 1) := by
  exact Fintype.card_le_of_surjective
    (controlledForget update readout hreadout depth)
    (controlledForget_surjective update readout hreadout depth)

private theorem controlled_setoid_eq_of_class_count_eq
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat)
    (hcount : controlledClassCount update readout depth =
      controlledClassCount update readout (depth + 1)) :
    controlledDepthSetoid update readout depth =
      controlledDepthSetoid update readout (depth + 1) := by
  have hbijective : Function.Bijective (controlledForget update readout hreadout depth) :=
    (Fintype.bijective_iff_surjective_and_card
      (controlledForget update readout hreadout depth)).2
      ⟨controlledForget_surjective update readout hreadout depth, hcount.symm⟩
  apply Setoid.ext
  intro y y'
  constructor
  · intro h
    apply Quotient.exact
    apply hbijective.1
    simpa only [controlledForget, Quotient.lift_mk] using Quotient.sound h
  · intro h
    exact controlled_depth_succ_le update readout hreadout depth h

private theorem controlledClassCount_le_state_count
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) :
    controlledClassCount update readout depth ≤ Fintype.card Y := by
  exact Fintype.card_le_of_surjective (Quotient.mk _)
    Quotient.mk_surjective

private theorem controlled_initial_class_count
    {Y : Type*} {U O : Type u} [Fintype Y] [Fintype O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    controlledClassCount update readout 0 = Fintype.card O := by
  classical
  let quotientReadout :
      Quotient (Setoid.ker readout) -> O :=
    Quotient.lift readout (by
      intro y y' h
      exact h)
  have quotientReadout_surjective : Function.Surjective quotientReadout := by
    intro output
    obtain ⟨y, hy⟩ := hreadout output
    exact ⟨Quotient.mk _ y, hy⟩
  have quotientReadout_injective : Function.Injective quotientReadout := by
    intro first second h
    obtain ⟨y, rfl⟩ := Quotient.exists_rep first
    obtain ⟨y', rfl⟩ := Quotient.exists_rep second
    apply Quotient.sound
    exact h
  letI : Fintype (Quotient (Setoid.ker readout)) :=
    Fintype.ofSurjective (Quotient.mk _) Quotient.mk_surjective
  have hcard := Fintype.card_congr
    (Equiv.ofBijective quotientReadout
      ⟨quotientReadout_injective, quotientReadout_surjective⟩)
  change Fintype.card (Quotient (Setoid.ker readout)) = Fintype.card O
  exact hcard

/-- Every complete behavior relation lies below the current readout kernel. -/
private theorem controlled_limit_below_kernel
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    controlledLimitRelation update readout ≤ readoutKernel readout := by
  intro pair h
  simpa [controlledLimitRelation, controlledBehavior, runWord, readoutKernel] using
    congrFun h []

/-- The complete controlled relation is forward stable for every input. -/
private theorem controlled_limit_invariant
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    forall input pair, pair ∈ controlledLimitRelation update readout ->
      (update input pair.1, update input pair.2) ∈
        controlledLimitRelation update readout := by
  intro input pair h
  change controlledBehavior update readout (update input pair.1) =
    controlledBehavior update readout (update input pair.2)
  funext word
  simpa [controlledLimitRelation, controlledBehavior, runWord] using
    congrFun h (input :: word)

/-- A kernel relation invariant under all controlled successors is complete. -/
private theorem controlled_relation_le_limit
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O)
    (relation : Set (Y × Y))
    (belowKernel : relation ≤ readoutKernel readout)
    (invariant : forall input pair, pair ∈ relation ->
      (update input pair.1, update input pair.2) ∈ relation) :
    relation ≤ controlledLimitRelation update readout := by
  intro pair hp
  change controlledBehavior update readout pair.1 =
    controlledBehavior update readout pair.2
  funext word
  induction word generalizing pair with
  | nil =>
      have hcurrent := belowKernel hp
      change readout pair.1 = readout pair.2 at hcurrent
      simpa [controlledBehavior, runWord] using hcurrent
  | cons input word ih =>
      have hnext := invariant input pair hp
      simpa [controlledBehavior, runWord] using
        ih hnext

/-- The complete relation is a fixed point of the common-invariant operator. -/
private theorem controlled_limit_fixed
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    controlledRefinementOperator update readout
        (controlledLimitRelation update readout) =
      controlledLimitRelation update readout := by
  ext pair
  constructor
  · intro hp
    have hcurrent : readout pair.1 = readout pair.2 := hp.1
    have hsuccessors : forall input,
        (update input pair.1, update input pair.2) ∈
          controlledLimitRelation update readout :=
      Set.mem_iInter.mp hp.2
    change controlledBehavior update readout pair.1 =
      controlledBehavior update readout pair.2
    funext word
    induction word with
    | nil => simpa [controlledLimitRelation, controlledBehavior, runWord] using hcurrent
    | cons input word ih =>
        simpa [controlledBehavior, runWord] using congrFun (hsuccessors input) word
  · intro hp
    refine ⟨controlled_limit_below_kernel update readout hp, ?_⟩
    exact Set.mem_iInter.mpr fun input => controlled_limit_invariant
      update readout input pair hp

/-- The complete relation is the greatest fixed point of the source operator. -/
private theorem controlled_limit_eq_gfp
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    controlledLimitRelation update readout =
      (controlledRefinementOperator update readout).gfp := by
  let operator := controlledRefinementOperator update readout
  have hfixed : operator (controlledLimitRelation update readout) =
      controlledLimitRelation update readout := controlled_limit_fixed update readout
  have hExtrema := D5.S1.Dynamics.KnasterTarski.knaster_tarski_extremal_fixed_points operator
  apply le_antisymm
  · exact hExtrema.2.2 hfixed
  · apply controlled_relation_le_limit update readout operator.gfp
    · intro pair hp
      have hp' : pair ∈ operator operator.gfp := by
        rw [hExtrema.2.1]
        exact hp
      exact hp'.1
    · intro input pair hp
      have hp' : pair ∈ operator operator.gfp := by
        rw [hExtrema.2.1]
        exact hp
      exact Set.mem_iInter.mp hp'.2 input

private theorem controlled_stable_relation_eq_limit
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat)
    (stable : controlledDepthRelation update readout depth =
      controlledDepthRelation update readout (depth + 1)) :
    controlledDepthRelation update readout depth =
      controlledLimitRelation update readout := by
  apply le_antisymm
  · apply controlled_relation_le_limit update readout
      (controlledDepthRelation update readout depth)
    · intro pair hp
      change boundedWordEquivalent update readout depth pair.1 pair.2 at hp
      simpa [readoutKernel, runWord] using hp [] (Nat.zero_le depth)
    · intro input pair hp
      have hrec := (controlled_behavior_relation_recursion update readout depth).2
      have hfixed : pair ∈ controlledRefinementOperator update readout
          (controlledDepthRelation update readout depth) := by
        change pair ∈ readoutKernel readout ∩
          ⋂ input : U,
            (Prod.map (update input) (update input)) ⁻¹'
              controlledDepthRelation update readout depth
        rw [← hrec, ← stable]
        exact hp
      exact Set.mem_iInter.mp hfixed.2 input
  · intro pair hp word hlength
    exact congrFun hp word

/-- Relations that are equivalences, refine current readout equality, and are
preserved by every controlled transition. -/
def commonStableEquivalences {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) : Set (Set (Y × Y)) :=
  {relation |
    Equivalence (fun y y' => (y, y') ∈ relation) ∧
      relation ≤ readoutKernel readout ∧
      forall input pair, pair ∈ relation ->
        (update input pair.1, update input pair.2) ∈ relation}

private theorem controlled_limit_is_greatest_stable_equivalence
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    IsGreatest (commonStableEquivalences update readout)
      (controlledLimitRelation update readout) := by
  constructor
  · refine ⟨?_, controlled_limit_below_kernel update readout,
      controlled_limit_invariant update readout⟩
    constructor
    · intro y
      rfl
    · intro y y' h
      exact h.symm
    · intro y y' y'' hxy hyz
      exact hxy.trans hyz
  · intro relation hrelation
    exact controlled_relation_le_limit update readout relation
      hrelation.2.1 hrelation.2.2

private theorem controlled_permanent_stability
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth offset : Nat)
    (stable : controlledDepthRelation update readout depth =
      controlledDepthRelation update readout (depth + 1)) :
    controlledDepthRelation update readout (depth + offset) =
      controlledDepthRelation update readout depth := by
  have hrec := (controlled_behavior_relation_recursion update readout depth).2
  have hfixed : controlledRefinementOperator update readout
      (controlledDepthRelation update readout depth) =
        controlledDepthRelation update readout depth := by
    change readoutKernel readout ∩
        ⋂ input : U,
          (Prod.map (update input) (update input)) ⁻¹'
            controlledDepthRelation update readout depth =
      controlledDepthRelation update readout depth
    rw [← hrec, ← stable]
  induction offset with
  | zero => simp
  | succ offset ih =>
      calc
        controlledDepthRelation update readout (depth + (offset + 1)) =
            controlledDepthRelation update readout ((depth + offset) + 1) := by
              rfl
        _ = controlledRefinementOperator update readout
              (controlledDepthRelation update readout (depth + offset)) := by
              exact (controlled_behavior_relation_recursion update readout
                (depth + offset)).2
        _ = controlledRefinementOperator update readout
              (controlledDepthRelation update readout depth) :=
              congrArg (controlledRefinementOperator update readout) ih
        _ = controlledDepthRelation update readout depth := hfixed

/-- The first depth at which two consecutive controlled quotients agree. -/
noncomputable def controlledStabilityDepth
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) : Nat :=
  sInf {depth | controlledDepthSetoid update readout depth =
    controlledDepthSetoid update readout (depth + 1)}

private theorem controlled_stable_setoid_exists
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    exists depth, controlledDepthSetoid update readout depth =
      controlledDepthSetoid update readout (depth + 1) := by
  let depth := stabilizationDepth update readout
  refine ⟨depth, ?_⟩
  apply Setoid.ext
  intro y y'
  change controlledSignature update readout depth y =
      controlledSignature update readout depth y' ↔
    controlledSignature update readout (depth + 1) y =
      controlledSignature update readout (depth + 1) y'
  simpa [depth] using
    ((controlled_signature_algorithm_correctness update readout hreadout).2.2.1
      1 y y').symm

private theorem controlled_stable_setoid_to_relation
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat)
    (stable : controlledDepthSetoid update readout depth =
      controlledDepthSetoid update readout (depth + 1)) :
    controlledDepthRelation update readout depth =
      controlledDepthRelation update readout (depth + 1) := by
  ext pair
  constructor
  · intro h
    apply (controlled_depth_setoid_rel_iff update readout hreadout
      (depth + 1) pair.1 pair.2).mp
    rw [← stable]
    exact (controlled_depth_setoid_rel_iff update readout hreadout
      depth pair.1 pair.2).mpr h
  · intro h
    apply (controlled_depth_setoid_rel_iff update readout hreadout
      depth pair.1 pair.2).mp
    rw [stable]
    exact (controlled_depth_setoid_rel_iff update readout hreadout
      (depth + 1) pair.1 pair.2).mpr h

private theorem controlled_relation_stable_to_setoid
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat)
    (stable : controlledDepthRelation update readout depth =
      controlledDepthRelation update readout (depth + 1)) :
    controlledDepthSetoid update readout depth =
      controlledDepthSetoid update readout (depth + 1) := by
  apply Setoid.ext
  intro y y'
  constructor
  · intro h
    apply (controlled_depth_setoid_rel_iff update readout hreadout
      (depth + 1) y y').mpr
    rw [← stable]
    exact (controlled_depth_setoid_rel_iff update readout hreadout
      depth y y').mp h
  · intro h
    apply (controlled_depth_setoid_rel_iff update readout hreadout
      depth y y').mpr
    rw [stable]
    exact (controlled_depth_setoid_rel_iff update readout hreadout
      (depth + 1) y y').mp h

private theorem controlled_limit_class_count_le_state_count
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) :
    controlledLimitClassCount update readout ≤ Fintype.card Y := by
  exact Fintype.card_le_of_surjective
    (completionProjection update readout) Quotient.mk_surjective

private theorem controlled_class_count_at_stability
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout)
    (stable : controlledDepthSetoid update readout
        (controlledStabilityDepth update readout) =
      controlledDepthSetoid update readout
        (controlledStabilityDepth update readout + 1)) :
    controlledClassCount update readout
        (controlledStabilityDepth update readout) =
      controlledLimitClassCount update readout := by
  let depth := controlledStabilityDepth update readout
  have hrelation : controlledDepthRelation update readout depth =
      controlledLimitRelation update readout :=
    controlled_stable_relation_eq_limit update readout depth
      (controlled_stable_setoid_to_relation update readout hreadout depth stable)
  let quotientEquiv :
      Quotient (controlledDepthSetoid update readout depth) ≃
        Quotient (controlledLimitSetoid update readout) :=
    Quotient.congrRight fun y y' =>
      (controlled_depth_setoid_rel_iff update readout hreadout depth y y').trans
        (by
          change (y, y') ∈ controlledDepthRelation update readout depth ↔
            (y, y') ∈ controlledLimitRelation update readout
          rw [hrelation])
  exact Fintype.card_congr quotientEquiv

/-- For a finite controlled system, one stable refinement is permanent. The
complete behavior relation is both the refinement operator's greatest fixed
point and the greatest common stable equivalence. Its least stable depth is
bounded by the available increase in quotient classes. -/
theorem controlled_finite_stability
    {Y : Type*} {U O : Type u} [Fintype Y] [Fintype U] [Fintype O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    (forall depth,
      controlledDepthRelation update readout depth =
          controlledDepthRelation update readout (depth + 1) ->
        forall offset,
          controlledDepthRelation update readout (depth + offset) =
            controlledDepthRelation update readout depth) ∧
    controlledLimitRelation update readout =
      (controlledRefinementOperator update readout).gfp ∧
    IsGreatest (commonStableEquivalences update readout)
      (controlledLimitRelation update readout) ∧
    ((controlledDepthRelation update readout
          (controlledStabilityDepth update readout) =
        controlledDepthRelation update readout
          (controlledStabilityDepth update readout + 1)) ∧
      forall depth,
        controlledDepthRelation update readout depth =
            controlledDepthRelation update readout (depth + 1) ->
          controlledStabilityDepth update readout ≤ depth) ∧
    controlledStabilityDepth update readout ≤
      controlledLimitClassCount update readout - Fintype.card O ∧
    controlledLimitClassCount update readout - Fintype.card O ≤
      Fintype.card Y - Fintype.card O := by
  have hstableExists := controlled_stable_setoid_exists update readout hreadout
  have hstableSetoid : controlledDepthSetoid update readout
      (controlledStabilityDepth update readout) =
    controlledDepthSetoid update readout
      (controlledStabilityDepth update readout + 1) := by
    exact Nat.sInf_mem hstableExists
  have hstableRelation : controlledDepthRelation update readout
      (controlledStabilityDepth update readout) =
    controlledDepthRelation update readout
      (controlledStabilityDepth update readout + 1) :=
    controlled_stable_setoid_to_relation update readout hreadout
      (controlledStabilityDepth update readout) hstableSetoid
  have hminimalRelation : forall depth,
      controlledDepthRelation update readout depth =
          controlledDepthRelation update readout (depth + 1) ->
        controlledStabilityDepth update readout ≤ depth := by
    intro depth hstable
    exact Nat.sInf_le
      (controlled_relation_stable_to_setoid update readout hreadout depth hstable)
  have hgrowth : forall depth, depth ≤ controlledStabilityDepth update readout ->
      controlledClassCount update readout 0 + depth ≤
        controlledClassCount update readout depth := by
    intro depth hdepth
    induction depth with
    | zero => simp
    | succ depth ih =>
        have hlt : depth < controlledStabilityDepth update readout := by omega
        have hcountNe : controlledClassCount update readout depth ≠
            controlledClassCount update readout (depth + 1) := by
          intro hcount
          have hstable := controlled_setoid_eq_of_class_count_eq
            update readout hreadout depth hcount
          exact (Nat.not_le_of_lt hlt) (Nat.sInf_le hstable)
        have hstrict : controlledClassCount update readout depth <
            controlledClassCount update readout (depth + 1) :=
          lt_of_le_of_ne (controlledClassCount_mono update readout hreadout depth)
            hcountNe
        have hprior := ih (by omega)
        omega
  have hclassAtStable := controlled_class_count_at_stability
    update readout hreadout hstableSetoid
  have hinitial := controlled_initial_class_count update readout hreadout
  have hlimitUpper := controlled_limit_class_count_le_state_count update readout
  have hgrowthAtStable := hgrowth (controlledStabilityDepth update readout) le_rfl
  refine ⟨(fun depth stable offset =>
      controlled_permanent_stability update readout depth offset stable),
    controlled_limit_eq_gfp update readout,
    controlled_limit_is_greatest_stable_equivalence update readout,
    ⟨hstableRelation, hminimalRelation⟩, ?_, ?_⟩
  · omega
  · omega

/-- The finite, nonempty hypotheses and realized-output convention have a
concrete model. -/
example : Function.Surjective (id : Bool -> Bool) := Function.surjective_id

/-- The theorem applies to the concrete controlled identity system. -/
example :
    let update : Bool -> Bool -> Bool := fun _ state => state
    controlledLimitRelation update id =
      (controlledRefinementOperator update id).gfp := by
  dsimp
  exact (controlled_finite_stability (fun _ : Bool => id) id
    Function.surjective_id).2.1

#print axioms controlled_finite_stability

end

end D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability
