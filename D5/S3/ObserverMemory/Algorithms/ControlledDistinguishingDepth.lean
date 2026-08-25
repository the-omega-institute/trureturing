/- GID: D5/S3/ObserverMemory/Algorithms/ControlledDistinguishingDepth
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ControlledDistinguishingDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Shortest distinguishing words characterize controlled completion depth. -/

import D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability

/- Library-search audit trail (2026-08-21):
   * Repository exact hits `runWord`, `controlledDepthRelation`,
     `controlledLimitRelation`, `controlledStabilityDepth`, and
     `controlled_finite_stability` supply the canonical controlled-word
     semantics and least-stability result; they are imported and applied below.
   * The autonomous `shortest_distance_eq_none_iff` is a close, non-exact hit:
     it treats one update rather than an input-indexed update family.
   * Pinned Mathlib exact hits `Nat.find_spec`, `Nat.find_min'`,
     `Finset.le_sup'`, and `Finset.sup'_le` support least-word selection and the
     nonempty finite maximum. No repository or pinned-Mathlib theorem packages
     both branching-input clauses proved here.
   * `loogle` and `leansearch` executables are absent from PATH. -/

namespace D5.S3.ObserverMemory.Algorithms.ControlledDistinguishingDepth

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization
open D5.S3.ObserverMemory.Algorithms.ControlledRelationRecursion
open D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability

universe u

noncomputable section

/-- A word of the stated length separates a state pair through the readout. -/
def distinguishesAtDepth {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O)
    (pair : Y × Y) (depth : Nat) : Prop :=
  ∃ word : List U, word.length = depth ∧
    readout (runWord update word pair.1) ≠
      readout (runWord update word pair.2)

/-- The least length of an input word that distinguishes a pair, with `none`
for pairs indistinguishable by every finite input word. -/
noncomputable def shortestDistinguishingDepth {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O)
    (pair : Y × Y) : Option Nat := by
  classical
  exact if h : ∃ depth, distinguishesAtDepth update readout pair depth then
    some (Nat.find h)
  else
    none

/-- The finite state pairs that admit a distinguishing input word. -/
noncomputable def finitelyDistinguishablePairs
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) : Finset (Y × Y) := by
  classical
  exact Finset.univ.filter fun pair =>
    (shortestDistinguishingDepth update readout pair).isSome

private theorem shortest_depth_some_iff
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O)
    (pair : Y × Y) (depth : Nat) :
    shortestDistinguishingDepth update readout pair = some depth ↔
      distinguishesAtDepth update readout pair depth ∧
        ∀ earlier < depth,
          ¬ distinguishesAtDepth update readout pair earlier := by
  classical
  rw [shortestDistinguishingDepth]
  split_ifs with h
  · simp only [Option.some.injEq]
    exact Nat.find_eq_iff h
  · constructor
    · intro heq
      cases heq
    · intro hdepth
      exact False.elim (h ⟨depth, hdepth.1⟩)

private theorem mem_controlled_depth_iff_shortest_later
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O)
    (pair : Y × Y) (horizon : Nat) :
    pair ∈ controlledDepthRelation update readout horizon ↔
      ∀ depth, shortestDistinguishingDepth update readout pair = some depth ->
        horizon < depth := by
  classical
  constructor
  · intro hbounded depth hdepth
    have hspec := (shortest_depth_some_iff update readout pair depth).mp hdepth
    rcases hspec.1 with ⟨word, hlength, hne⟩
    change boundedWordEquivalent update readout horizon pair.1 pair.2 at hbounded
    by_contra hnot
    exact hne (hbounded word (by omega))
  · intro hlater
    change boundedWordEquivalent update readout horizon pair.1 pair.2
    intro word hlength
    by_contra hne
    have hdistinguishes : distinguishesAtDepth update readout pair word.length :=
      ⟨word, rfl, hne⟩
    have hexists : ∃ depth, distinguishesAtDepth update readout pair depth :=
      ⟨word.length, hdistinguishes⟩
    have hsome : shortestDistinguishingDepth update readout pair =
        some (Nat.find hexists) := by
      simp [shortestDistinguishingDepth, hexists]
    have hleast : Nat.find hexists ≤ word.length :=
      Nat.find_min' hexists hdistinguishes
    have hstrict := hlater (Nat.find hexists) hsome
    omega

/-- Infinite shortest-word distance is exactly complete controlled behavior
equivalence. -/
theorem shortest_distinguishing_depth_eq_none_iff
    {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (pair : Y × Y) :
    shortestDistinguishingDepth update readout pair = none ↔
      pair ∈ controlledLimitRelation update readout := by
  classical
  constructor
  · intro hnone
    change controlledBehavior update readout pair.1 =
      controlledBehavior update readout pair.2
    funext word
    by_contra hne
    have hexists : ∃ depth, distinguishesAtDepth update readout pair depth :=
      ⟨word.length, word, rfl, hne⟩
    simp [shortestDistinguishingDepth, hexists] at hnone
  · intro hlimit
    change controlledBehavior update readout pair.1 =
      controlledBehavior update readout pair.2 at hlimit
    rw [shortestDistinguishingDepth]
    split_ifs with hexists
    · rcases Nat.find_spec hexists with ⟨word, hlength, hne⟩
      exact False.elim (hne (congrFun hlimit word))
    · rfl

private theorem controlled_relation_stable_at_latest
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hdistinguishable :
      (finitelyDistinguishablePairs update readout).Nonempty) :
    let latest := (finitelyDistinguishablePairs update readout).sup'
      hdistinguishable fun pair =>
        (shortestDistinguishingDepth update readout pair).getD 0
    controlledDepthRelation update readout latest =
      controlledDepthRelation update readout (latest + 1) := by
  classical
  let latest := (finitelyDistinguishablePairs update readout).sup'
    hdistinguishable fun pair =>
      (shortestDistinguishingDepth update readout pair).getD 0
  apply Set.ext
  intro pair
  constructor
  · intro hbounded
    apply (mem_controlled_depth_iff_shortest_later update readout pair
      (latest + 1)).2
    intro depth hdepth
    have hmem : pair ∈ finitelyDistinguishablePairs update readout := by
      simp [finitelyDistinguishablePairs, hdepth]
    have hle := Finset.le_sup'
      (f := fun pair : Y × Y =>
        (shortestDistinguishingDepth update readout pair).getD 0)
      hmem
    have hdepthLater :=
      (mem_controlled_depth_iff_shortest_later update readout pair latest).1
        hbounded depth hdepth
    rw [hdepth] at hle
    simp only [Option.getD_some] at hle
    have hleLatest : depth ≤ latest := by
      exact hle
    omega
  · intro hbounded
    apply (mem_controlled_depth_iff_shortest_later update readout pair latest).2
    intro depth hdepth
    have := (mem_controlled_depth_iff_shortest_later update readout pair
      (latest + 1)).1 hbounded depth hdepth
    omega

/-- For finite controlled systems, infinite distance characterizes the complete
relation, and the least stable refinement depth is the largest finite shortest
distinguishing-word depth whenever such a pair exists. -/
theorem controlled_shortest_intervention_witness
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    (∀ pair : Y × Y,
      shortestDistinguishingDepth update readout pair = none ↔
        pair ∈ controlledLimitRelation update readout) ∧
    (∀ hdistinguishable :
        (finitelyDistinguishablePairs update readout).Nonempty,
      controlledStabilityDepth update readout =
        (finitelyDistinguishablePairs update readout).sup'
          hdistinguishable fun pair =>
            (shortestDistinguishingDepth update readout pair).getD 0) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype O := Fintype.ofFinite O
  refine ⟨shortest_distinguishing_depth_eq_none_iff update readout, ?_⟩
  intro hdistinguishable
  let latest := (finitelyDistinguishablePairs update readout).sup'
    hdistinguishable fun pair =>
      (shortestDistinguishingDepth update readout pair).getD 0
  have hfinite := controlled_finite_stability update readout hreadout
  have hstableCanonical : controlledDepthRelation update readout
      (controlledStabilityDepth update readout) =
    controlledDepthRelation update readout
      (controlledStabilityDepth update readout + 1) :=
    hfinite.2.2.2.1.1
  have hstableLatest : controlledDepthRelation update readout latest =
      controlledDepthRelation update readout (latest + 1) := by
    exact controlled_relation_stable_at_latest update readout hdistinguishable
  apply le_antisymm
  · exact hfinite.2.2.2.1.2 latest hstableLatest
  · apply Finset.sup'_le
    intro pair hpair
    cases hdepth : shortestDistinguishingDepth update readout pair with
    | none =>
        simp [finitelyDistinguishablePairs, hdepth] at hpair
    | some depth =>
        simp only [Option.getD_some]
        by_contra hnotle
        have hstrict : controlledStabilityDepth update readout < depth :=
          Nat.lt_of_not_ge hnotle
        have hbounded : pair ∈ controlledDepthRelation update readout
            (controlledStabilityDepth update readout) := by
          apply (mem_controlled_depth_iff_shortest_later update readout pair
            (controlledStabilityDepth update readout)).2
          intro candidate hcand
          rw [hdepth] at hcand
          injection hcand with heq
          simpa [heq] using hstrict
        have hpermanent := hfinite.1
          (controlledStabilityDepth update readout) hstableCanonical
          (depth - controlledStabilityDepth update readout)
        have hsum : controlledStabilityDepth update readout +
            (depth - controlledStabilityDepth update readout) = depth :=
          Nat.add_sub_of_le (Nat.le_of_lt hstrict)
        have hboundedAtDepth : pair ∈
            controlledDepthRelation update readout depth := by
          rw [← hsum, hpermanent]
          exact hbounded
        have himpossible :=
          (mem_controlled_depth_iff_shortest_later update readout pair depth).1
            hboundedAtDepth depth hdepth
        omega

/-- The source hypotheses and the distinguishable-pair premise have a concrete
two-state model. -/
example :
    let update : Unit -> Bool -> Bool := fun _ state => state
    (finitelyDistinguishablePairs update id).Nonempty := by
  dsimp
  refine ⟨(false, true), ?_⟩
  have hexists : ∃ depth,
      distinguishesAtDepth (fun _ : Unit => fun state : Bool => state)
        id (false, true) depth :=
    ⟨0, [], rfl, Bool.false_ne_true⟩
  rw [finitelyDistinguishablePairs]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [shortestDistinguishingDepth]
  simp only [dif_pos hexists, Option.isSome_some]

#print axioms controlled_shortest_intervention_witness

end

end D5.S3.ObserverMemory.Algorithms.ControlledDistinguishingDepth
