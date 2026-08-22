/- GID: D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adjacent core points and phase-labeled frontier paths have unique edges. -/

import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentCore

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiCarryTransducer

noncomputable section

/-- `r` is the first core point strictly after `q`. -/
def AdjacentCorePoint (w : List Bool) (q r : Nat) : Prop :=
  q ∈ Core w ∧ r ∈ Core w ∧ q < r ∧
    ∀ s ∈ Core w, q < s → r ≤ s

theorem adjacent_core_point_right_unique {w : List Bool} {q r₁ r₂ : Nat}
    (h₁ : AdjacentCorePoint w q r₁)
    (h₂ : AdjacentCorePoint w q r₂) :
    r₁ = r₂ := by
  apply Nat.le_antisymm
  · exact h₁.2.2.2 r₂ h₂.2.1 h₂.2.2.1
  · exact h₂.2.2.2 r₁ h₁.2.1 h₁.2.2.1

/-- Consecutive values of a complete strict core enumeration are adjacent. -/
theorem frontier_consecutive_core_adjacent {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) (n : Nat) :
    AdjacentCorePoint w (certificate.enumerate n)
      (certificate.enumerate (n + 1)) := by
  have hstrict : StrictMono certificate.enumerate :=
    strictMono_nat_of_lt_succ hcertificate.successor_strict
  refine ⟨?_, ?_, hcertificate.successor_strict n, ?_⟩
  · rw [← hcertificate.range_eq]
    exact ⟨n, rfl⟩
  · rw [← hcertificate.range_eq]
    exact ⟨n + 1, rfl⟩
  · intro s hs hns
    rw [← hcertificate.range_eq] at hs
    obtain ⟨m, rfl⟩ := hs
    by_cases hnext : n + 1 ≤ m
    · exact hstrict.monotone hnext
    · have hmn : m ≤ n := by omega
      exact (not_lt_of_ge (hstrict.monotone hmn) hns).elim

/-- Any locally adjacent candidate is forced to be the enumerated successor. -/
theorem adjacent_core_point_eq_frontier_successor {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) {n r : Nat}
    (hedge : AdjacentCorePoint w (certificate.enumerate n) r) :
    r = certificate.enumerate (n + 1) :=
  adjacent_core_point_right_unique hedge
    (frontier_consecutive_core_adjacent hcertificate n)

/-- A carry-reachable frontier step labeled by its prefix phase and its
aperiodic family input letter. -/
structure PhaseLabeledReachability (certificate : FrontierReturnWord)
    (n : Nat) where
  phase : FrontierPhase
  letter : Bool
  phase_eq : phase = certificate.phase
  letter_eq : letter =
    familyLetter (frontierFamily certificate.phase) n
  reachable : FrontierRunStep certificate n

def phaseLabeledReachability {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) (n : Nat) :
    PhaseLabeledReachability certificate n :=
  { phase := certificate.phase
    letter := familyLetter (frontierFamily certificate.phase) n
    phase_eq := rfl
    letter_eq := rfl
    reachable := hcertificate.run_step n }

/-- The six-state prefix label is preserved along every labeled frontier
reachability witness. The input letter is retained separately and may vary. -/
theorem phase_labeled_reachability_phase_preserved
    {certificate : FrontierReturnWord} {m n : Nat}
    (left : PhaseLabeledReachability certificate m)
    (right : PhaseLabeledReachability certificate n) :
    left.phase = right.phase :=
  left.phase_eq.trans right.phase_eq.symm

/-- A phase-labeled reachable step whose selected Lucas candidate is an
actual adjacent core point. -/
structure PhaseEnrichedCoreEdge (w : List Bool)
    (certificate : FrontierReturnWord) (n : Nat) where
  target : Nat
  labeled : PhaseLabeledReachability certificate n
  adjacent : AdjacentCorePoint w (certificate.enumerate n) target
  additive : (target : Int) = certificate.enumerate n +
    if labeled.letter then certificate.a else certificate.b

/-- An adjacent edge has one target, one prefix phase, and one input label. -/
theorem phase_enriched_core_edge_unique {w : List Bool}
    {certificate : FrontierReturnWord} {n : Nat}
    (left right : PhaseEnrichedCoreEdge w certificate n) :
    left.target = right.target ∧
      left.labeled.phase = right.labeled.phase ∧
      left.labeled.letter = right.labeled.letter := by
  exact ⟨adjacent_core_point_right_unique left.adjacent right.adjacent,
    left.labeled.phase_eq.trans right.labeled.phase_eq.symm,
    left.labeled.letter_eq.trans right.labeled.letter_eq.symm⟩

/-- Erasing the labels and the adjacent-core witness recovers the frozen
carry reachability relation. -/
theorem phase_enriched_core_edge_erases {w : List Bool}
    {certificate : FrontierReturnWord} {n : Nat}
    (edge : PhaseEnrichedCoreEdge w certificate n) :
    FrontierRunStep certificate n :=
  edge.labeled.reachable

def PhaseEnrichedCoreTrace (w : List Bool)
    (certificate : FrontierReturnWord) : Prop :=
  ∀ n : Nat, Nonempty (PhaseEnrichedCoreEdge w certificate n)

/-- The enriched trace supplies the exact phase-selected additive equation. -/
theorem phase_enriched_core_trace_gap_additive {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : PhaseEnrichedCoreTrace w certificate) :
    ∀ n : Nat, (certificate.enumerate (n + 1) : Int) =
      certificate.enumerate n +
        if familyLetter (frontierFamily certificate.phase) n then
          certificate.a else certificate.b := by
  intro n
  obtain ⟨edge⟩ := htrace n
  have htarget := adjacent_core_point_eq_frontier_successor
    hcertificate edge.adjacent
  rw [← htarget]
  simpa only [edge.labeled.letter_eq] using edge.additive

theorem phase_enriched_core_trace_two_gap_additive {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : PhaseEnrichedCoreTrace w certificate) :
    ∀ n : Nat,
      (certificate.enumerate (n + 1) : Int) =
          certificate.enumerate n + certificate.a ∨
        (certificate.enumerate (n + 1) : Int) =
          certificate.enumerate n + certificate.b := by
  intro n
  have hgap := phase_enriched_core_trace_gap_additive hcertificate htrace n
  cases hletter : familyLetter (frontierFamily certificate.phase) n
  · right
    simpa [hletter] using hgap
  · left
    simpa [hletter] using hgap

theorem phase_enriched_core_trace_gap_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : PhaseEnrichedCoreTrace w certificate) :
    FrontierGapPhase certificate := by
  intro n
  have hgap := phase_enriched_core_trace_gap_additive hcertificate htrace n
  simp only [FrontierReturnWord.gap]
  omega

/-- A proved gap phase constructs the enriched trace without choosing any
semantic field: every field is the actual enumerated endpoint or derived
phase/input label. -/
theorem phase_enriched_core_trace_of_gap_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hphase : FrontierGapPhase certificate) :
    PhaseEnrichedCoreTrace w certificate := by
  intro n
  refine ⟨{
    target := certificate.enumerate (n + 1)
    labeled := phaseLabeledReachability hcertificate n
    adjacent := frontier_consecutive_core_adjacent hcertificate n
    additive := ?_ }⟩
  have hgap := hphase n
  simp only [FrontierReturnWord.gap] at hgap
  change (certificate.enumerate (n + 1) : Int) =
    certificate.enumerate n +
      if familyLetter (frontierFamily certificate.phase) n then
        certificate.a else certificate.b
  exact sub_eq_iff_eq_add'.mp hgap

theorem phase_enriched_core_trace_iff_gap_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    PhaseEnrichedCoreTrace w certificate ↔ FrontierGapPhase certificate :=
  ⟨phase_enriched_core_trace_gap_phase hcertificate,
    phase_enriched_core_trace_of_gap_phase hcertificate⟩

end


end D5.X_Frontier.BasePhiNegativePrefixTrident
