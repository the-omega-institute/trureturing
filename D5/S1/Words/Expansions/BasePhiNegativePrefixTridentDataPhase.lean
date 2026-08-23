/- GID: D5/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Correct the six-state frontier projection using exact core-gap data. -/

import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentEdge

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Digit

noncomputable section

/-- Exact core-gap scans retain all six recursive states but emit family `G`
only from state `G1e`; every other state emits family `F`. -/
def dataFrontierFamily : FrontierPhase → GapFamily
  | .G1e => .G
  | .F0o | .F1o | .F0e | .G0o | .H0e => .F

/-- The corrected selector obtained by projecting a prefix-machine state to
the core-gap family observed by the exact scanner. -/
noncomputable def dataFrontierGapSelector
    (certificate : FrontierReturnWord) (n : Nat) : Int :=
  if familyLetter (dataFrontierFamily certificate.phase) n then
    certificate.a
  else
    certificate.b

def DataFrontierGapPhase (certificate : FrontierReturnWord) : Prop :=
  ∀ n : Nat, certificate.gap n = dataFrontierGapSelector certificate n

/-- Executable base certificates for the declarative prefix machine. -/
def dataStartCertificate : Bool → FrontierPhaseCertificate
  | false => ⟨.F0o, 4, 3⟩
  | true => ⟨.F1o, 7, 4⟩

/-- Executable form of the ten admissible transitions. The two repeated-one
branches are totality cases and are unreachable for admissible prefixes. -/
def dataNextCertificate : FrontierPhaseCertificate → Bool →
    FrontierPhaseCertificate
  | ⟨.F0o, a, b⟩, false => ⟨.F0e, a + b, a⟩
  | ⟨.F0o, a, b⟩, true => ⟨.G1e, 2 * a + b, a + b⟩
  | ⟨.F1o, a, b⟩, false => ⟨.F0e, a, b⟩
  | ⟨.F1o, a, b⟩, true => ⟨.F1o, a, b⟩
  | ⟨.F0e, a, b⟩, false => ⟨.F0o, a + b, a⟩
  | ⟨.F0e, a, b⟩, true => ⟨.F1o, 2 * a + b, a + b⟩
  | ⟨.G1e, a, b⟩, false => ⟨.G0o, a, b⟩
  | ⟨.G1e, a, b⟩, true => ⟨.G1e, a, b⟩
  | ⟨.G0o, a, b⟩, false => ⟨.H0e, a + b, a⟩
  | ⟨.G0o, a, b⟩, true => ⟨.G1e, 2 * a + b, a + b⟩
  | ⟨.H0e, a, b⟩, false => ⟨.G0o, a + b, a⟩
  | ⟨.H0e, a, b⟩, true => ⟨.F1o, 2 * a + b, a + b⟩

def dataPhaseCertificate? : List Bool → Option FrontierPhaseCertificate
  | [] => none
  | bit :: tail =>
      some (tail.foldl dataNextCertificate (dataStartCertificate bit))

theorem data_transition_evaluates
    {before after : FrontierPhaseCertificate} {bit : Bool}
    (h : FrontierPhaseTransition before bit after) :
    dataNextCertificate before bit = after := by
  cases h <;> rfl

theorem data_phase_machine_nonempty {w : List Bool}
    {certificate : FrontierPhaseCertificate}
    (h : PrefixPhaseMachineFor w certificate) : w ≠ [] := by
  induction h <;> simp_all

theorem data_phase_append_singleton {w : List Bool} (hw : w ≠ [])
    (bit : Bool) :
    dataPhaseCertificate? (w ++ [bit]) =
      (dataPhaseCertificate? w).map fun certificate =>
        dataNextCertificate certificate bit := by
  cases w with
  | nil => contradiction
  | cons head tail =>
      simp [dataPhaseCertificate?, List.foldl_append]

/-- The executable certificate evaluator is sound for every derivation of the
declarative prefix machine. -/
theorem data_phase_machine_evaluates {w : List Bool}
    {certificate : FrontierPhaseCertificate}
    (h : PrefixPhaseMachineFor w certificate) :
    dataPhaseCertificate? w = some certificate := by
  induction h with
  | zero => rfl
  | one => rfl
  | step hprefix transition ih =>
      rw [data_phase_append_singleton (data_phase_machine_nonempty hprefix)]
      rw [ih]
      simp [data_transition_evaluates transition]

theorem data_phase_machine_010_eq {certificate : FrontierPhaseCertificate}
    (h : PrefixPhaseMachineFor [false, true, false] certificate) :
    certificate = ⟨.G0o, 11, 7⟩ := by
  have heval := data_phase_machine_evaluates h
  have : some (⟨.G0o, 11, 7⟩ : FrontierPhaseCertificate) =
      some certificate := by
    simpa [dataPhaseCertificate?, dataStartCertificate,
      dataNextCertificate] using heval
  exact (Option.some.inj this).symm

private theorem fibonacci_gap_letter_zero : fibonacciGapLetter 0 = true := by
  have hsquare : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hslowTwo : 2 ≤ Real.sqrt 5 := by nlinarith
  have hshighThree : Real.sqrt 5 < 3 := by nlinarith
  have hfloorOne : ⌊Real.goldenRatio⌋ = (1 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> simp [Real.goldenRatio] <;> nlinarith
  have hfloorTwo : ⌊2 * Real.goldenRatio⌋ = (3 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> simp [Real.goldenRatio] <;> nlinarith
  norm_num [fibonacciGapLetter, hfloorOne, hfloorTwo]

/-- Direct regression for the counterexample that invalidated the old
projection: the corrected selector chooses the observed first gap `11`. -/
theorem dataFrontierGapSelector_prefix010_zero
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor [false, true, false] certificate) :
    dataFrontierGapSelector certificate 0 = 11 := by
  have hphase := data_phase_machine_010_eq hcertificate.phase_machine
  simp [dataFrontierGapSelector, FrontierReturnWord.phase,
    FrontierReturnWord.a, hphase,
    dataFrontierFamily, familyLetter, fibonacci_gap_letter_zero]

theorem dataFrontierGapPhase_prefix010_zero
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor [false, true, false] certificate)
    (hphase : DataFrontierGapPhase certificate) :
    certificate.gap 0 = 11 := by
  rw [hphase 0]
  exact dataFrontierGapSelector_prefix010_zero hcertificate

/-- Integer weight accumulated by the deterministic carry/skip run between
two input indices. -/
def carryRunWeight (expansion : BasePhiNegativeExpansion) (q r : Nat) : Int :=
  (rawValue (carrySkipRun expansion r).positive : Int) -
    rawValue (carrySkipRun expansion q).positive

/-- One carry/skip microstep adds its input token and the current skip event. -/
theorem carry_local_weight_identity (expansion : BasePhiNegativeExpansion)
    {before after : CarrySkipState}
    (htransition : CarrySkipTransition expansion before after) :
    (rawValue after.positive : Int) - rawValue before.positive =
      1 + negativeOneEvent expansion before.input := by
  rw [CarrySkipTransition] at htransition
  subst after
  change (rawValue (carrySkipStep expansion before.input before.positive) : Int) -
      rawValue before.positive = 1 + negativeOneEvent expansion before.input
  rw [rawValue_carrySkipStep]
  push_cast
  ring

/-- The run weight is a cocycle under subdivision of the input interval. -/
theorem carry_run_weight_cocycle (expansion : BasePhiNegativeExpansion)
    (p q r : Nat) :
    carryRunWeight expansion p r =
      carryRunWeight expansion p q + carryRunWeight expansion q r := by
  simp only [carryRunWeight]
  ring

/-- Telescoping the local identity leaves the input displacement and the exact
change in the negative-one event counter. -/
theorem carry_run_weight_telescope (expansion : BasePhiNegativeExpansion)
    (q r : Nat) :
    carryRunWeight expansion q r =
      (r : Int) - q +
        ((negativeOneCount expansion r : Nat) : Int) -
          negativeOneCount expansion q := by
  have hq := (carrySkipRun_invariant expansion q).2.2
  have hr := (carrySkipRun_invariant expansion r).2.2
  rw [carrySkipRun_input, carrySkipRun_skips] at hq hr
  simp only [carryRunWeight]
  rw [hq, hr]
  omega

/-- Frontier specialization of the telescope. The remaining counter delta is
the semantic quantity that a global Core-gap recurrence must identify. -/
theorem frontier_run_weight_telescope (certificate : FrontierReturnWord)
    (n : Nat) :
    carryRunWeight canonicalExpansion (certificate.enumerate n)
        (certificate.enumerate (n + 1)) =
      certificate.gap n +
        ((negativeOneCount canonicalExpansion
            (certificate.enumerate (n + 1)) : Nat) : Int) -
          negativeOneCount canonicalExpansion (certificate.enumerate n) := by
  rw [carry_run_weight_telescope]
  simp only [FrontierReturnWord.gap]

/-- A carry-reachable frontier step labeled by the corrected data family. -/
structure DataPhaseLabeledReachability (certificate : FrontierReturnWord)
    (n : Nat) where
  phase : FrontierPhase
  letter : Bool
  phase_eq : phase = certificate.phase
  letter_eq : letter =
    familyLetter (dataFrontierFamily certificate.phase) n
  reachable : FrontierRunStep certificate n

def dataPhaseLabeledReachability {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) (n : Nat) :
    DataPhaseLabeledReachability certificate n :=
  { phase := certificate.phase
    letter := familyLetter (dataFrontierFamily certificate.phase) n
    phase_eq := rfl
    letter_eq := rfl
    reachable := hcertificate.run_step n }

structure DataPhaseEnrichedCoreEdge (w : List Bool)
    (certificate : FrontierReturnWord) (n : Nat) where
  target : Nat
  labeled : DataPhaseLabeledReachability certificate n
  adjacent : AdjacentCorePoint w (certificate.enumerate n) target
  additive : (target : Int) = certificate.enumerate n +
    dataFrontierGapSelector certificate n

def DataPhaseEnrichedCoreTrace (w : List Bool)
    (certificate : FrontierReturnWord) : Prop :=
  ∀ n : Nat, Nonempty (DataPhaseEnrichedCoreEdge w certificate n)

theorem data_phase_enriched_core_trace_gap_additive {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : DataPhaseEnrichedCoreTrace w certificate) :
    ∀ n : Nat, (certificate.enumerate (n + 1) : Int) =
      certificate.enumerate n + dataFrontierGapSelector certificate n := by
  intro n
  obtain ⟨edge⟩ := htrace n
  have htarget := adjacent_core_point_eq_frontier_successor
    hcertificate edge.adjacent
  rw [← htarget]
  exact edge.additive

theorem data_phase_enriched_core_trace_two_gap_additive {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : DataPhaseEnrichedCoreTrace w certificate) :
    ∀ n : Nat,
      (certificate.enumerate (n + 1) : Int) =
          certificate.enumerate n + certificate.a ∨
        (certificate.enumerate (n + 1) : Int) =
          certificate.enumerate n + certificate.b := by
  intro n
  have hgap := data_phase_enriched_core_trace_gap_additive
    hcertificate htrace n
  cases hletter : familyLetter (dataFrontierFamily certificate.phase) n
  · right
    simpa [dataFrontierGapSelector, hletter] using hgap
  · left
    simpa [dataFrontierGapSelector, hletter] using hgap

theorem data_phase_enriched_core_trace_gap_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : DataPhaseEnrichedCoreTrace w certificate) :
    DataFrontierGapPhase certificate := by
  intro n
  have hgap := data_phase_enriched_core_trace_gap_additive
    hcertificate htrace n
  simp only [FrontierReturnWord.gap]
  omega

theorem data_phase_enriched_core_trace_of_gap_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hphase : DataFrontierGapPhase certificate) :
    DataPhaseEnrichedCoreTrace w certificate := by
  intro n
  refine ⟨{
    target := certificate.enumerate (n + 1)
    labeled := dataPhaseLabeledReachability hcertificate n
    adjacent := frontier_consecutive_core_adjacent hcertificate n
    additive := ?_ }⟩
  have hgap := hphase n
  simp only [FrontierReturnWord.gap] at hgap
  exact sub_eq_iff_eq_add'.mp hgap

theorem data_phase_enriched_core_trace_iff_gap_phase {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    DataPhaseEnrichedCoreTrace w certificate ↔
      DataFrontierGapPhase certificate :=
  ⟨data_phase_enriched_core_trace_gap_phase hcertificate,
    data_phase_enriched_core_trace_of_gap_phase hcertificate⟩

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
