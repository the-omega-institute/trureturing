/- GID: D5/X_Frontier/BasePhiNegativePrefixTrident
   generality: I
   mirror-B: none(waiver:negative-base-phi-frontier)
   mirror-E: D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json
   anchors: []
   digest: Classify admissible negative base-phi prefix occurrence sets by Lucas-gap trident families. -/

import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentPhaseObstruction
import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentDataPhase

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Scale

noncomputable section

/- The canonical core enumeration is defined from `Core` itself.  In
particular, it does not recover the core set from a conjectural gap stream. -/
noncomputable def canonicalCoreEnum (w : List Bool) : Nat → Nat :=
  Nat.nth fun q => q ∈ Core w

theorem carrySkipRun_reflTransGen (expansion : BasePhiNegativeExpansion)
    {m n : Nat} (hmn : m ≤ n) :
    Relation.ReflTransGen (CarrySkipTransition expansion)
      (carrySkipRun expansion m) (carrySkipRun expansion n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => exact .refl
  | succ k ih =>
      apply Relation.ReflTransGen.tail ih
      change carrySkipRun expansion (m + k + 1) =
        nextState expansion (carrySkipRun expansion (m + k))
      rw [carrySkipRun_succ]

/- This is the exact reduction available from the present return-word
interface.  The remaining mathematical obligation is infinitude of the
canonical core; no phase coherence is manufactured by choice. -/
theorem frontier_step_semantics_of_core_infinite
    {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    (hphase : prefix_phase_machine_total hw hadmissible)
    (hcore : (Core w).Infinite) :
    frontier_step_semantics hw hadmissible hfibers hlift hphase := by
  obtain ⟨phaseCertificate, hphaseMachine, _⟩ := hphase
  let certificate : FrontierReturnWord :=
    { phaseCertificate := phaseCertificate
      boundary := carrySkipRun canonicalExpansion (canonicalCoreEnum w 0)
      enumerate := canonicalCoreEnum w }
  refine ⟨certificate, ?_⟩
  refine
    { phase_machine := hphaseMachine
      boundary_eq := rfl
      range_eq := ?_
      successor_strict := ?_
      run_step := ?_ }
  · exact Nat.range_nth_of_infinite hcore
  · exact fun n => Nat.nth_strictMono hcore (Nat.lt_succ_self n)
  · intro n
    apply carrySkipRun_reflTransGen
    exact Nat.le_of_lt (Nat.nth_strictMono hcore (Nat.lt_succ_self n))

theorem core_infinite_of_frontier_step_semantics
    {w : List Bool} {hw : w ≠ []}
    {hadmissible : AdmissibleNegativePrefix canonicalExpansion w}
    {hfibers : negative_tail_fiber_shape hw hadmissible}
    {hlift : core_occurrence_unique_lift hw hadmissible hfibers}
    {hphase : prefix_phase_machine_total hw hadmissible}
    (hfrontier : frontier_step_semantics hw hadmissible hfibers hlift hphase) :
    (Core w).Infinite := by
  obtain ⟨certificate, hcertificate⟩ := hfrontier
  rw [← hcertificate.range_eq]
  exact Set.infinite_range_of_injective
    (strictMono_nat_of_lt_succ hcertificate.successor_strict).injective

theorem frontier_step_semantics_iff_core_infinite
    {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    (hphase : prefix_phase_machine_total hw hadmissible) :
    frontier_step_semantics hw hadmissible hfibers hlift hphase ↔
      (Core w).Infinite :=
  ⟨core_infinite_of_frontier_step_semantics,
    frontier_step_semantics_of_core_infinite hw hadmissible hfibers hlift hphase⟩

theorem frontier_step_semantics_proved
    {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    (hphase : prefix_phase_machine_total hw hadmissible) :
    frontier_step_semantics hw hadmissible hfibers hlift hphase :=
  frontier_step_semantics_of_core_infinite hw hadmissible hfibers hlift hphase
    (core_infinite_proved hw hadmissible hfibers hlift)

def coreEnum (certificate : FrontierReturnWord) (n : Nat) : Int :=
  certificate.enumerate n

theorem core_enum_from_frontier {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    (∀ n : Nat,
      CarrySkipInvariant canonicalExpansion (frontierState certificate n)) ∧
      ∀ n : Nat, 0 < certificate.enumerate n := by
  constructor
  · intro n
    exact carrySkipRun_invariant canonicalExpansion (certificate.enumerate n)
  · intro n
    have hcore : certificate.enumerate n ∈ Core w := by
      rw [← hcertificate.range_eq]
      exact ⟨n, rfl⟩
    exact hcore.1.1.1

theorem core_enum_sound_complete {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    Set.range certificate.enumerate = Core w ∧
      Function.Injective certificate.enumerate :=
  ⟨hcertificate.range_eq,
    (strictMono_nat_of_lt_succ hcertificate.successor_strict).injective⟩

def source_index_successor_delta {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hraw : (∀ n : Nat,
      CarrySkipInvariant canonicalExpansion (frontierState certificate n)) ∧
      ∀ n : Nat, 0 < certificate.enumerate n) : Prop :=
  ∀ n : Nat,
    (certificate.gap n = certificate.a ∨ certificate.gap n = certificate.b) ∧
      FrontierRunStep certificate n

/- Additive successor equations are the arithmetic form needed before the
final subtraction defining `gap`; they avoid any use of truncated Nat
subtraction. -/
def sourceIndexSuccessorAdditive (certificate : FrontierReturnWord) : Prop :=
  ∀ n : Nat,
    (certificate.enumerate (n + 1) : Int) =
        certificate.enumerate n + certificate.a ∨
      (certificate.enumerate (n + 1) : Int) =
        certificate.enumerate n + certificate.b

theorem source_index_successor_delta_of_additive
    {w : List Bool} {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hraw : (∀ n : Nat,
      CarrySkipInvariant canonicalExpansion (frontierState certificate n)) ∧
      ∀ n : Nat, 0 < certificate.enumerate n)
    (hadditive : sourceIndexSuccessorAdditive certificate) :
    source_index_successor_delta hcertificate hraw := by
  intro n
  refine ⟨?_, hcertificate.run_step n⟩
  rcases hadditive n with ha | hb
  · left
    simp only [FrontierReturnWord.gap]
    omega
  · right
    simp only [FrontierReturnWord.gap]
    omega

theorem source_index_successor_additive_of_delta
    {w : List Bool} {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hraw : (∀ n : Nat,
      CarrySkipInvariant canonicalExpansion (frontierState certificate n)) ∧
      ∀ n : Nat, 0 < certificate.enumerate n)
    (hdelta : source_index_successor_delta hcertificate hraw) :
    sourceIndexSuccessorAdditive certificate := by
  intro n
  rcases (hdelta n).1 with ha | hb
  · left
    simp only [FrontierReturnWord.gap] at ha
    omega
  · right
    simp only [FrontierReturnWord.gap] at hb
    omega

theorem source_index_successor_delta_iff_additive
    {w : List Bool} {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hraw : (∀ n : Nat,
      CarrySkipInvariant canonicalExpansion (frontierState certificate n)) ∧
      ∀ n : Nat, 0 < certificate.enumerate n) :
    source_index_successor_delta hcertificate hraw ↔
      sourceIndexSuccessorAdditive certificate :=
  ⟨source_index_successor_additive_of_delta hcertificate hraw,
    source_index_successor_delta_of_additive hcertificate hraw⟩

theorem source_index_successor_delta_of_data_phase_enriched_trace
    {w : List Bool} {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : DataPhaseEnrichedCoreTrace w certificate) :
    source_index_successor_delta hcertificate
      (core_enum_from_frontier hcertificate) := by
  apply source_index_successor_delta_of_additive hcertificate
    (core_enum_from_frontier hcertificate)
  exact data_phase_enriched_core_trace_two_gap_additive hcertificate htrace

def data_phase_gap_stream {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hdelta : source_index_successor_delta hcertificate
      (core_enum_from_frontier hcertificate)) : Prop :=
  DataFrontierGapPhase certificate

theorem data_phase_gap_stream_of_enriched_trace
    {w : List Bool} {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (htrace : DataPhaseEnrichedCoreTrace w certificate) :
    data_phase_gap_stream hcertificate
      (source_index_successor_delta_of_data_phase_enriched_trace
        hcertificate htrace) :=
  data_phase_enriched_core_trace_gap_phase hcertificate htrace

/- The existing target gap word is not periodic modulo six.  Consequently a
fixed `n % 6` phase table cannot supply `FrontierGapPhase`; any finite-state
proof must retain the aperiodic Fibonacci input letter. -/
theorem fibonacci_gap_letter_not_six_periodic :
    ¬ ∀ n : Nat, fibonacciGapLetter (n + 6) = fibonacciGapLetter n := by
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hslowTwo : 2 ≤ Real.sqrt 5 := by nlinarith
  have hslowFifteen : (15 : Real) / 7 ≤ Real.sqrt 5 := by nlinarith
  have hshighNine : Real.sqrt 5 < (9 : Real) / 4 := by nlinarith
  have hshighThree : Real.sqrt 5 < 3 := by nlinarith
  have hfloorOne : ⌊Real.goldenRatio⌋ = (1 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> simp [Real.goldenRatio] <;> nlinarith
  have hfloorTwo : ⌊2 * Real.goldenRatio⌋ = (3 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> simp [Real.goldenRatio] <;> nlinarith
  have hfloorSeven : ⌊7 * Real.goldenRatio⌋ = (11 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> simp [Real.goldenRatio] <;> nlinarith
  have hfloorEight : ⌊8 * Real.goldenRatio⌋ = (12 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> simp [Real.goldenRatio] <;> nlinarith
  intro hperiodic
  have hzero := hperiodic 0
  norm_num [fibonacciGapLetter, hfloorOne, hfloorTwo,
    hfloorSeven, hfloorEight] at hzero

theorem core_enum_strictMono {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    StrictMono certificate.enumerate :=
  strictMono_nat_of_lt_succ hcertificate.successor_strict

theorem sequence_eq_v_of_head_and_gaps {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hdelta : source_index_successor_delta hcertificate
      (core_enum_from_frontier hcertificate))
    (hstream : data_phase_gap_stream hcertificate hdelta) :
    coreEnum certificate =
      vForFamily (dataFrontierFamily certificate.phase)
        certificate.a certificate.b certificate.first := by
  funext n
  induction n with
  | zero =>
      cases dataFrontierFamily certificate.phase <;>
        rfl
  | succ n ih =>
      have hgap := hstream n
      change coreEnum certificate (n + 1) - coreEnum certificate n =
        dataFrontierGapSelector certificate n at hgap
      simp only [dataFrontierGapSelector] at hgap
      cases family : dataFrontierFamily certificate.phase <;>
        simp only [family, vForFamily, vF, vG, vH, gapSequence] at ih hgap ⊢ <;>
        rw [← ih] <;>
        omega

theorem core_lucas_gap_classification {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hlucas : lucas_pair_closed_under_growth hcertificate)
    (hraw : (∀ n : Nat,
      CarrySkipInvariant canonicalExpansion (frontierState certificate n)) ∧
      ∀ n : Nat, 0 < certificate.enumerate n)
    (hsound : Set.range certificate.enumerate = Core w ∧
      Function.Injective certificate.enumerate)
    (hsequence : coreEnum certificate =
      vForFamily (dataFrontierFamily certificate.phase)
        certificate.a certificate.b certificate.first) :
    CoreLucasWitness w := by
  refine ⟨dataFrontierFamily certificate.phase, certificate.a, certificate.b,
    certificate.first, hlucas.1, ?_, ?_⟩
  · change (0 : Int) < (certificate.enumerate 0 : Int)
    exact_mod_cast hraw.2 0
  · rw [← hsound.1]
    ext N
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, congrFun hsequence n⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hcast : (certificate.enumerate n : Int) = (N : Int) :=
        (congrFun hsequence n).trans hn.symm
      exact_mod_cast hcast

def v_translate_initial_value (family : GapFamily) (a b r : Int) : Prop :=
  ∀ j : Nat,
    (fun n => vForFamily family a b r n + (j : Int)) =
      vForFamily family a b (r + (j : Int))

theorem v_translate_initial_value_proved (family : GapFamily) (a b r : Int) :
    v_translate_initial_value family a b r := by
  intro j
  funext n
  cases family <;> induction n with
  | zero => rfl
  | succ n ih =>
      simp only [vForFamily, vF, vG, vH, gapSequence] at ih ⊢
      rw [← ih]
      ring

def three_arms_pairwise_disjoint {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r) : Prop :=
  w.head? = some false →
    ∀ i j : Fin 3, i ≠ j →
      Disjoint
        (sequenceRange (vForFamily family a b (r + (i.1 : Int))))
        (sequenceRange (vForFamily family a b (r + (j.1 : Int))))

def occurrenceSet_lucas_gap_classification {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hdisjoint : three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate) : Prop :=
  ∃ (family : GapFamily) (a b r : Int),
      LucasPair a b ∧ 0 < r ∧
      if w.head? = some true then
        occurrenceSet canonicalExpansion w =
          sequenceRange (vForFamily family a b r)
      else
        occurrenceSet canonicalExpansion w =
          ⋃ j : Fin 3,
            sequenceRange (vForFamily family a b (r + (j.1 : Int)))

private theorem LucasPair.parameters {a b : Int} (h : LucasPair a b) :
    lucasParameter a ∧ lucasParameter b := by
  obtain ⟨k, _, ha, hb⟩ := h
  exact ⟨⟨k + 1, ha⟩, ⟨k, hb⟩⟩

private theorem vForFamily_pos {family : GapFamily} {a b r : Int}
    (hpair : LucasPair a b) (hr : 0 < r) (n : Nat) :
    0 < vForFamily family a b r n := by
  have hparameters := hpair.parameters
  have ha := lucas_parameter_pos hparameters.1
  have hb := lucas_parameter_pos hparameters.2
  have hmono : StrictMono (vForFamily family a b r) := by
    cases family <;> exact gap_sequence_strict_mono _ ha hb
  cases n with
  | zero => cases family <;> exact hr
  | succ n =>
      have hfirst := hmono (Nat.zero_lt_succ n)
      cases family <;> simpa [vForFamily, vF, vG, vH, gapSequence] using
        lt_trans hr hfirst

private theorem prefix_head_false {w : List Bool} (hw : w ≠ [])
    (hhead : w.head? = some false) {q : Nat}
    (hq : q ∈ Core w) :
    negativeDigit canonicalExpansion q 0 = false := by
  cases w with
  | nil => contradiction
  | cons bit tail =>
      have hzero := hq.2.2 ⟨0, by simp⟩
      simpa using hzero.trans (show bit = false by simpa using hhead)

private theorem core_shift_occurs_of_head_false {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hhead : w.head? = some false) {q j : Nat}
    (hq : q ∈ Core w) (hj : j < 3) :
    q + j ∈ occurrenceSet canonicalExpansion w := by
  have hqOccurrence : q ∈ occurrenceSet canonicalExpansion w :=
    ⟨hq.1.1.1, hq.2⟩
  obtain ⟨s, hs, _⟩ :=
    (hfibers q hqOccurrence).2 (prefix_head_false hw hhead hq)
  have hsMem : s ∈ negativeTailFiber q := by
    rw [hs.2.2]
    simp
  have hsEq : s = q := by
    have hqs := hq.1.2 s hsMem
    omega
  have hshiftMem : q + j ∈ negativeTailFiber q := by
    rw [hs.2.2, hsEq]
    change q + j = q ∨ q + j = q + 1 ∨ q + j = q + 2
    omega
  exact ⟨hshiftMem.1, prefix_occurs_of_same_tail hshiftMem.2 hq.2⟩

private theorem shifted_sequence_lift {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hhead : w.head? = some false) {i : Fin 3} {N : Nat}
    (hN : N ∈ sequenceRange
      (vForFamily family a b (r + (i.1 : Int)))) :
    ∃ q : Nat, q ∈ Core w ∧ N = q + i.1 ∧
      N ∈ occurrenceSet canonicalExpansion w := by
  obtain ⟨n, hn⟩ := hN
  have hbasePos := vForFamily_pos (family := family) hcore.1 hcore.2.1 n
  let q := (vForFamily family a b r n).toNat
  have hqCast : (q : Int) = vForFamily family a b r n := by
    exact Int.toNat_of_nonneg hbasePos.le
  have hNInt : (N : Int) = (q : Int) + (i.1 : Int) := by
    rw [hqCast]
    exact hn.trans (congrFun (htranslate i.1) n).symm
  have hNq : N = q + i.1 := by exact_mod_cast hNInt
  have hqCore : q ∈ Core w := by
    rw [hcore.2.2]
    exact ⟨n, hqCast⟩
  refine ⟨q, hqCore, hNq, ?_⟩
  rw [hNq]
  exact core_shift_occurs_of_head_false hw hadmissible hfibers hhead
    hqCore i.2

theorem three_arms_pairwise_disjoint_proved {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r) :
    three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate := by
  intro hhead i j hij
  rw [Set.disjoint_left]
  intro N hNi hNj
  rcases shifted_sequence_lift hw hadmissible hfibers hcore htranslate hhead hNi with
    ⟨qi, hqiCore, hNqi, hNiOccurrence⟩
  rcases shifted_sequence_lift hw hadmissible hfibers hcore htranslate hhead hNj with
    ⟨qj, hqjCore, hNqj, _hNjOccurrence⟩
  have hiBound : i.1 < prefixMultiplicity w := by
    simp [prefixMultiplicity, hhead, i.2]
  have hjBound : j.1 < prefixMultiplicity w := by
    simp [prefixMultiplicity, hhead, j.2]
  obtain ⟨qk, _hqk, hunique⟩ := hlift N hNiOccurrence
  have hiEq : (qi, i.1) = qk := hunique (qi, i.1) ⟨hqiCore, hiBound, hNqi⟩
  have hjEq : (qj, j.1) = qk := hunique (qj, j.1) ⟨hqjCore, hjBound, hNqj⟩
  apply hij
  apply Fin.ext
  exact congrArg Prod.snd (hiEq.trans hjEq.symm)

theorem occurrenceSet_lucas_gap_classification_proved {w : List Bool}
    (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    {family : GapFamily} {a b r : Int}
    (hcore : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r))
    (htranslate : v_translate_initial_value family a b r)
    (hdisjoint : three_arms_pairwise_disjoint hw hadmissible hfibers hlift
      hcore htranslate) :
    occurrenceSet_lucas_gap_classification hw hadmissible hfibers hlift
      hcore htranslate hdisjoint := by
  classical
  refine ⟨family, a, b, r, hcore.1, hcore.2.1, ?_⟩
  split_ifs with hhead
  · ext N
    constructor
    · intro hN
      obtain ⟨qj, hqj, _hunique⟩ := hlift N hN
      have hjZero : qj.2 = 0 := by
        have := hqj.2.1
        simp [prefixMultiplicity, hhead] at this
        omega
      have hqN : qj.1 = N := by omega
      rw [← hcore.2.2]
      simpa [hqN] using hqj.1
    · intro hN
      rw [← hcore.2.2] at hN
      exact ⟨hN.1.1.1, hN.2⟩
  · have hheadFalse : w.head? = some false := by
      cases w with
      | nil => contradiction
      | cons bit tail =>
          cases bit <;> simp_all
    ext N
    constructor
    · intro hN
      obtain ⟨qj, hqj, _hunique⟩ := hlift N hN
      have hjBound : qj.2 < 3 := by
        simpa [prefixMultiplicity, hheadFalse] using hqj.2.1
      let j : Fin 3 := ⟨qj.2, hjBound⟩
      rw [Set.mem_iUnion]
      refine ⟨j, ?_⟩
      rw [sequenceRange]
      rw [hcore.2.2] at hqj
      obtain ⟨n, hn⟩ := hqj.1
      refine ⟨n, ?_⟩
      rw [← congrFun (htranslate j.1) n, ← hn]
      exact_mod_cast hqj.2.2
    · rw [Set.mem_iUnion]
      rintro ⟨j, hNj⟩
      rcases shifted_sequence_lift hw hadmissible hfibers hcore htranslate
        hheadFalse hNj with ⟨q, hqCore, hNq, hNOccurrence⟩
      exact hNOccurrence

/-- Whole-chain elaboration check.  Each open provider consumes only frozen
interfaces or conclusions produced earlier in the fifteen-node chain. -/
theorem classification_chain_signatures_consistent
    {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    (hphase : prefix_phase_machine_total hw hadmissible)
    (hfrontier : frontier_step_semantics hw hadmissible hfibers hlift hphase)
    (hlucas : ∀ {certificate : FrontierReturnWord},
      (hcertificate : FrontierReturnWordFor w certificate) →
        lucas_pair_closed_under_growth hcertificate)
    (hdelta : ∀ {certificate : FrontierReturnWord},
      (hcertificate : FrontierReturnWordFor w certificate) →
      source_index_successor_delta hcertificate
        (core_enum_from_frontier hcertificate))
    (hstream : ∀ {certificate : FrontierReturnWord},
      (hcertificate : FrontierReturnWordFor w certificate) →
      (delta : source_index_successor_delta hcertificate
        (core_enum_from_frontier hcertificate)) →
      data_phase_gap_stream hcertificate delta)
    (harms : ∀ {family : GapFamily} {a b r : Int},
      (hcore : LucasPair a b ∧ 0 < r ∧
        Core w = sequenceRange (vForFamily family a b r)) →
      (htranslate : v_translate_initial_value family a b r) →
      three_arms_pairwise_disjoint hw hadmissible hfibers hlift hcore htranslate)
    (hfinal : ∀ {family : GapFamily} {a b r : Int},
      (hcore : LucasPair a b ∧ 0 < r ∧
        Core w = sequenceRange (vForFamily family a b r)) →
      (htranslate : v_translate_initial_value family a b r) →
      (hdisjoint : three_arms_pairwise_disjoint hw hadmissible hfibers hlift
        hcore htranslate) →
      occurrenceSet_lucas_gap_classification hw hadmissible hfibers hlift
        hcore htranslate hdisjoint) :
    ∃ (family : GapFamily) (a b r : Int),
      LucasPair a b ∧ 0 < r ∧
      if w.head? = some true then
        occurrenceSet canonicalExpansion w =
          sequenceRange (vForFamily family a b r)
      else
        occurrenceSet canonicalExpansion w =
          ⋃ j : Fin 3,
            sequenceRange (vForFamily family a b (r + (j.1 : Int))) := by
  rcases hfrontier with ⟨certificate, hcertificate⟩
  have hraw := core_enum_from_frontier hcertificate
  have hsound := core_enum_sound_complete hcertificate
  have hdelta' := hdelta hcertificate
  have hstream' := hstream hcertificate hdelta'
  have hsequence := sequence_eq_v_of_head_and_gaps hcertificate hdelta' hstream'
  have hcoreWitness := core_lucas_gap_classification hcertificate
    (hlucas hcertificate) hraw hsound hsequence
  rcases hcoreWitness with ⟨family, a, b, r, hpair, hpositive, hcore⟩
  have htranslate := v_translate_initial_value_proved family a b r
  have hcoreData : LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r) :=
    ⟨hpair, hpositive, hcore⟩
  have hdisjoint := harms hcoreData htranslate
  have hclassified := hfinal hcoreData htranslate hdisjoint
  simpa [occurrenceSet_lucas_gap_classification] using hclassified

/-!
The source question asks for an exact classification of occurrence sequences
for finite negative-position prefix cylinders in the two-sided base-phi
expansion. The finite scan is evidence only; it is not a proof of this
classification.

## Interface correction record (2026-08-21)

The fifteen chain signatures below were corrected one by one. Return words now
derive `first` and `gap` from the enumerator, bind their phase certificate to
`PrefixPhaseMachineFor`, bind the boundary to `carrySkipRun`, and require the
actual `CarrySkipTransition` paths. Thus the phase/return-word interface cannot
silently replace the values consumed by later nodes.

1. `negative_tail_fiber_shape`: takes the nonempty prefix and admissibility
   hypotheses and records the singleton/three-point fiber consequence of
   the singleton/trident fiber shape (paper: Dekking 7.1/7.5; proved here directly).
2. `core_occurrence_unique_lift`: consumes the fiber-shape conclusion.
3. `prefix_phase_machine_total`: exposes a unique phase certificate generated
   by the ten-rule prefix machine.
4. `frontier_step_semantics`: consumes the preceding fiber, lift, and phase
   interfaces and produces a bound `FrontierReturnWord`.
5. `lucas_pair_closed_under_growth`: consumes the bound return word and states
   the Lucas-pair/growth invariant.
6. `core_enum_from_frontier`: derives carry invariants and positivity from the
   actual enumerator; this node is directly proved.
7. `core_enum_sound_complete`: derives range equality and injectivity; directly
   proved from the return-word fields.
8. `source_index_successor_delta`: requires each enumerator gap to be one of
   the certificate pair and each successor to follow the frozen carry path.
9. `data_phase_gap_stream`: states the corrected data-derived phase gap stream
   from that delta.
10. `core_enum_strictMono`: derives global strict monotonicity from the return
    word's successor-step order; directly proved.
11. `sequence_eq_v_of_head_and_gaps`: reconstructs the family sequence from
    the derived head and gaps; directly proved.
12. `core_lucas_gap_classification`: translates that sequence and Lucas data to
    `CoreLucasWitness`; directly proved.
13. `v_translate_initial_value`: is directly proved by induction for all three
    families (`v_translate_initial_value_proved`).
14. `three_arms_pairwise_disjoint`: consumes the corrected lift and translation
    interfaces.
15. `occurrenceSet_lucas_gap_classification`: consumes the three-arm result and
    states the final one-arm/three-arm classification.

Five inconsistencies were found and repaired while aligning the record.
First, the old file exposed only seven compressed `Prop` obligations even
though the surrounding reconnaissance prose described fifteen typed chain
nodes; the chain is now fifteen separately typed, composable interfaces.
Second, `carrySkipStep` and its state machine are not in
`BasePhiNegativeBridge.lean`; the frozen definitions are in
`BasePhiCarryTransducer.lean`, which is now the import and source used by this
file. Third, a constructor binder used a reserved Lean syntax prefix and is
renamed to `hprefix`. Fourth, the derived first value did not elaborate
directly through `exact_mod_cast`; an explicit target change precedes it now.
Fifth, SL-028 reported `FrontierReturnWordFor.strictMono` as a duplicate of
`core_enum_strictMono`; the proof now stores the successor-step strict order
and derives the global `StrictMono` via `strictMono_nat_of_lt_succ`, and the
final admission carries no SL-028 observation.

Per-theorem quality account of the seven discharged nodes (review-graded, not
flattened): `core_enum_from_frontier` and `sequence_eq_v_of_head_and_gaps` are
interface-alignment gains (the former ties `frontierState` to `carrySkipRun`
through `carrySkipRun_invariant`; the latter derives `first`/`gap` from
`enumerate`, repairing the independent-field mismatch and enabling the closing
induction). `core_lucas_gap_classification` is an alignment-dependent
set/range transport, not a new semantic classification.
`core_enum_sound_complete` and `core_enum_strictMono` are trivial projections
of `successor_strict`. `v_translate_initial_value_proved` is an independent
routine induction. `classification_chain_signatures_consistent` is chain
plumbing: kernel-checked type compatibility, not semantic closure.

The first node's fiber-shape dependency is now discharged by
`D5.S1.Words.Expansions.BasePhiTailFiber.negative_tail_fiber_shape`, proved
directly via Beatty floor coordinates (the paper's Theorem 7.5 recursion
itself remains unformalized and unclaimed). No new non-`X_Frontier` `sorry`
was introduced; the final theorem below remains the sole frontier placeholder.

## Closed supporting interfaces

`BasePhiCanonicalExpansion` supplies the unique two-sided digit/value bridge.
`BasePhiCarryTransducer` supplies the deterministic carry/skip state machine
used by `frontierState` and `FrontierRunStep`. The `BasePhiNegative` definitions
retain their original scope; this file only binds the open chain to those
frozen interfaces.

## Status of semantic providers

The fiber shape, unique lift, phase totality, frontier existence, Lucas growth,
pairwise-disjoint arms, and final set transport now have kernel-checked proofs.
The additive successor provider remains open. The old phase provider remains
kernel-refuted by the imported frozen `010` obstruction; the replacement below
uses a new data-derived projection and does not alter that frozen record.

1. `frontier_step_semantics`: closed. `core_infinite_proved` constructs
   arbitrarily large occurrences by adjoining a sufficiently remote even
   Lucas pair of canonical digits, then uses the unique lift and the bound
   `prefixMultiplicity w ≤ 3` to prove `(Core w).Infinite`.
   `frontier_step_semantics_proved` therefore enumerates the actual core via
   `Nat.nth`; its source does not depend on the desired gap stream.
2. `source_index_successor_delta`: the compiled residual proposition is
   `sourceIndexSuccessorAdditive certificate`;
   `source_index_successor_delta_iff_additive` proves the exact equivalence
   before any integer gap is unfolded. `adjacent_core_point_right_unique` and
   `adjacent_core_point_eq_frontier_successor` now prove uniqueness and the
   strict-enumeration squeeze for every genuine adjacent-core candidate. What
   remains is existence: the phase-selected Lucas candidate must belong to
   `Core w` and exclude an intervening point. The singleton/triple theorem only
   compares inputs sharing one complete negative tail and cannot prove that.
3. `data_phase_gap_stream`: the exact scan retains the six prefix-machine
   states but corrects their output projection to `G1e ↦ G` and every other
   state to `F`. `DataFrontierGapPhase` and
   `DataPhaseEnrichedCoreTrace` state the replacement invariant, and
   `data_phase_enriched_core_trace_iff_gap_phase` proves their equivalence.
   `data_phase_machine_010_eq` computes the formal prefix certificate as
   `⟨G0o, 11, 7⟩`; `dataFrontierGapSelector_prefix010_zero` then proves the
   corrected first selection is `11`. The old `frontierFamily` projection and
   its two frozen refutation theorems remain unchanged.
4. `carry_run_weight_telescope`: the corrected module proves the local
   carry-step weight identity, the cocycle subdivision law, and the telescoped
   run equation. The residual term is the change in `negativeOneCount` between
   consecutive Core indices. No current theorem identifies that event-count
   change with the next hit of an arbitrary negative-prefix Core cylinder, so
   the global `DataPhaseEnrichedCoreTrace` existence provider remains open.
   `fibonacci_gap_letter_not_six_periodic` independently excludes replacing
   the retained aperiodic input letter by a fixed `n % 6` table.

Thus the corrected selector removes the explicit `010` contradiction, but the
current S1 interfaces still do not prove the complete F/G itinerary of an
arbitrary negative-tail prefix cylinder. No finite scan is used as a proof,
and no false theorem is replaced by a weaker claim or a hidden assumption.

The full theorem still has its `sorry` placeholder below, inside `X_Frontier`.
All other declarations above are signature checks or direct proofs; the
frontier semantic providers are intentionally not claimed closed.
-/

/- THEORIST_FRONTIER_CONTRACT_V2
{
  "schema": "trureturing-theorist-frontier-v2",
  "exact_statement": {
    "gid": "D5/X_Frontier/BasePhiNegativePrefixTrident.negative_prefix_trident_classification",
    "statement_sha256": "sha256:25ddd0972fd7b97c88f87ea47bb9843e5c014cdad5344c37451293f18cb4a0d9"
  },
  "motivation_gids": [
    "D5/S0/Conventions/WDigits",
    "D5/S1/Deficit/ZeckendorfDisplacementReading",
    "D5/S1/Words/Complexity/MechanicalSubshiftIntercept",
    "D5/S1/Words/GoldenMechanicalWord",
    "D5/S1/Words/GoldenSubstFixed",
    "D5/S1/Words/ReturnWords/GoldenOccurrenceGaps",
    "D5/S1/Words/ReturnWords/GoldenReturnItinerary",
    "D5/S1/Words/ReturnWords/GoldenReturnWords",
    "D5/S1/Words/ReturnWords/GoldenReturnWordsExact",
    "D5/S1/Words/ZeckendorfBeattyBridge",
    "D5/S1/Words/ZeckendorfOrder"
  ],
  "falsifier": "An admissible negative prefix w whose exact occurrence set is neither one Lucas-gap F/G/H sequence range nor a union of three such ranges sharing one Lucas pair.",
  "search_receipt_gids": ["D5/L/Words/dekking2023structure"],
  "computation_receipt_gids": ["D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json"],
  "triage_class": "theorem"
}
-/

/- TASK D5-T0046
   Formalize the two-sided base-phi digit/value bridge and classify every
   admissible negative prefix as one Lucas-gap F/G/H family or a union of
   three such families sharing one Lucas pair. The N<=2,000,000 exact
   integer-pair scan is finite evidence only; it does not close this theorem.
-/

/- include_in_statement=true -/
theorem negative_prefix_trident_classification
    (expansion : BasePhiNegativeExpansion) :
    ∀ w : List Bool,
      AdmissibleNegativePrefix expansion w →
        (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
          occurrenceSet expansion w = sequenceRange (vF a b r)) ∨
        (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
          occurrenceSet expansion w = sequenceRange (vG a b r)) ∨
        (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
          occurrenceSet expansion w = sequenceRange (vH a b r)) ∨
        (∃ (a b : Int) (families : Fin 3 → GapFamily) (first : Fin 3 → Int),
          lucasParameter a ∧ lucasParameter b ∧ (∀ i, 0 < first i) ∧
          occurrenceSet expansion w =
            ⋃ i, sequenceRange (vForFamily (families i) a b (first i))) := by
  sorry

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
