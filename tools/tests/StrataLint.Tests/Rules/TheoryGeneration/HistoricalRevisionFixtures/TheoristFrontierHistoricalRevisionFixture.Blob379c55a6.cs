namespace StrataLint.Tests;

internal static partial class TheoristFrontierHistoricalRevisionFixture
{
    private const string Blob379c55a6 = """
/- GID: D5/X_Frontier/BasePhiNegativePrefixTrident
   generality: I
   mirror-B: none(waiver:negative-base-phi-frontier)
   mirror-E: D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json
   anchors: []
   digest: Classify admissible negative base-phi prefix occurrence sets by Lucas-gap trident families. -/

import D5.S1.Words.Expansions.BasePhiCarryTransducer
import D5.S1.Words.Expansions.BasePhiCanonicalExpansion

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Scale

noncomputable section

/-!
The canonical-expansion bridge is useful here even before the return-word
classification is available.  It removes the otherwise arbitrary choice of
`BasePhiNegativeExpansion` from every occurrence-set statement.
-/

noncomputable def canonicalDigits (N : Nat) : Int →₀ Nat :=
  Classical.choose (basePhiExpansion_exists N)

theorem canonicalDigits_spec (N : Nat) :
    (∀ i : Int, canonicalDigits N i ≤ 1) ∧
      (∀ i : Int, canonicalDigits N i = 1 → canonicalDigits N (i + 1) = 0) ∧
      basePhiValue (canonicalDigits N) = (N : D5.S0.Carrier.GoldenInt) := by
  exact Classical.choose_spec (basePhiExpansion_exists N)

noncomputable def canonicalExpansion : BasePhiNegativeExpansion :=
  { digit := canonicalDigits
    binary := fun N i => (canonicalDigits_spec N).1 i
    canonical := fun N i => (canonicalDigits_spec N).2.1 i
    value_equation := fun N => (canonicalDigits_spec N).2.2 }

theorem expansion_digit_eq_canonical (expansion : BasePhiNegativeExpansion) (N : Nat) :
    expansion.digit N = canonicalDigits N := by
  obtain ⟨digits, hdigits, hunique⟩ := basePhiExpansion_existsUnique N
  exact (hunique (expansion.digit N) ⟨expansion.binary N, expansion.canonical N,
    expansion.value_equation N⟩).trans
    (hunique (canonicalDigits N) (canonicalDigits_spec N)).symm

theorem occurrenceSet_eq_canonical (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    occurrenceSet expansion w = occurrenceSet canonicalExpansion w := by
  ext N
  have hdigits : expansion.digit N = canonicalExpansion.digit N := by
    exact expansion_digit_eq_canonical expansion N
  constructor <;> intro h
  · rcases h with ⟨hpositive, hoccurs⟩
    refine ⟨hpositive, ?_⟩
    simpa [NegativePrefixOccurs, reachesNegativeDepth, negativeDigit, hdigits] using hoccurs
  · rcases h with ⟨hpositive, hoccurs⟩
    refine ⟨hpositive, ?_⟩
    simpa [NegativePrefixOccurs, reachesNegativeDepth, negativeDigit, hdigits] using hoccurs

theorem occurrenceSet_nonempty_of_admissible (expansion : BasePhiNegativeExpansion)
    {w : List Bool} (h : AdmissibleNegativePrefix expansion w) :
    (occurrenceSet expansion w).Nonempty :=
  (admissible_negative_prefix_iff_occurrence_set_nonempty expansion w).mp h

theorem occurrenceSet_subset_positive (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    occurrenceSet expansion w ⊆ {N | 0 < N} := by
  intro N hN
  exact hN.1

theorem admissible_prefix_no_adjacent_true (expansion : BasePhiNegativeExpansion)
    {w : List Bool} (h : AdmissibleNegativePrefix expansion w) :
    ∀ i : Nat, ∀ hi : i + 1 < w.length,
      ¬(w.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ = true ∧
        w.get ⟨i + 1, hi⟩ = true) := by
  intro i hi hbits
  exact not_admissible_negative_prefix_of_adjacent_true expansion w i hi
    hbits.1 hbits.2 h

def TridentWitness (expansion : BasePhiNegativeExpansion) (w : List Bool) : Prop :=
  (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
      occurrenceSet expansion w = sequenceRange (vF a b r)) ∨
    (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
      occurrenceSet expansion w = sequenceRange (vG a b r)) ∨
    (∃ a b r, 0 < r ∧ lucasParameter a ∧ lucasParameter b ∧
      occurrenceSet expansion w = sequenceRange (vH a b r)) ∨
    (∃ (a b : Int) (families : Fin 3 → GapFamily) (first : Fin 3 → Int),
      lucasParameter a ∧ lucasParameter b ∧ (∀ i, 0 < first i) ∧
      occurrenceSet expansion w =
        ⋃ i, sequenceRange (vForFamily (families i) a b (first i)))

theorem admissible_negative_prefix_iff_canonical (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    AdmissibleNegativePrefix expansion w ↔
      AdmissibleNegativePrefix canonicalExpansion w := by
  rw [admissible_negative_prefix_iff_occurrence_set_nonempty,
    admissible_negative_prefix_iff_occurrence_set_nonempty,
    occurrenceSet_eq_canonical]

theorem trident_witness_iff_canonical (expansion : BasePhiNegativeExpansion)
    (w : List Bool) :
    TridentWitness expansion w ↔ TridentWitness canonicalExpansion w := by
  simp only [TridentWitness, occurrenceSet_eq_canonical]

theorem trident_classification_reduces_to_canonical (expansion : BasePhiNegativeExpansion) :
    (∀ w : List Bool,
      AdmissibleNegativePrefix expansion w → TridentWitness expansion w) ↔
      (∀ w : List Bool,
        AdmissibleNegativePrefix canonicalExpansion w → TridentWitness canonicalExpansion w) := by
  constructor
  · intro h w hw
    exact (trident_witness_iff_canonical expansion w).mp
      (h w ((admissible_negative_prefix_iff_canonical expansion w).mpr hw))
  · intro h w hw
    exact (trident_witness_iff_canonical expansion w).mpr
      (h w ((admissible_negative_prefix_iff_canonical expansion w).mp hw))

def SameNegativeTail (M N : Nat) : Prop :=
  ∀ i : Nat, negativeDigit canonicalExpansion M i = negativeDigit canonicalExpansion N i

def negativeTailFiber (N : Nat) : Set Nat :=
  {M | 0 < M ∧ SameNegativeTail M N}

def fiberStart (q : Nat) : Prop :=
  q ∈ negativeTailFiber q ∧ ∀ M ∈ negativeTailFiber q, q ≤ M

def Core (w : List Bool) : Set Nat :=
  {q | fiberStart q ∧ NegativePrefixOccurs canonicalExpansion w q}

def prefixMultiplicity (w : List Bool) : Nat :=
  if w.head? = some true then 1 else 3

def LucasPair (a b : Int) : Prop :=
  ∃ k : Nat, 2 ≤ k ∧ a = goldenLucas (k + 1) ∧ b = goldenLucas k

inductive FrontierPhase where
  | F0o
  | F1o
  | F0e
  | G1e
  | G0o
  | H0e
  deriving DecidableEq

def frontierFamily : FrontierPhase → GapFamily
  | .F0o | .F1o | .F0e => .F
  | .G1e | .G0o => .G
  | .H0e => .H

def grow0 (a b : Int) : Int × Int :=
  (a + b, a)

def grow1 (a b : Int) : Int × Int :=
  (2 * a + b, a + b)

structure FrontierPhaseCertificate where
  phase : FrontierPhase
  a : Int
  b : Int

/-- The ten transitions from the six-state frontier proposal.  This is the
prefix-extension machine; it is deliberately separate from the input-by-input
carry machine below. -/
inductive FrontierPhaseTransition :
    FrontierPhaseCertificate → Bool → FrontierPhaseCertificate → Prop where
  | F0o_zero (a b : Int) :
      FrontierPhaseTransition ⟨.F0o, a, b⟩ false ⟨.F0e, a + b, a⟩
  | F0o_one (a b : Int) :
      FrontierPhaseTransition ⟨.F0o, a, b⟩ true ⟨.G1e, 2 * a + b, a + b⟩
  | F1o_zero (a b : Int) :
      FrontierPhaseTransition ⟨.F1o, a, b⟩ false ⟨.F0e, a, b⟩
  | F0e_zero (a b : Int) :
      FrontierPhaseTransition ⟨.F0e, a, b⟩ false ⟨.F0o, a + b, a⟩
  | F0e_one (a b : Int) :
      FrontierPhaseTransition ⟨.F0e, a, b⟩ true ⟨.F1o, 2 * a + b, a + b⟩
  | G1e_zero (a b : Int) :
      FrontierPhaseTransition ⟨.G1e, a, b⟩ false ⟨.G0o, a, b⟩
  | G0o_zero (a b : Int) :
      FrontierPhaseTransition ⟨.G0o, a, b⟩ false ⟨.H0e, a + b, a⟩
  | G0o_one (a b : Int) :
      FrontierPhaseTransition ⟨.G0o, a, b⟩ true ⟨.G1e, 2 * a + b, a + b⟩
  | H0e_zero (a b : Int) :
      FrontierPhaseTransition ⟨.H0e, a, b⟩ false ⟨.G0o, a + b, a⟩
  | H0e_one (a b : Int) :
      FrontierPhaseTransition ⟨.H0e, a, b⟩ true ⟨.F1o, 2 * a + b, a + b⟩

/-- A phase certificate is generated from one of the two checked base cases by
the prefix-extension table.  In particular, its Lucas parameters cannot be
changed independently of its phase history. -/
inductive PrefixPhaseMachineFor : List Bool → FrontierPhaseCertificate → Prop where
  | zero : PrefixPhaseMachineFor [false] ⟨.F0o, 4, 3⟩
  | one : PrefixPhaseMachineFor [true] ⟨.F1o, 7, 4⟩
  | step {w : List Bool} {before after : FrontierPhaseCertificate} {bit : Bool}
      (hprefix : PrefixPhaseMachineFor w before)
      (transition : FrontierPhaseTransition before bit after) :
      PrefixPhaseMachineFor (w ++ [bit]) after

structure FrontierReturnWord where
  phaseCertificate : FrontierPhaseCertificate
  boundary : CarrySkipState
  enumerate : Nat → Nat

def FrontierReturnWord.phase (certificate : FrontierReturnWord) : FrontierPhase :=
  certificate.phaseCertificate.phase

def FrontierReturnWord.a (certificate : FrontierReturnWord) : Int :=
  certificate.phaseCertificate.a

def FrontierReturnWord.b (certificate : FrontierReturnWord) : Int :=
  certificate.phaseCertificate.b

/-- The first term is derived from the enumerator, rather than stored as an
independent field. -/
def FrontierReturnWord.first (certificate : FrontierReturnWord) : Int :=
  certificate.enumerate 0

/-- Gaps are differences of consecutive enumerated inputs, rather than an
independent stream. -/
def FrontierReturnWord.gap (certificate : FrontierReturnWord) (n : Nat) : Int :=
  (certificate.enumerate (n + 1) : Int) - certificate.enumerate n

/-- Every frontier point is interpreted at the actual terminal state of the
frozen carry/skip run. -/
noncomputable def frontierState (certificate : FrontierReturnWord) (n : Nat) :
    CarrySkipState :=
  carrySkipRun canonicalExpansion (certificate.enumerate n)

/-- Moving between consecutive frontier points is a finite chain of the actual
`CarrySkipTransition`; one step therefore uses `nextState`, whose positive
component is `carrySkipStep`. -/
def FrontierRunStep (certificate : FrontierReturnWord) (n : Nat) : Prop :=
  Relation.ReflTransGen (CarrySkipTransition canonicalExpansion)
    (frontierState certificate n) (frontierState certificate (n + 1))

def FrontierGapPhase (certificate : FrontierReturnWord) : Prop :=
  ∀ n : Nat,
    certificate.gap n =
      if familyLetter (frontierFamily certificate.phase) n then
        certificate.a
      else
        certificate.b

/-- The return-word predicate binds every field to either the prefix machine or
the frozen carry machine. -/
structure FrontierReturnWordFor (w : List Bool)
    (certificate : FrontierReturnWord) : Prop where
  phase_machine : PrefixPhaseMachineFor w certificate.phaseCertificate
  boundary_eq : certificate.boundary = frontierState certificate 0
  range_eq : Set.range certificate.enumerate = Core w
  successor_strict : ∀ n : Nat,
    certificate.enumerate n < certificate.enumerate (n + 1)
  run_step : ∀ n : Nat, FrontierRunStep certificate n

def CoreLucasWitness (w : List Bool) : Prop :=
  ∃ (family : GapFamily) (a b r : Int),
    LucasPair a b ∧ 0 < r ∧
      Core w = sequenceRange (vForFamily family a b r)

/- The first signature depends on Dekking's Recursive Structure Theorem 7.5.
That theorem is not formalized in the current import closure; this proposition
records the required consequence without claiming the missing proof. -/
def negative_tail_fiber_shape {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) : Prop :=
  ∀ N ∈ occurrenceSet canonicalExpansion w,
    (negativeDigit canonicalExpansion N 0 = true →
      negativeTailFiber N = ({N} : Set Nat)) ∧
    (negativeDigit canonicalExpansion N 0 = false →
      ∃! q : Nat, q ≤ N ∧ N ≤ q + 2 ∧
        negativeTailFiber N = {M | M = q ∨ M = q + 1 ∨ M = q + 2})

def core_occurrence_unique_lift {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible) : Prop :=
  ∀ N ∈ occurrenceSet canonicalExpansion w,
    ∃! qj : Nat × Nat,
      qj.1 ∈ Core w ∧ qj.2 < prefixMultiplicity w ∧ N = qj.1 + qj.2

def prefix_phase_machine_total {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) : Prop :=
  ∃! certificate : FrontierPhaseCertificate, PrefixPhaseMachineFor w certificate

def frontier_step_semantics {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers)
    (hphase : prefix_phase_machine_total hw hadmissible) : Prop :=
  ∃ certificate : FrontierReturnWord, FrontierReturnWordFor w certificate

def lucas_pair_closed_under_growth {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) : Prop :=
  LucasPair certificate.a certificate.b ∧ 3 ≤ certificate.b

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

def six_phase_gap_stream {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate)
    (hdelta : source_index_successor_delta hcertificate
      (core_enum_from_frontier hcertificate)) : Prop :=
  FrontierGapPhase certificate

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
    (hstream : six_phase_gap_stream hcertificate hdelta) :
    coreEnum certificate =
      vForFamily (frontierFamily certificate.phase)
        certificate.a certificate.b certificate.first := by
  funext n
  induction n with
  | zero =>
      cases frontierFamily certificate.phase <;>
        rfl
  | succ n ih =>
      have hgap := hstream n
      change coreEnum certificate (n + 1) - coreEnum certificate n =
        (if familyLetter (frontierFamily certificate.phase) n then
          certificate.a else certificate.b) at hgap
      cases family : frontierFamily certificate.phase <;>
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
      vForFamily (frontierFamily certificate.phase)
        certificate.a certificate.b certificate.first) :
    CoreLucasWitness w := by
  refine ⟨frontierFamily certificate.phase, certificate.a, certificate.b,
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
      six_phase_gap_stream hcertificate delta)
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
   Dekking Recursive Structure Theorem 7.5.
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
9. `six_phase_gap_stream`: derives the phase gap stream from that delta.
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

Two additional inconsistencies were found while aligning the record. First, the
old file exposed only seven compressed `Prop` obligations even though the
surrounding reconnaissance prose described fifteen typed chain nodes. Second,
`carrySkipStep` and its state machine are not in `BasePhiNegativeBridge.lean`;
the frozen definitions are in `BasePhiCarryTransducer.lean`, which is now the
import and source used by this file.

The first node remains explicitly dependent on Dekking 7.5, which is not yet
formalized in this import closure. That missing theorem is recorded, not
bypassed. No new non-`X_Frontier` `sorry` was introduced; the final theorem
below remains the sole frontier placeholder.

## Closed supporting interfaces

`BasePhiCanonicalExpansion` supplies the unique two-sided digit/value bridge.
`BasePhiCarryTransducer` supplies the deterministic carry/skip state machine
used by `frontierState` and `FrontierRunStep`. The `BasePhiNegative` definitions
retain their original scope; this file only binds the open chain to those
frozen interfaces.

## Status of open providers

The semantic providers remain open at their declared types. In particular,
`negative_tail_fiber_shape` is the carry/skip boundary theorem and retains its
explicit Dekking 7.5 dependency; no missing theorem is replaced by a weaker
claim or a hidden assumption.

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
""";
}
