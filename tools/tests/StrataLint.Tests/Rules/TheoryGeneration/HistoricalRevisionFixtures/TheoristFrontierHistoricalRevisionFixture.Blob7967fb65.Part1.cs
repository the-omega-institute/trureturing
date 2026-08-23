namespace StrataLint.Tests;

internal static partial class TheoristFrontierHistoricalRevisionFixture
{
    private const string Blob7967fb65Part1 = """
/- GID: D5/X_Frontier/BasePhiNegativePrefixTrident
   generality: I
   mirror-B: none(waiver:negative-base-phi-frontier)
   mirror-E: D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json
   anchors: []
   digest: Classify admissible negative base-phi prefix occurrence sets by Lucas-gap trident families. -/

import D5.S1.Words.Expansions.BasePhiCarryTransducer
import D5.S1.Words.Expansions.BasePhiCanonicalExpansion
import D5.S1.Words.Expansions.BasePhiTailFiber

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

/- This is the frontier-facing signature of the singleton/trident fiber
shape. The paper (Dekking, Section 7.1/Theorem 7.5) locates the phenomenon;
the S1 proof below establishes it directly via Beatty floor coordinates and
does not formalize the paper's recursion. -/
def negative_tail_fiber_shape {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) : Prop :=
  ∀ N ∈ occurrenceSet canonicalExpansion w,
    (negativeDigit canonicalExpansion N 0 = true →
      negativeTailFiber N = ({N} : Set Nat)) ∧
    (negativeDigit canonicalExpansion N 0 = false →
      ∃! q : Nat, q ≤ N ∧ N ≤ q + 2 ∧
        negativeTailFiber N = {M | M = q ∨ M = q + 1 ∨ M = q + 2})

theorem negative_tail_fiber_shape_proved {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    negative_tail_fiber_shape hw hadmissible := by
  intro N hN
  have hshape :=
    D5.S1.Words.Expansions.BasePhiTailFiber.negative_tail_fiber_shape
      canonicalExpansion N hN.1 ⟨w.length, hN.2.1⟩
  simpa [negativeTailFiber, SameNegativeTail,
    D5.S1.Words.Expansions.BasePhiRecursiveStructure.negativeTailFiber,
    D5.S1.Words.Expansions.BasePhiRecursiveStructure.SameNegativeTail] using hshape

def core_occurrence_unique_lift {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible) : Prop :=
  ∀ N ∈ occurrenceSet canonicalExpansion w,
    ∃! qj : Nat × Nat,
      qj.1 ∈ Core w ∧ qj.2 < prefixMultiplicity w ∧ N = qj.1 + qj.2

private theorem digit_eq_of_same_tail {M N : Nat}
    (hsame : SameNegativeTail M N) {i : Int} (hi : i < 0) :
    canonicalExpansion.digit M i = canonicalExpansion.digit N i := by
  let k : Nat := (-i).toNat - 1
  have hneg : 0 < (-i).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hcast : ((-i).toNat : Int) = -i := Int.toNat_of_nonneg (by omega)
  have hk : k + 1 = (-i).toNat := Nat.sub_add_cancel (by omega)
  have hindex : -((k + 1 : Nat) : Int) = i := by
    rw [hk, hcast]
    omega
  have hbool := hsame k
  unfold negativeDigit at hbool
  rw [hindex] at hbool
  have hMle := canonicalExpansion.binary M i
  have hNle := canonicalExpansion.binary N i
  by_cases hM : canonicalExpansion.digit M i = 1
  · have hN : canonicalExpansion.digit N i = 1 := by
      apply of_decide_eq_true
      rw [← hbool]
      exact decide_eq_true hM
    omega
  · have hMzero : canonicalExpansion.digit M i = 0 := by omega
    have hNzero : canonicalExpansion.digit N i = 0 := by
      by_contra hN
      have hNone : canonicalExpansion.digit N i = 1 := by omega
      have : decide (canonicalExpansion.digit M i = 1) = true := by
        rw [hbool, decide_eq_true hNone]
      exact hM (of_decide_eq_true this)
    omega

private theorem reaches_of_same_tail {M N depth : Nat}
    (hsame : SameNegativeTail M N)
    (hreaches : reachesNegativeDepth canonicalExpansion N depth) :
    reachesNegativeDepth canonicalExpansion M depth := by
  rcases hreaches with ⟨hdepth, i, hiSupport, hi⟩
  refine ⟨hdepth, i, ?_, hi⟩
  have hiNeg : i < 0 := by omega
  have hEq := digit_eq_of_same_tail hsame hiNeg
  rw [Finsupp.mem_support_iff, hEq]
  exact Finsupp.mem_support_iff.mp hiSupport

private theorem prefix_occurs_of_same_tail {w : List Bool} {M N : Nat}
    (hsame : SameNegativeTail M N)
    (hoccurs : NegativePrefixOccurs canonicalExpansion w N) :
    NegativePrefixOccurs canonicalExpansion w M := by
  refine ⟨reaches_of_same_tail hsame hoccurs.1, ?_⟩
  intro i
  exact (hsame i).trans (hoccurs.2 i)

private theorem same_tail_symm {M N : Nat} (h : SameNegativeTail M N) :
    SameNegativeTail N M := fun i => (h i).symm

private theorem same_tail_trans {L M N : Nat}
    (hLM : SameNegativeTail L M) (hMN : SameNegativeTail M N) :
    SameNegativeTail L N := fun i => (hLM i).trans (hMN i)

theorem core_occurrence_unique_lift_proved {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible) :
    core_occurrence_unique_lift hw hadmissible hfibers := by
  intro N hN
  cases w with
  | nil => exact (hw rfl).elim
  | cons bit tail => cases bit with
    | true =>
        have hhead : negativeDigit canonicalExpansion N 0 = true := by
          simpa using hN.2.2 ⟨0, by simp⟩
        refine ⟨(N, 0), ?_, ?_⟩
        · refine ⟨⟨?_, hN.2⟩, by simp [prefixMultiplicity]⟩
          refine ⟨⟨hN.1, fun _ => rfl⟩, ?_⟩
          intro M hM
          have hsingleton := (hfibers N hN).1 hhead
          rw [hsingleton] at hM
          have hMN : M = N := by
            simpa only [Set.mem_singleton_iff] using hM
          exact hMN.ge
        · rintro ⟨q, j⟩ hqj
          have hj : j = 0 := by
            simpa [prefixMultiplicity] using hqj.2.1
          have hq : q = N := by omega
          subst q
          subst j
          rfl
    | false =>
        have hhead : negativeDigit canonicalExpansion N 0 = false := by
          simpa using hN.2.2 ⟨0, by simp⟩
        obtain ⟨q, hq, hqUnique⟩ := (hfibers N hN).2 hhead
        have hqMemN : q ∈ negativeTailFiber N := by
          rw [hq.2.2]
          simp
        have hqPos : 0 < q := hqMemN.1
        have hqSameN : SameNegativeTail q N := hqMemN.2
        have hfiberEq : negativeTailFiber q = negativeTailFiber N := by
          ext M
          constructor
          · rintro ⟨hM, hMq⟩
            exact ⟨hM, same_tail_trans hMq hqSameN⟩
          · rintro ⟨hM, hMN⟩
            exact ⟨hM, same_tail_trans hMN (same_tail_symm hqSameN)⟩
        have hqCore : q ∈ Core (false :: tail) := by
          refine ⟨⟨⟨hqPos, fun _ => rfl⟩, ?_⟩, ?_⟩
          · intro M hM
            rw [hfiberEq, hq.2.2] at hM
            rcases hM with rfl | rfl | rfl <;> omega
          · exact prefix_occurs_of_same_tail hqSameN hN.2
        let j := N - q
        have hj : j < prefixMultiplicity (false :: tail) := by
          simp [j, prefixMultiplicity]
          omega
        have hNqj : N = q + j := by
          dsimp [j]
          omega
        refine ⟨(q, j), ⟨hqCore, hj, hNqj⟩, ?_⟩
        rintro ⟨q', j'⟩ hqj'
        have hq'Start : fiberStart q' := hqj'.1.1
        have hq'Prefix : NegativePrefixOccurs canonicalExpansion (false :: tail) q' :=
          hqj'.1.2
        have hq'Pos : 0 < q' := hq'Start.1.1
        have hq'Occurrence : q' ∈ occurrenceSet canonicalExpansion (false :: tail) :=
          ⟨hq'Pos, hq'Prefix⟩
        have hq'Head : negativeDigit canonicalExpansion q' 0 = false := by
          simpa using hq'Prefix.2 ⟨0, by simp⟩
        obtain ⟨s, hs, _⟩ := (hfibers q' hq'Occurrence).2 hq'Head
        have hsMem : s ∈ negativeTailFiber q' := by
          rw [hs.2.2]
          simp
        have hsEq : s = q' := by
          have := hq'Start.2 s hsMem
          omega
        have hq'Fiber : negativeTailFiber q' =
            {M | M = q' ∨ M = q' + 1 ∨ M = q' + 2} := by
          simpa [hsEq] using hs.2.2
        have hNMemQ' : N ∈ negativeTailFiber q' := by
          have hj' : j' < 3 := by simpa [prefixMultiplicity] using hqj'.2.1
          rw [hq'Fiber]
          change N = q' ∨ N = q' + 1 ∨ N = q' + 2
          omega
        have hNsameQ' := hNMemQ'.2
        have hQ'sameN := same_tail_symm hNsameQ'
        have hfiberQ'N : negativeTailFiber q' = negativeTailFiber N := by
          ext M
          constructor
          · rintro ⟨hM, hMq'⟩
            exact ⟨hM, same_tail_trans hMq' hQ'sameN⟩
          · rintro ⟨hM, hMN⟩
            exact ⟨hM, same_tail_trans hMN (same_tail_symm hQ'sameN)⟩
        have hq'Data : q' ≤ N ∧ N ≤ q' + 2 ∧
            negativeTailFiber N = {M | M = q' ∨ M = q' + 1 ∨ M = q' + 2} := by
          constructor
          · omega
          constructor
          · have : j' < 3 := by simpa [prefixMultiplicity] using hqj'.2.1
            omega
          · rw [← hfiberQ'N]
            exact hq'Fiber
        have hqEq : q' = q := hqUnique q' hq'Data
        apply Prod.ext
        · exact hqEq
        · omega

def prefix_phase_machine_total {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) : Prop :=
  ∃! certificate : FrontierPhaseCertificate, PrefixPhaseMachineFor w certificate

private def startCertificate : Bool → FrontierPhaseCertificate
  | false => ⟨.F0o, 4, 3⟩
  | true => ⟨.F1o, 7, 4⟩

private def nextCertificate : FrontierPhaseCertificate → Bool →
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

private def phaseCertificate? : List Bool → Option FrontierPhaseCertificate
  | [] => none
  | bit :: tail => some (tail.foldl nextCertificate (startCertificate bit))

private theorem transition_nextCertificate {before after : FrontierPhaseCertificate}
    {bit : Bool} (h : FrontierPhaseTransition before bit after) :
    nextCertificate before bit = after := by
  cases h <;> rfl

private theorem phase_machine_nonempty {w : List Bool} {c : FrontierPhaseCertificate}
    (h : PrefixPhaseMachineFor w c) : w ≠ [] := by
  induction h <;> simp_all

private theorem phaseCertificate_append_singleton {w : List Bool} (hw : w ≠ [])
    (bit : Bool) :
    phaseCertificate? (w ++ [bit]) =
      (phaseCertificate? w).map fun c => nextCertificate c bit := by
  cases w with
  | nil => contradiction
  | cons head tail => simp [phaseCertificate?, List.foldl_append]

private theorem phase_machine_evaluates {w : List Bool} {c : FrontierPhaseCertificate}
    (h : PrefixPhaseMachineFor w c) : phaseCertificate? w = some c := by
  induction h with
  | zero => rfl
  | one => rfl
  | step hprefix transition ih =>
      rw [phaseCertificate_append_singleton (phase_machine_nonempty hprefix) _]
      rw [ih]
      simp [transition_nextCertificate transition]

private theorem phase_marks_last_true {w : List Bool} {c : FrontierPhaseCertificate}
    (h : PrefixPhaseMachineFor w c) :
    (c.phase = .F1o ∨ c.phase = .G1e) ↔ w.getLast? = some true := by
  induction h with
  | zero => decide
  | one => decide
  | step hprefix transition ih =>
      cases transition <;> simp

private theorem phase_machine_unique {w : List Bool} {c d : FrontierPhaseCertificate}
    (hc : PrefixPhaseMachineFor w c) (hd : PrefixPhaseMachineFor w d) : c = d := by
  have hcEval := phase_machine_evaluates hc
  have hdEval := phase_machine_evaluates hd
  rw [hcEval] at hdEval
  exact Option.some.inj hdEval

private def AdjacentChain (previous : Bool) : List Bool → Prop
  | [] => True
  | bit :: tail => ¬(previous = true ∧ bit = true) ∧ AdjacentChain bit tail

private theorem adjacentChain_of_indexed (head : Bool) (tail : List Bool)
    (h : ∀ i : Nat, ∀ hi : i + 1 < (head :: tail).length,
      ¬((head :: tail).get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ = true ∧
        (head :: tail).get ⟨i + 1, hi⟩ = true)) :
    AdjacentChain head tail := by
  induction tail generalizing head with
  | nil => trivial
  | cons bit tail ih =>
      constructor
      · simpa using h 0 (by simp)
      · apply ih bit
        intro i hi
        have hnext := h (i + 1) (by simp at hi ⊢; omega)
        simpa using hnext

private theorem transition_exists_of_adjacent {w : List Bool}
    {c : FrontierPhaseCertificate} {previous bit : Bool}
    (hmachine : PrefixPhaseMachineFor w c)
    (hlast : w.getLast? = some previous)
    (hadjacent : ¬(previous = true ∧ bit = true)) :
    FrontierPhaseTransition c bit (nextCertificate c bit) := by
  have hphase := phase_marks_last_true hmachine
  rcases c with ⟨phase, a, b⟩
  cases phase <;> cases bit
  · exact .F0o_zero a b
  · exact .F0o_one a b
  · exact .F1o_zero a b
  · exfalso
    apply hadjacent
    refine ⟨?_, rfl⟩
    apply Option.some.inj
    exact hlast.symm.trans (hphase.mp (Or.inl rfl))
  · exact .F0e_zero a b
  · exact .F0e_one a b
  · exact .G1e_zero a b
  · exfalso
    apply hadjacent
    refine ⟨?_, rfl⟩
    apply Option.some.inj
    exact hlast.symm.trans (hphase.mp (Or.inr rfl))
  · exact .G0o_zero a b
  · exact .G0o_one a b
  · exact .H0e_zero a b
  · exact .H0e_one a b

private theorem extend_phase_machine {word : List Bool}
    {c : FrontierPhaseCertificate} {previous : Bool} (tail : List Bool)
    (hmachine : PrefixPhaseMachineFor word c)
    (hlast : word.getLast? = some previous)
    (hchain : AdjacentChain previous tail) :
    PrefixPhaseMachineFor (word ++ tail) (tail.foldl nextCertificate c) := by
  induction tail generalizing word c previous with
  | nil => simpa
  | cons bit tail ih =>
      have hadjacent := hchain.1
      have hrest := hchain.2
      have htransition := transition_exists_of_adjacent hmachine hlast hadjacent
      have hstep := PrefixPhaseMachineFor.step hmachine htransition
      have hlastStep : (word ++ [bit]).getLast? = some bit := by simp
      have hresult := ih (word := word ++ [bit]) hstep hlastStep hrest
      simpa [List.foldl, List.append_assoc] using hresult

private theorem phase_machine_exists_of_admissible {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    ∃ c, PrefixPhaseMachineFor w c := by
  cases w with
  | nil => contradiction
  | cons head tail =>
      have hindexed := admissible_prefix_no_adjacent_true canonicalExpansion hadmissible
      have hchain := adjacentChain_of_indexed head tail hindexed
      cases head with
      | false =>
          exact ⟨_, extend_phase_machine tail PrefixPhaseMachineFor.zero (by simp) hchain⟩
      | true =>
          exact ⟨_, extend_phase_machine tail PrefixPhaseMachineFor.one (by simp) hchain⟩

theorem prefix_phase_machine_total_proved {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    prefix_phase_machine_total hw hadmissible := by
  obtain ⟨c, hc⟩ := phase_machine_exists_of_admissible hw hadmissible
  exact ⟨c, hc, fun d hd => phase_machine_unique hd hc⟩

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

private theorem goldenLucas_add_two (n : Nat) :
    goldenLucas (n + 2) = goldenLucas (n + 1) + goldenLucas n := by
  have hp : D5.S0.Carrier.phi ^ (n + 2) =
      D5.S0.Carrier.phi ^ (n + 1) + D5.S0.Carrier.phi ^ n := by
    rw [show n + 2 = n + 2 by rfl, pow_add,
      D5.S0.Carrier.phi_sq, pow_succ]
    ring
  simp only [goldenLucas, hp, D5.S0.Carrier.trace]
  simp
  ring

private theorem LucasPair.grow0 {a b : Int} (h : LucasPair a b) :
    LucasPair (a + b) a := by
  obtain ⟨k, hk, ha, hb⟩ := h
  refine ⟨k + 1, by omega, ?_, ?_⟩
  · rw [ha, hb]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using (goldenLucas_add_two k).symm
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using ha

private theorem LucasPair.grow1 {a b : Int} (h : LucasPair a b) :
    LucasPair (2 * a + b) (a + b) := by
  have h0 := h.grow0
  have h1 := h0.grow0
  convert h1 using 1 <;> ring

private theorem LucasPair.b_ge_three {a b : Int} (h : LucasPair a b) :
    3 ≤ b := by
  obtain ⟨k, hk, _, rfl⟩ := h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 2 + j = (j + 1) + 1 by omega,
    golden_lucas_succ_eq_fib_add_fib]
  have h1 : Nat.fib 1 ≤ Nat.fib (j + 1) := Nat.fib_mono (by omega)
  have h3 : Nat.fib 3 ≤ Nat.fib (j + 3) := Nat.fib_mono (by omega)
  norm_num at h1 h3
  rw [show j + 1 + 2 = j + 3 by omega]
  exact_mod_cast Nat.add_le_add h1 h3

private theorem lucas_of_phase_machine {w : List Bool}
    {c : FrontierPhaseCertificate} (h : PrefixPhaseMachineFor w c) :
    LucasPair c.a c.b ∧ 3 ≤ c.b := by
  induction h with
  | zero =>
      constructor
      · refine ⟨2, by norm_num, ?_, ?_⟩ <;>
          first
          | rw [show 2 + 1 = 2 + 1 by rfl,
              golden_lucas_succ_eq_fib_add_fib]; norm_num
          | rw [show 2 = 1 + 1 by omega,
              golden_lucas_succ_eq_fib_add_fib]; norm_num
      · norm_num
  | one =>
      constructor
      · refine ⟨3, by norm_num, ?_, ?_⟩ <;>
          first
          | rw [show 3 + 1 = 3 + 1 by rfl,
              golden_lucas_succ_eq_fib_add_fib]; norm_num
          | rw [show 3 = 2 + 1 by omega,
              golden_lucas_succ_eq_fib_add_fib]; norm_num
      · norm_num
  | step hprefix transition ih =>
      cases transition
      · exact ⟨ih.1.grow0, ih.1.grow0.b_ge_three⟩
      · exact ⟨ih.1.grow1, ih.1.grow1.b_ge_three⟩
      · exact ih
      · exact ⟨ih.1.grow0, ih.1.grow0.b_ge_three⟩
      · exact ⟨ih.1.grow1, ih.1.grow1.b_ge_three⟩
      · exact ih
      · exact ⟨ih.1.grow0, ih.1.grow0.b_ge_three⟩
      · exact ⟨ih.1.grow1, ih.1.grow1.b_ge_three⟩
      · exact ⟨ih.1.grow0, ih.1.grow0.b_ge_three⟩
      · exact ⟨ih.1.grow1, ih.1.grow1.b_ge_three⟩

theorem lucas_pair_closed_under_growth_proved {w : List Bool}
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor w certificate) :
    lucas_pair_closed_under_growth hcertificate := by
""";

    private static string Blob7967fb65 => Blob7967fb65Part1 + "\n" + Blob7967fb65Part2;
}
