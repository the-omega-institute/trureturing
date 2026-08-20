/- GID: D5/X_Frontier/BasePhiNegativePrefixTrident
   generality: G
   mirror-B: none(waiver:negative-base-phi-frontier)
   mirror-E: D5/E/S1/Words/BasePhiNegativePrefixTrident.result--json
   anchors: [D5/S0/Conventions/WDigits, D5/S1/Words/GoldenMechanicalWord]
   digest: Classify admissible negative base-phi prefix occurrence sets by Lucas-gap trident families. -/

import D5.S0.Carrier.Units
import D5.S0.Conventions.WDigits
import D5.S1.Scale.Lucas
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S1.Scale
open scoped BigOperators

/-!
The source question asks for an exact classification of occurrence sequences
for finite negative-position prefix cylinders in the two-sided base-phi
expansion.  The definitions below keep the integer-pair value equation and
the non-adjacent digit condition explicit.  `vF`, `vG`, and `vH` have the
paper's first-difference words `x_F`, `x_G = b x_F`, and `x_H = a x_F` on a
Lucas-number gap pair.  The finite scan is evidence for this classification,
not its proof.
-/

noncomputable def basePhiValue (digits : Int →₀ Nat) : D5.S0.Carrier.GoldenInt :=
  Finset.sum digits.support (fun i =>
    (digits i : D5.S0.Carrier.GoldenInt) *
      (((D5.S0.Carrier.phiUnit ^ i : D5.S0.Carrier.GoldenIntˣ) :
        D5.S0.Carrier.GoldenInt)))

structure BasePhiNegativeExpansion where
  digit : Nat → Int →₀ Nat
  binary : ∀ N i, digit N i ≤ 1
  canonical : ∀ N i, digit N i = 1 → digit N (i + 1) = 0
  value_equation : ∀ N, basePhiValue (digit N) = (N : D5.S0.Carrier.GoldenInt)

def negativeDigit (expansion : BasePhiNegativeExpansion) (N i : Nat) : Bool :=
  decide (expansion.digit N (-((i + 1 : Nat) : Int)) = 1)

def reachesNegativeDepth (expansion : BasePhiNegativeExpansion)
    (N depth : Nat) : Prop :=
  0 < depth ∧
    ∃ i ∈ (expansion.digit N).support, i ≤ -((depth : Nat) : Int)

def NegativePrefixOccurs (expansion : BasePhiNegativeExpansion)
    (w : List Bool) (N : Nat) : Prop :=
  reachesNegativeDepth expansion N w.length ∧
    ∀ i : Fin w.length, negativeDigit expansion N i.1 = w.get i

def AdmissibleNegativePrefix (expansion : BasePhiNegativeExpansion)
    (w : List Bool) : Prop :=
  ∃ N, 0 < N ∧ NegativePrefixOccurs expansion w N

def occurrenceSet (expansion : BasePhiNegativeExpansion) (w : List Bool) : Set Nat :=
  {N | 0 < N ∧ NegativePrefixOccurs expansion w N}

def lucasParameter (value : Int) : Prop :=
  ∃ k : Nat, value = goldenLucas k

inductive GapFamily where
  | F
  | G
  | H
  deriving DecidableEq

noncomputable def fibonacciGapLetter (n : Nat) : Bool :=
  decide
    ((⌊((n + 2 : Nat) : ℝ) * Real.goldenRatio⌋ : Int) -
        (⌊((n + 1 : Nat) : ℝ) * Real.goldenRatio⌋ : Int) = 2)

noncomputable def familyLetter : GapFamily → Nat → Bool
  | .F, n => fibonacciGapLetter n
  | .G, 0 => false
  | .G, Nat.succ n => fibonacciGapLetter n
  | .H, 0 => true
  | .H, Nat.succ n => fibonacciGapLetter n

noncomputable def gapSequence (family : GapFamily) (a b first : Int) : Nat → Int
  | 0 => first
  | Nat.succ n =>
      gapSequence family a b first n + if familyLetter family n then a else b

noncomputable def vF (a b first : Int) (n : Nat) : Int :=
  gapSequence .F a b first n

noncomputable def vG (a b first : Int) (n : Nat) : Int :=
  gapSequence .G a b first n

noncomputable def vH (a b first : Int) (n : Nat) : Int :=
  gapSequence .H a b first n

noncomputable def vForFamily (family : GapFamily)
    (a b first : Int) (n : Nat) : Int :=
  match family with
  | .F => vF a b first n
  | .G => vG a b first n
  | .H => vH a b first n

def sequenceRange (sequence : Nat → Int) : Set Nat :=
  {N | ∃ n, (N : Int) = sequence n}

/- THEORIST_FRONTIER_CONTRACT_V2
{
  "schema": "trureturing-theorist-frontier-v2",
  "exact_statement": {
    "gid": "D5/X_Frontier/BasePhiNegativePrefixTrident.negative_prefix_trident_classification",
    "statement_sha256": "sha256:8a4c05efb74115fbd34bad4a1ed67d2718252ea2f831a3091a63d82e7bb4f2a1"
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

end D5.X_Frontier.BasePhiNegativePrefixTrident
