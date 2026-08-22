/- GID: D5/S1/Words/Expansions/BasePhiNegative
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiNegative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Negative base-phi prefixes and their Lucas-gap sequence families. -/

import D5.S0.Carrier.Units
import D5.S0.Conventions.WDigits
import D5.S1.Scale.Lucas
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Words.Expansions.BasePhiNegative

open D5.S1.Scale
open scoped BigOperators

/-- The exact value in `Z[phi]` of a finite two-sided digit family. -/
noncomputable def basePhiValue (digits : Int →₀ Nat) : D5.S0.Carrier.GoldenInt :=
  Finset.sum digits.support (fun i =>
    (digits i : D5.S0.Carrier.GoldenInt) *
      (((D5.S0.Carrier.phiUnit ^ i : D5.S0.Carrier.GoldenIntˣ) :
        D5.S0.Carrier.GoldenInt)))

/-- A choice of finite canonical base-phi expansions for all natural numbers. -/
structure BasePhiNegativeExpansion where
  digit : Nat → Int →₀ Nat
  binary : ∀ N i, digit N i ≤ 1
  canonical : ∀ N i, digit N i = 1 → digit N (i + 1) = 0
  value_equation : ∀ N, basePhiValue (digit N) = (N : D5.S0.Carrier.GoldenInt)

/-- The digit at exponent `-(i+1)`. -/
def negativeDigit (expansion : BasePhiNegativeExpansion) (N i : Nat) : Bool :=
  decide (expansion.digit N (-((i + 1 : Nat) : Int)) = 1)

/-- The finite expansion of `N` contains a nonzero digit at or below `-depth`. -/
def reachesNegativeDepth (expansion : BasePhiNegativeExpansion)
    (N depth : Nat) : Prop :=
  0 < depth ∧
    ∃ i ∈ (expansion.digit N).support, i ≤ -((depth : Nat) : Int)

/-- The finite word `w` is the negative prefix of the expansion of `N`. -/
def NegativePrefixOccurs (expansion : BasePhiNegativeExpansion)
    (w : List Bool) (N : Nat) : Prop :=
  reachesNegativeDepth expansion N w.length ∧
    ∀ i : Fin w.length, negativeDigit expansion N i.1 = w.get i

/-- A negative prefix is admissible when it occurs for some positive natural number. -/
def AdmissibleNegativePrefix (expansion : BasePhiNegativeExpansion)
    (w : List Bool) : Prop :=
  ∃ N, 0 < N ∧ NegativePrefixOccurs expansion w N

/-- The positive natural numbers whose negative prefix is `w`. -/
def occurrenceSet (expansion : BasePhiNegativeExpansion) (w : List Bool) : Set Nat :=
  {N | 0 < N ∧ NegativePrefixOccurs expansion w N}

/-- An integer is an allowed gap parameter when it is a Lucas number. -/
def lucasParameter (value : Int) : Prop :=
  ∃ k : Nat, value = goldenLucas k

/-- The three Sturmian first-difference families in the trident conjecture. -/
inductive GapFamily where
  | F
  | G
  | H
  deriving DecidableEq

/-- The Fibonacci first-difference word, with `true` denoting the larger gap. -/
noncomputable def fibonacciGapLetter (n : Nat) : Bool :=
  decide
    ((⌊((n + 2 : Nat) : ℝ) * Real.goldenRatio⌋ : Int) -
        (⌊((n + 1 : Nat) : ℝ) * Real.goldenRatio⌋ : Int) = 2)

/-- The `F`, `G = bF`, and `H = aF` first-difference words. -/
noncomputable def familyLetter : GapFamily → Nat → Bool
  | .F, n => fibonacciGapLetter n
  | .G, 0 => false
  | .G, Nat.succ n => fibonacciGapLetter n
  | .H, 0 => true
  | .H, Nat.succ n => fibonacciGapLetter n

/-- The sequence obtained by accumulating gaps `a` and `b` along one family word. -/
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

/-- The natural values attained by an integer-valued sequence. -/
def sequenceRange (sequence : Nat → Int) : Set Nat :=
  {N | ∃ n, (N : Int) = sequence n}

/-- Every Lucas gap parameter is strictly positive. -/
theorem lucas_parameter_pos {value : Int} (h : lucasParameter value) : 0 < value := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => norm_num [goldenLucas, D5.S0.Carrier.trace]
  | succ k =>
      rw [show k + 1 = k + 1 by rfl, golden_lucas_succ_eq_fib_add_fib]
      have hfib : 0 < Nat.fib (k + 2) := Nat.fib_pos.mpr (by omega)
      omega

/-- Positive gap letters make every trident component strictly increasing. -/
theorem gap_sequence_strict_mono (family : GapFamily) {a b first : Int}
    (ha : 0 < a) (hb : 0 < b) : StrictMono (gapSequence family a b first) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [gapSequence]
  split <;> omega

/-- The first difference of `vF` is selected by the Fibonacci gap word. -/
theorem vF_succ (a b first : Int) (n : Nat) :
    vF a b first (n + 1) =
      vF a b first n + if familyLetter .F n then a else b := by
  rfl

/-- The first difference of `vG` is selected by `b` followed by the Fibonacci gap word. -/
theorem vG_succ (a b first : Int) (n : Nat) :
    vG a b first (n + 1) =
      vG a b first n + if familyLetter .G n then a else b := by
  rfl

/-- The first difference of `vH` is selected by `a` followed by the Fibonacci gap word. -/
theorem vH_succ (a b first : Int) (n : Nat) :
    vH a b first (n + 1) =
      vH a b first n + if familyLetter .H n then a else b := by
  rfl

/-- A deeper true negative digit forces the adjacent shallower digit to be false. -/
theorem negative_digit_succ_eq_false_of_eq_true
    (expansion : BasePhiNegativeExpansion) (N i : Nat)
    (h : negativeDigit expansion N (i + 1) = true) :
    negativeDigit expansion N i = false := by
  have hone : expansion.digit N (-(((i + 1) + 1 : Nat) : Int)) = 1 := by
    exact of_decide_eq_true h
  have hzero := expansion.canonical N (-(((i + 1) + 1 : Nat) : Int)) hone
  have hindex : -(((i + 1) + 1 : Nat) : Int) + 1 = -((i + 1 : Nat) : Int) := by
    push_cast
    ring
  rw [hindex] at hzero
  change decide (expansion.digit N (-((i + 1 : Nat) : Int)) = 1) = false
  rw [hzero]
  decide

/-- A negative prefix containing adjacent true digits is not admissible. -/
theorem not_admissible_negative_prefix_of_adjacent_true
    (expansion : BasePhiNegativeExpansion) (w : List Bool) (i : Nat)
    (hi : i + 1 < w.length)
    (hcurrent : w.get ⟨i, by omega⟩ = true)
    (hnext : w.get ⟨i + 1, hi⟩ = true) :
    ¬ AdmissibleNegativePrefix expansion w := by
  rintro ⟨N, _hN, hoccurs⟩
  have hshallow : negativeDigit expansion N i = true :=
    (hoccurs.2 ⟨i, by omega⟩).trans hcurrent
  have hdeep : negativeDigit expansion N (i + 1) = true :=
    (hoccurs.2 ⟨i + 1, hi⟩).trans hnext
  have hfalse := negative_digit_succ_eq_false_of_eq_true expansion N i hdeep
  exact Bool.false_ne_true (hfalse.symm.trans hshallow)

/-- Admissibility is exactly nonemptiness of the occurrence set. -/
theorem admissible_negative_prefix_iff_occurrence_set_nonempty
    (expansion : BasePhiNegativeExpansion) (w : List Bool) :
    AdmissibleNegativePrefix expansion w ↔ (occurrenceSet expansion w).Nonempty := by
  rfl

/-- The one-digit prefixes cover exactly the positive expansions reaching depth one. -/
theorem single_digit_occurrence_sets_union (expansion : BasePhiNegativeExpansion) :
    occurrenceSet expansion [false] ∪ occurrenceSet expansion [true] =
      {N | 0 < N ∧ reachesNegativeDepth expansion N 1} := by
  ext N
  simp [occurrenceSet, NegativePrefixOccurs]
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.1⟩
    · exact ⟨h.1, h.2.1⟩
  · intro h
    cases hdigit : negativeDigit expansion N 0 with
    | false => exact Or.inl ⟨h.1, h.2, rfl⟩
    | true => exact Or.inr ⟨h.1, h.2, rfl⟩

/-- The one-digit negative-prefix occurrence sets are disjoint. -/
theorem single_digit_occurrence_sets_disjoint (expansion : BasePhiNegativeExpansion) :
    Disjoint (occurrenceSet expansion [false]) (occurrenceSet expansion [true]) := by
  rw [Set.disjoint_left]
  intro N hfalse htrue
  simp [occurrenceSet, NegativePrefixOccurs] at hfalse htrue
  simp_all

end D5.S1.Words.Expansions.BasePhiNegative
