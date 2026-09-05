/- GID: D5/S1/Digit/GoldenBase4AutomataOracle
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4AutomataOracle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical Zeckendorf words and exact floor differences define the base-four golden-ratio DFAO specification. -/

import D5.S0.Automata.TypedSampleIdentification
import D5.S1.Digit.Addition
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Real.GoldenRatio

/- Library-search audit trail (2026-09-02):
   * `D5.S0.Conventions.WDigits` already identifies canonical W strings with
     Mathlib's `Nat.zeckendorfEquiv`.
   * `D5.S1.Digit.Addition` already provides canonical raw coordinates and exact
     decoding of `Z n`; no second Zeckendorf implementation is introduced.
   * `D5.S0.Automata.TypedSampleIdentification` supplies the typed sparse-sample
     and finite-coloring obstruction layer.
   * Repository searches found no exact base-four digit oracle for the golden
     ratio and no specialization of the finite obstruction theorem to powers
     of four. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4AutomataOracle

open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.TypedSampleIdentification
open D5.S0.Conventions

/-- The two states of the canonical Zeckendorf validity automaton. -/
inductive ZeckendorfBaseState
  | clear
  | previousOne
  deriving DecidableEq

instance : Fintype ZeckendorfBaseState where
  elems := {ZeckendorfBaseState.clear, ZeckendorfBaseState.previousOne}
  complete := by intro x; cases x <;> simp

/-- The partial Zeckendorf transition law: a one may follow a clear state, and
only a zero may follow a previous one. -/
def zeckendorfBaseStep :
    ZeckendorfBaseState -> Fin 2 -> Option ZeckendorfBaseState
  | .clear, symbol =>
      if symbol = 0 then some .clear else some .previousOne
  | .previousOne, symbol =>
      if symbol = 0 then some .clear else none

/-- The canonical most-significant-digit-first Zeckendorf base automaton. -/
def zeckendorfBase : PartialBaseAutomaton (Fin 2) ZeckendorfBaseState where
  start := .clear
  step := zeckendorfBaseStep

/-- Number of dense zero-based bits needed to display Mathlib's descending
Fibonacci-index representation. Zero is represented by one zero bit. -/
def zeckendorfWordLength (n : Nat) : Nat :=
  match wdigits n with
  | [] => 1
  | largest :: _ => largest - 1

/-- The zero-based W bit at a raw digit index. -/
def zeckendorfBit (n rawIndex : Nat) : Fin 2 :=
  if rawIndex + 2 ∈ wdigits n then 1 else 0

/-- Dense most-significant-digit-first Zeckendorf word, obtained directly from
the canonical occupied indices in `wdigits`. -/
def zeckendorfMSDWord (n : Nat) : List (Fin 2) :=
  (List.range (zeckendorfWordLength n)).reverse.map (zeckendorfBit n)

@[simp] theorem length_zeckendorfMSDWord (n : Nat) :
    (zeckendorfMSDWord n).length = zeckendorfWordLength n := by
  simp [zeckendorfMSDWord]

/-- The sparse input word used for the `i`th base-four digit. -/
def base4PowerWord (i : Nat) : List (Fin 2) :=
  zeckendorfMSDWord (4 ^ i)

/-- Exact integer part of `4^i * phi`. -/
noncomputable def base4Floor (i : Nat) : Int :=
  ⌊(4 : Real) ^ i * Real.goldenRatio⌋

/-- Exact floor difference defining the `i`th base-four digit of the golden
ratio. -/
noncomputable def base4DigitInt (i : Nat) : Int :=
  base4Floor (i + 1) - 4 * base4Floor i

private theorem floor_radix_digit_bounds
    (base : Nat) (base_pos : 0 < base) (x : Real) :
    0 <= ⌊(base : Real) * x⌋ - (base : Int) * ⌊x⌋ ∧
      ⌊(base : Real) * x⌋ - (base : Int) * ⌊x⌋ < (base : Int) := by
  have lower :
      (base : Int) * ⌊x⌋ <= ⌊(base : Real) * x⌋ := by
    rw [Int.le_floor]
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le x)
      (Nat.cast_nonneg base)
  have upper :
      ⌊(base : Real) * x⌋ <
        (base : Int) * ⌊x⌋ + (base : Int) := by
    rw [Int.floor_lt]
    push_cast
    have floor_gap := Int.lt_floor_add_one x
    have base_real_pos : (0 : Real) < base := by
      exact_mod_cast base_pos
    nlinarith [mul_lt_mul_of_pos_left floor_gap base_real_pos]
  constructor <;> omega

/-- The exact floor difference is always one of `0,1,2,3`. -/
theorem base4DigitInt_bounds (i : Nat) :
    0 <= base4DigitInt i ∧ base4DigitInt i < 4 := by
  let x : Real := (4 : Real) ^ i * Real.goldenRatio
  have next_floor : base4Floor (i + 1) = ⌊(4 : Real) * x⌋ := by
    change ⌊(4 : Real) ^ (i + 1) * Real.goldenRatio⌋ =
      ⌊(4 : Real) * x⌋
    congr 1
    dsimp [x]
    rw [pow_succ]
    ring
  have current_floor : base4Floor i = ⌊x⌋ := by
    rfl
  rw [base4DigitInt, next_floor, current_floor]
  exact floor_radix_digit_bounds 4 (by decide) x

/-- The exact base-four digit as an element of the four-symbol output alphabet. -/
noncomputable def base4GoldenDigit (i : Nat) : Fin 4 :=
  ⟨(base4DigitInt i).toNat, by
    rw [Int.toNat_lt (base4DigitInt_bounds i).1]
    exact (base4DigitInt_bounds i).2⟩

@[simp] theorem base4GoldenDigit_val (i : Nat) :
    (base4GoldenDigit i : Nat) = (base4DigitInt i).toNat := rfl

/-- Successive floors decompose into radix-four quotient and exact digit. -/
theorem base4_floor_succ_decomposition (i : Nat) :
    base4Floor (i + 1) =
      4 * base4Floor i + ((base4GoldenDigit i : Nat) : Int) := by
  have nonnegative := (base4DigitInt_bounds i).1
  rw [base4GoldenDigit_val, Int.toNat_of_nonneg nonnegative]
  unfold base4DigitInt
  omega

/-- The complete sparse specification: read the Zeckendorf representation of
`4^i` and emit the `i`th exact base-four digit of the golden ratio. -/
noncomputable def base4GoldenSpecification :
    LabeledSample (Fin 2) (Fin 4) Nat where
  word := base4PowerWord
  label := base4GoldenDigit

/-- The first `count` inputs of the complete sparse specification. -/
noncomputable def base4GoldenPrefixSample (count : Nat) :
    LabeledSample (Fin 2) (Fin 4) (Fin count) :=
  base4GoldenSpecification.reindex fun i => i.1

/-- Global correctness immediately restricts to every finite prefix sample. -/
theorem global_correctness_implies_prefix_correctness
    {State : Type*}
    (machine : TypedDFAO zeckendorfBase (Fin 4) State)
    (correct : machine.Fits base4GoldenSpecification)
    (count : Nat) :
    machine.Fits (base4GoldenPrefixSample count) :=
  TypedDFAO.fits_reindex machine base4GoldenSpecification
    (fun i : Fin count => i.1) correct

/-- A finite typed-model obstruction at every size at most `k` on some prefix
sample proves a strict global state lower bound for every typed machine that
computes the base-four golden-ratio specification. -/
theorem base4_state_lower_bound_of_finite_obstruction
    (count k : Nat)
    (obstruction : ∀ n, n ≤ k →
      FiniteTypedModel zeckendorfBase (base4GoldenPrefixSample count) n →
        False)
    {State : Type*} [Fintype State]
    (machine : TypedDFAO zeckendorfBase (Fin 4) State)
    (global_correct : machine.Fits base4GoldenSpecification) :
    k < Fintype.card State :=
  no_small_model_implies_state_lower_bound
    (base4GoldenPrefixSample count) k obstruction machine
    (global_correctness_implies_prefix_correctness machine global_correct count)

#print axioms base4DigitInt_bounds
#print axioms base4_floor_succ_decomposition
#print axioms base4_state_lower_bound_of_finite_obstruction

end D5.S1.Digit.GoldenBase4AutomataOracle
