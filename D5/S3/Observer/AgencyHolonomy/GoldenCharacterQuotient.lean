/- GID: D5/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient
   generality: I
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden quadratic character gives the binary quotient of unramified prime words. -/

import D5.S3.Arith.Lattices.RamifiedFiveBoundarySelection
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol

/- Library-search audit trail (2026-09-01):
   * Repository searches for `gpmo`, `legendreSym 5`, quadratic-character names,
     prime-word products, permutation invariance, inert-prime counts, and binary orientation
     found no theorem combining the source's unramified word quotient and parity formula.
     `ModFiveOrientationBit` is explicitly non-homomorphic; `ModFiveObserverDiagonalization`
     has an analytic carrier; and `PrimeWordOccupationDescent` is character-independent.
   * The exact repository theorem `ramified_five_boundary_selection` supplies
     `legendreSym 5 p = 0 <-> p = 5` for primes and is applied directly.
   * Pinned Mathlib exact hits `legendreSym.mul`, `legendreSym.eq_one_or_neg_one`,
     `List.prod_append`, `List.Perm.prod_eq`, and `List.countP_cons` supply the standard steps.
     Loogle confirmed `List.Perm.prod_eq`; LeanSearch returned no response for the parity query.
   * Searches of the installed non-Mathlib Lean packages found no Legendre-symbol declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.GoldenCharacterQuotient

open D5.S3.Arith.Lattices.RamifiedFiveBoundarySelection

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Rational primes away from the discriminant prime five. -/
def UnramifiedPrime := {p : Nat // p.Prime ∧ p ≠ 5}

/-- The quadratic character modulo five on an unramified rational prime. -/
def goldenCharacter (p : UnramifiedPrime) : Int :=
  legendreSym 5 p.1

/-- The product of the golden characters along an ordered prime word. -/
def holFive (word : List UnramifiedPrime) : Int :=
  (word.map goldenCharacter).prod

/-- The number of inert letters in an unramified prime word. -/
def inertCount (word : List UnramifiedPrime) : Nat :=
  word.countP fun p => decide (goldenCharacter p = -1)

/-- The integer represented by multiplying the letters of a prime word. -/
def primeWordValue (word : List UnramifiedPrime) : Int :=
  (word.map fun p => (p.1 : Int)).prod

/-- The golden character of an unramified prime is nonzero. -/
theorem goldenCharacter_ne_zero (p : UnramifiedPrime) : goldenCharacter p ≠ 0 := by
  intro hzero
  exact p.property.2
    ((ramified_five_boundary_selection.2.2.1 p.1 p.property.1).1 hzero)

/-- Every unramified golden character value is one or negative one. -/
theorem goldenCharacter_eq_one_or_neg_one (p : UnramifiedPrime) :
    goldenCharacter p = 1 ∨ goldenCharacter p = -1 := by
  have hresidue : ((p.1 : Int) : ZMod 5) ≠ 0 := by
    intro hzero
    apply goldenCharacter_ne_zero p
    exact (legendreSym.eq_zero_iff 5 (p.1 : Int)).2 hzero
  simpa [goldenCharacter] using
    (legendreSym.eq_one_or_neg_one (p := 5) (a := (p.1 : Int)) hresidue)

/-- Concatenation of words becomes multiplication in the golden quotient. -/
theorem holFive_append (first second : List UnramifiedPrime) :
    holFive (first ++ second) = holFive first * holFive second := by
  simp [holFive, List.prod_append]

/-- The golden quotient forgets the order of prime letters. -/
theorem holFive_perm {first second : List UnramifiedPrime}
    (permutation : List.Perm first second) : holFive first = holFive second := by
  exact (permutation.map goldenCharacter).prod_eq

/-- Multiplicativity of the Legendre symbol identifies the word product with one symbol. -/
theorem holFive_eq_legendreSym_primeWordValue (word : List UnramifiedPrime) :
    holFive word = legendreSym 5 (primeWordValue word) := by
  induction word with
  | nil => simp [holFive, primeWordValue]
  | cons p tail inductionHypothesis =>
      have htail : (tail.map goldenCharacter).prod =
          legendreSym 5 ((tail.map fun q => (q.1 : Int)).prod) := by
        simpa only [holFive, primeWordValue] using inductionHypothesis
      simp only [holFive, primeWordValue, List.map_cons, List.prod_cons, goldenCharacter]
      rw [htail, legendreSym.mul]

/-- The quotient remembers exactly the parity of the inert letters. -/
theorem holFive_eq_neg_one_pow_inertCount (word : List UnramifiedPrime) :
    holFive word = (-1 : Int) ^ inertCount word := by
  induction word with
  | nil => simp [holFive, inertCount]
  | cons p tail inductionHypothesis =>
      change (tail.map goldenCharacter).prod = (-1 : Int) ^ inertCount tail at inductionHypothesis
      rcases goldenCharacter_eq_one_or_neg_one p with hsplit | hinert
      · simp [holFive, inertCount, hsplit, inductionHypothesis]
      · simp [holFive, inertCount, hinert, inductionHypothesis, pow_succ, mul_comm]

/-- The two-element multiplicative target, represented by the units of the integers. -/
def goldenCharacterUnit (p : UnramifiedPrime) : Intˣ :=
  if goldenCharacter p = 1 then 1 else -1

@[simp] theorem goldenCharacterUnit_coe (p : UnramifiedPrime) :
    (goldenCharacterUnit p : Int) = goldenCharacter p := by
  rcases goldenCharacter_eq_one_or_neg_one p with hsplit | hinert
  · simp [goldenCharacterUnit, hsplit]
  · simp [goldenCharacterUnit, hinert]

/-- The canonical homomorphism from concatenated prime words to the binary quotient. -/
def holFiveQuotient : FreeMonoid UnramifiedPrime →* Intˣ :=
  FreeMonoid.lift goldenCharacterUnit

@[simp] theorem holFiveQuotient_coe (word : List UnramifiedPrime) :
    (holFiveQuotient (FreeMonoid.ofList word) : Int) = holFive word := by
  induction word with
  | nil => simp [holFiveQuotient, holFive]
  | cons p tail inductionHypothesis =>
      rw [show holFiveQuotient (FreeMonoid.ofList (p :: tail)) =
          goldenCharacterUnit p * holFiveQuotient (FreeMonoid.ofList tail) by
        simp [holFiveQuotient]]
      change (goldenCharacterUnit p : Int) *
          (holFiveQuotient (FreeMonoid.ofList tail) : Int) =
        goldenCharacter p * holFive tail
      rw [goldenCharacterUnit_coe, inductionHypothesis]

/-- The integer-valued holonomy has exactly the two possible orientation values. -/
theorem holFive_eq_one_or_neg_one (word : List UnramifiedPrime) :
    holFive word = 1 ∨ holFive word = -1 := by
  rcases Int.units_eq_one_or (holFiveQuotient (FreeMonoid.ofList word)) with hone | hneg
  · left
    rw [← holFiveQuotient_coe]
    simpa using congrArg (fun unit : Intˣ => (unit : Int)) hone
  · right
    rw [← holFiveQuotient_coe]
    simpa using congrArg (fun unit : Intˣ => (unit : Int)) hneg

def two : UnramifiedPrime := ⟨2, Nat.prime_two, by norm_num⟩

def three : UnramifiedPrime := ⟨3, Nat.prime_three, by norm_num⟩

def eleven : UnramifiedPrime := ⟨11, by norm_num, by norm_num⟩

def nineteen : UnramifiedPrime := ⟨19, by norm_num, by norm_num⟩

/-- Concrete split and inert values of the golden quadratic character. -/
theorem goldenCharacter_witness_values :
    goldenCharacter eleven = 1 ∧
      goldenCharacter nineteen = 1 ∧
      goldenCharacter two = -1 ∧
      goldenCharacter three = -1 := by
  norm_num [goldenCharacter, eleven, nineteen, two, three]

/-- Two inert letters give the identity, while one inert letter gives the nonidentity value. -/
theorem holFive_nontrivial_witnesses :
    holFive [two, three] = 1 ∧ holFive [two, eleven] = -1 := by
  norm_num [holFive, goldenCharacter, two, three, eleven]

/-- The self-contained content of the golden-character quotient: it is multiplicative,
order-independent, records inert-prime parity, lands in the two integer units, and is nontrivial. -/
theorem golden_character_quotient_spec :
    (∀ word : List UnramifiedPrime,
      (holFiveQuotient (FreeMonoid.ofList word) : Int) = holFive word) ∧
    (∀ first second : List UnramifiedPrime,
      holFive (first ++ second) = holFive first * holFive second) ∧
    (∀ first second : List UnramifiedPrime,
      List.Perm first second → holFive first = holFive second) ∧
    (∀ word : List UnramifiedPrime,
      holFive word = (-1 : Int) ^ inertCount word) ∧
    (∀ word : List UnramifiedPrime, holFive word = 1 ∨ holFive word = -1) ∧
    (goldenCharacter eleven = 1 ∧
      goldenCharacter nineteen = 1 ∧
      goldenCharacter two = -1 ∧
      goldenCharacter three = -1) ∧
    (holFive [two, three] = 1 ∧ holFive [two, eleven] = -1) := by
  exact ⟨holFiveQuotient_coe, holFive_append, fun _ _ => holFive_perm,
    holFive_eq_neg_one_pow_inertCount, holFive_eq_one_or_neg_one,
    goldenCharacter_witness_values, holFive_nontrivial_witnesses⟩

#print axioms golden_character_quotient_spec

end D5.S3.Observer.AgencyHolonomy.GoldenCharacterQuotient
