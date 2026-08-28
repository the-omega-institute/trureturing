/- GID: D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/LocalReciprocityMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Odd-prime reciprocity readings separate rows and columns, including zero cases. -/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Current-tree searches for `legendreSym`, `jacobiSym`, and `quadraticChar` found eleven
     files, not the four reported in the brief. The four named golden/Fibonacci files are
     specialized. `AllPrimeSplittingProfileNoninjectivity` concerns unequal forms with one
     discriminant, so it does not define the prime-by-discriminant matrix or its two axes.
   * Pinned Mathlib exact hits `legendreSym.eq_zero_iff`, `eq_one_iff`,
     `eq_neg_one_iff`, and `eq_one_or_neg_one` supply the three-valued semantics.
     `jacobiSym.eq_zero_iff_not_coprime` supplies the composite-index counterexample.
   * `legendreSym.quadratic_reciprocity_one_mod_four` is applied in the main separation
     theorem. `ZMod.exists_sq_eq_neg_one_iff` was found but is not needed here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.LocalReciprocityMatrix

/-- The observer indices are odd natural primes. -/
abbrev OddPrime := {p : Nat // p.Prime ∧ p ≠ 2}

/-- Discriminant coordinates are represented by integers, including degenerate values. -/
abbrev Discriminant := Int

/-- The local reciprocity matrix entry `(Delta / p)` at an odd prime. -/
def localReciprocityMatrix (p : OddPrime) (delta : Discriminant) : Int :=
  letI : Fact p.1.Prime := ⟨p.2.1⟩
  legendreSym p.1 delta

/-- A fixed prime reads the discriminant coordinate. -/
def primeObservesDiscriminants (p : OddPrime) : Discriminant → Int :=
  fun delta => localReciprocityMatrix p delta

/-- A fixed discriminant reads the odd-prime coordinate. -/
def discriminantObservesPrimes (delta : Discriminant) : OddPrime → Int :=
  fun p => localReciprocityMatrix p delta

/-- Two discriminants are indistinguishable to one fixed prime. -/
def SameAtPrime (p : OddPrime) (deltaOne deltaTwo : Discriminant) : Prop :=
  primeObservesDiscriminants p deltaOne = primeObservesDiscriminants p deltaTwo

/-- Two primes are indistinguishable to one fixed discriminant. -/
def SameAtDiscriminant (delta : Discriminant) (pOne pTwo : OddPrime) : Prop :=
  discriminantObservesPrimes delta pOne = discriminantObservesPrimes delta pTwo

/-- The matrix entry has the split value `1`. -/
def IsSplitAt (p : OddPrime) (delta : Discriminant) : Prop :=
  localReciprocityMatrix p delta = 1

/-- The matrix entry has the inert value `-1`. -/
def IsInertAt (p : OddPrime) (delta : Discriminant) : Prop :=
  localReciprocityMatrix p delta = -1

/-- The matrix entry has the ramified value `0`. -/
def IsRamifiedAt (p : OddPrime) (delta : Discriminant) : Prop :=
  localReciprocityMatrix p delta = 0

instance (p : OddPrime) (delta : Discriminant) : Decidable (IsSplitAt p delta) := by
  unfold IsSplitAt
  infer_instance

instance (p : OddPrime) (delta : Discriminant) : Decidable (IsInertAt p delta) := by
  unfold IsInertAt
  infer_instance

instance (p : OddPrime) (delta : Discriminant) : Decidable (IsRamifiedAt p delta) := by
  unfold IsRamifiedAt
  infer_instance

/-- Every local reciprocity entry is `-1`, `0`, or `1`. -/
theorem local_reciprocity_value_trichotomy (p : OddPrime) (delta : Discriminant) :
    localReciprocityMatrix p delta = -1 ∨
      localReciprocityMatrix p delta = 0 ∨
        localReciprocityMatrix p delta = 1 := by
  letI : Fact p.1.Prime := ⟨p.2.1⟩
  change legendreSym p.1 delta = -1 ∨
    legendreSym p.1 delta = 0 ∨ legendreSym p.1 delta = 1
  by_cases hzero : (delta : ZMod p.1) = 0
  · exact Or.inr <| Or.inl <| (legendreSym.eq_zero_iff p.1 delta).2 hzero
  · rcases legendreSym.eq_one_or_neg_one p.1 hzero with hone | hneg
    · exact Or.inr <| Or.inr hone
    · exact Or.inl hneg

#print axioms local_reciprocity_value_trichotomy

/-- Split means that the discriminant is a nonzero square modulo the fixed prime. -/
theorem split_iff_nonzero_square_mod_prime (p : OddPrime) (delta : Discriminant) :
    IsSplitAt p delta ↔
      (delta : ZMod p.1) ≠ 0 ∧ IsSquare (delta : ZMod p.1) := by
  letI : Fact p.1.Prime := ⟨p.2.1⟩
  change legendreSym p.1 delta = 1 ↔
    (delta : ZMod p.1) ≠ 0 ∧ IsSquare (delta : ZMod p.1)
  constructor
  · intro hone
    have hnonzero : (delta : ZMod p.1) ≠ 0 := by
      intro hzero
      have hsymbolZero := (legendreSym.eq_zero_iff p.1 delta).2 hzero
      omega
    exact ⟨hnonzero, (legendreSym.eq_one_iff p.1 hnonzero).1 hone⟩
  · rintro ⟨hnonzero, hsquare⟩
    exact (legendreSym.eq_one_iff p.1 hnonzero).2 hsquare

#print axioms split_iff_nonzero_square_mod_prime

/-- Inert means that the discriminant is not a square modulo the fixed prime. -/
theorem inert_iff_nonsquare_mod_prime (p : OddPrime) (delta : Discriminant) :
    IsInertAt p delta ↔ ¬IsSquare (delta : ZMod p.1) := by
  letI : Fact p.1.Prime := ⟨p.2.1⟩
  change legendreSym p.1 delta = -1 ↔ ¬IsSquare (delta : ZMod p.1)
  exact legendreSym.eq_neg_one_iff p.1

#print axioms inert_iff_nonsquare_mod_prime

/-- Ramified means exactly that the fixed prime divides the discriminant. -/
theorem ramified_iff_prime_dvd_discriminant (p : OddPrime) (delta : Discriminant) :
    IsRamifiedAt p delta ↔ (p.1 : Int) ∣ delta := by
  letI : Fact p.1.Prime := ⟨p.2.1⟩
  change legendreSym p.1 delta = 0 ↔ (p.1 : Int) ∣ delta
  rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

#print axioms ramified_iff_prime_dvd_discriminant

/-- The concrete odd prime three. -/
def oddPrimeThree : OddPrime := ⟨3, by norm_num, by norm_num⟩

/-- The concrete odd prime five. -/
def oddPrimeFive : OddPrime := ⟨5, by norm_num, by norm_num⟩

/-- The concrete odd prime seven. -/
def oddPrimeSeven : OddPrime := ⟨7, by norm_num, by norm_num⟩

/-- The concrete odd prime thirteen. -/
def oddPrimeThirteen : OddPrime := ⟨13, by norm_num, by norm_num⟩

/-- The concrete discriminant coordinate five. -/
def discriminantFive : Discriminant := 5

/-- The concrete discriminant coordinate eight. -/
def discriminantEight : Discriminant := 8

/-- The concrete discriminant coordinate thirteen. -/
def discriminantThirteen : Discriminant := 13

/-- At the fixed prime three, the distinct discriminants five and eight collide. -/
theorem row_reading_collision_at_three :
    discriminantFive ≠ discriminantEight ∧
      SameAtPrime oddPrimeThree discriminantFive discriminantEight := by
  norm_num [SameAtPrime, primeObservesDiscriminants, localReciprocityMatrix,
    oddPrimeThree, discriminantFive, discriminantEight]

#print axioms row_reading_collision_at_three

/-- At the fixed discriminant five, the distinct primes three and seven collide. -/
theorem column_reading_collision_at_five :
    oddPrimeThree ≠ oddPrimeSeven ∧
      SameAtDiscriminant discriminantFive oddPrimeThree oddPrimeSeven := by
  norm_num [SameAtDiscriminant, discriminantObservesPrimes, localReciprocityMatrix,
    oddPrimeThree, oddPrimeSeven, discriminantFive]

#print axioms column_reading_collision_at_five

/-- A reciprocal transposed cell can agree while row and column indistinguishability differ. -/
theorem reciprocity_does_not_identify_reading_directions :
    localReciprocityMatrix oddPrimeFive discriminantThirteen =
      localReciprocityMatrix oddPrimeThirteen discriminantFive ∧
    SameAtPrime oddPrimeThree discriminantFive discriminantEight ∧
    ¬SameAtDiscriminant discriminantFive oddPrimeThree oddPrimeFive := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine ⟨?_, row_reading_collision_at_three.2, ?_⟩
  · simpa [localReciprocityMatrix, oddPrimeFive, oddPrimeThirteen,
      discriminantFive, discriminantThirteen] using
      (legendreSym.quadratic_reciprocity_one_mod_four
        (p := 5) (q := 13) (by norm_num) (by norm_num)).symm
  · norm_num [SameAtDiscriminant, discriminantObservesPrimes,
      localReciprocityMatrix, oddPrimeThree, oddPrimeFive, discriminantFive]

#print axioms reciprocity_does_not_identify_reading_directions

/-- Zero, one, and square discriminants exhibit the expected degenerate readings. -/
theorem discriminant_degeneracy_audit :
    (∀ p : OddPrime, IsRamifiedAt p 0 ∧ IsSplitAt p 1) ∧
      IsSplitAt oddPrimeThree 4 ∧ IsRamifiedAt oddPrimeThree 9 := by
  constructor
  · intro p
    constructor
    · exact (ramified_iff_prime_dvd_discriminant p 0).2 (dvd_zero _)
    · letI : Fact p.1.Prime := ⟨p.2.1⟩
      exact legendreSym.at_one p.1
  · norm_num [IsSplitAt, IsRamifiedAt, localReciprocityMatrix, oddPrimeThree]

#print axioms discriminant_degeneracy_audit

/-- At the composite index nine, Jacobi ramification does not mean divisibility by nine. -/
theorem primality_is_necessary_for_ramified_iff :
    jacobiSym 3 9 = 0 ∧ ¬(9 : Int) ∣ 3 := by
  constructor
  · haveI : NeZero 9 := ⟨by norm_num⟩
    rw [jacobiSym.eq_zero_iff_not_coprime]
    norm_num
  · norm_num

#print axioms primality_is_necessary_for_ramified_iff

/-- At the prime two, the Legendre symbol never has the inert value `-1`. -/
theorem oddness_is_necessary_for_inert_value :
    ∀ delta : Int, legendreSym 2 delta ≠ -1 := by
  intro delta
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hzero : (delta : ZMod 2) = 0
  · rw [(legendreSym.eq_zero_iff 2 delta).2 hzero]
    norm_num
  · have hone : legendreSym 2 delta = 1 := by
      simpa [legendreSym] using
        (quadraticChar_eq_one_of_char_two (ZMod.ringChar_zmod_n 2) hzero)
    rw [hone]
    norm_num

#print axioms oddness_is_necessary_for_inert_value

/- Assumption and degeneracy audit:
   * Primality is load-bearing: `localReciprocityMatrix` constructs the `Fact p.Prime`
     instance required by `legendreSym`, and the three semantic proofs use its prime lemmas.
     The named composite-nine Jacobi theorem shows that the ramified iff divisibility law
     fails for the total composite extension.
   * `p ≠ 2` is not used by the value or divisibility proofs. It is retained in the index
     space because the prime-two symbol never realizes inert, as the named theorem proves.
   * Delta zero and one give constant ramified and split columns. Squares four and nine show
     both the coprime split case and the divisible ramified case. These cover the zero,
     one, square, constant-map, and `n = 0` audits.
   * The carriers are the fixed nonempty types `OddPrime` and `Int`; empty/singleton carrier
     tests and identity-map tests are inapplicable. No unused theorem hypothesis remains. -/

end D5.S3.PrimeForms.Splitting.LocalReciprocityMatrix
