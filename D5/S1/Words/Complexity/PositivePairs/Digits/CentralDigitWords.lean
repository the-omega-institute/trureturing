/- GID: D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Direction-major and scale-minor digits build literal positive words. -/

import D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
import D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords

open scoped BigOperators
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution
open D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections

variable {A : Type*}

def digitBase (r : ℕ) : ℕ := 2 ^ r

private def zeroDigit (r : ℕ) : Fin (digitBase r) :=
  ⟨0, by simp [digitBase]⟩

/-- A complete digit array: one base-`2^r` digit for every selected direction
and every scale below `t`. -/
abbrev DigitArray [Fintype A] [LinearOrder A] (r t : ℕ) :=
  Fin (actualLyndonCount (A := A) r) → Fin t → Fin (digitBase r)

/-- The base-`2^r` natural encoded by one direction's scale digits. -/
noncomputable def digitValue [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t)
    (direction : Fin (actualLyndonCount (A := A) r)) : ℕ :=
  Nat.ofDigits (digitBase r)
    (List.ofFn fun scale : Fin t ↦ (digits direction scale : ℕ))

private def repeatedWord (count : ℕ) (word : List A) : List A :=
  (List.replicate count word).flatten

/-- One actual digit block: `j` powered copies of `u`, then the remaining
`2^r-1-j` powered copies of `v`. -/
noncomputable def digitBlock [Fintype A] [LinearOrder A] (r : ℕ)
    (direction : Fin (actualLyndonCount (A := A) r)) (scale digit : ℕ) : List A :=
  let pair := positivePairWords r (selectedDirection (A := A) r direction)
  let poweredU := literalPowerWord (2 ^ scale) pair.1
  let poweredV := literalPowerWord (2 ^ scale) pair.2
  repeatedWord digit poweredU ++
    repeatedWord (digitBase r - 1 - digit) poweredV

/-- Deterministic direction-major, scale-minor concatenation of all actual
digit blocks.  For `t=0` both index lists are empty, so the result is `[]`. -/
noncomputable def multiScaleWord [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t) : List A :=
  (List.ofFn fun direction : Fin (actualLyndonCount (A := A) r) ↦
    (List.ofFn fun scale : Fin t ↦
      digitBlock (A := A) r direction scale (digits direction scale)).flatten).flatten

private noncomputable def directionWord [Fintype A] [LinearOrder A]
    (r t : ℕ) (digits : DigitArray (A := A) r t)
    (direction : Fin (actualLyndonCount (A := A) r)) : List A :=
  (List.ofFn fun scale : Fin t ↦
    digitBlock (A := A) r direction scale (digits direction scale)).flatten

/-- The all-`v` reference is the zero digit array. -/
noncomputable def referenceWord [Fintype A] [LinearOrder A] (r t : ℕ) : List A :=
  multiScaleWord (A := A) r t (fun _ _ ↦ zeroDigit r)

/-- The fixed length coefficient appearing in the common length law. -/
noncomputable def baseLength [Fintype A] [LinearOrder A] (r : ℕ) : ℕ :=
  (digitBase r - 1) *
    ∑ i : Fin (actualLyndonCount (A := A) r),
      (positivePairWords r (selectedDirection (A := A) r i)).1.length

private noncomputable def rationalMagnus (source : List A) :
    RationalWordPolynomial A :=
  toRationalWordPolynomial (magnusPolynomial source)

private def AgreesBelow (r : ℕ) (left right : List A) : Prop :=
  ∀ pattern : List A, pattern.length < r →
    (rationalMagnus left).coeff (FreeMonoid.ofList pattern) =
      (rationalMagnus right).coeff (FreeMonoid.ofList pattern)

private theorem agreesBelow_append_and_degree_add
    (r : ℕ) {u u0 v v0 : List A}
    (hu : AgreesBelow r u u0) (hv : AgreesBelow r v v0) :
    AgreesBelow r (u ++ v) (u0 ++ v0) ∧
      ∀ pattern : List A, pattern.length = r →
        (rationalMagnus (u ++ v)).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus (u0 ++ v0)).coeff (FreeMonoid.ofList pattern) =
          ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)) +
          ((rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)) := by
  classical
  let centralWordSplits (w : FreeMonoid A) :
      Finset (FreeMonoid A × FreeMonoid A) :=
    (Finset.range (FreeMonoid.length w + 1)).image fun i ↦
      (FreeMonoid.ofList ((FreeMonoid.toList w).take i),
        FreeMonoid.ofList ((FreeMonoid.toList w).drop i))
  have mem_centralWordSplits_iff
      (w : FreeMonoid A) (pair : FreeMonoid A × FreeMonoid A) :
      pair ∈ centralWordSplits w ↔ pair.1 * pair.2 = w := by
    change pair ∈ (Finset.range (FreeMonoid.length w + 1)).image
        (fun i ↦
          (FreeMonoid.ofList ((FreeMonoid.toList w).take i),
            FreeMonoid.ofList ((FreeMonoid.toList w).drop i))) ↔ _
    constructor
    · intro hpair
      rcases Finset.mem_image.mp hpair with ⟨i, _, rfl⟩
      apply FreeMonoid.toList.injective
      simp [List.take_append_drop]
    · intro hpair
      apply Finset.mem_image.mpr
      refine ⟨FreeMonoid.length pair.1, ?_, ?_⟩
      · rw [Finset.mem_range, ← hpair, FreeMonoid.length_mul]
        omega
      · apply Prod.ext
        · apply FreeMonoid.toList.injective
          have hlist := congrArg FreeMonoid.toList hpair
          simpa [FreeMonoid.toList_mul, FreeMonoid.length,
            List.take_append_of_le_length] using
            congrArg (List.take (FreeMonoid.length pair.1)) hlist.symm
        · apply FreeMonoid.toList.injective
          have hlist := congrArg FreeMonoid.toList hpair
          simpa [FreeMonoid.toList_mul, FreeMonoid.length,
            List.drop_append_of_le_length] using
            congrArg (List.drop (FreeMonoid.length pair.1)) hlist.symm
  have central_coeff_mul_eq_split_sum
      (p q : RationalWordPolynomial A) (w : FreeMonoid A) :
      (p * q).coeff w =
        ∑ i ∈ Finset.range (FreeMonoid.length w + 1),
          p.coeff (FreeMonoid.ofList ((FreeMonoid.toList w).take i)) *
            q.coeff (FreeMonoid.ofList ((FreeMonoid.toList w).drop i)) := by
    rw [MonoidAlgebra.coeff_mul_antidiag p q w (centralWordSplits w)
      (fun {pair} ↦ mem_centralWordSplits_iff w pair)]
    dsimp only [centralWordSplits]
    rw [Finset.sum_image]
    intro i hi j hj hij
    have hi' : i ≤ FreeMonoid.length w := by
      have : i < FreeMonoid.length w + 1 := by simpa using hi
      omega
    have hj' : j ≤ FreeMonoid.length w := by
      have : j < FreeMonoid.length w + 1 := by simpa using hj
      omega
    have hi'' : i ≤ (FreeMonoid.toList w).length := by
      simpa [FreeMonoid.length] using hi'
    have hj'' : j ≤ (FreeMonoid.toList w).length := by
      simpa [FreeMonoid.length] using hj'
    have hlength := congrArg (fun pair : FreeMonoid A × FreeMonoid A ↦
      FreeMonoid.length pair.1) hij
    simpa [FreeMonoid.length, List.length_take, Nat.min_eq_left hi'',
      Nat.min_eq_left hj''] using hlength
  have magnusAppend (left right : List A) :
      rationalMagnus (left ++ right) =
        rationalMagnus left * rationalMagnus right := by
    simp [rationalMagnus, magnusPolynomial_append]
  have coeffEmpty (source : List A) : (rationalMagnus source).coeff 1 = 1 := by
    have hcount :
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          [] source = 1 := by
      induction source with
      | nil => rfl
      | cons a source ih => simpa [
          D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount] using ih
    rw [show (1 : FreeMonoid A) = FreeMonoid.ofList [] by rfl]
    change (Int.castRingHom ℚ)
        ((magnusPolynomial source).coeff (FreeMonoid.ofList [])) = 1
    rw [magnusPolynomial_coeff_scatteredCount]
    norm_num [hcount]
  constructor
  · intro pattern hp
    simp only [magnusAppend, central_coeff_mul_eq_split_sum,
      FreeMonoid.length, FreeMonoid.toList_ofList]
    apply Finset.sum_congr rfl
    intro i hi
    have htake : (pattern.take i).length < r :=
      lt_of_le_of_lt (List.length_take_le' i pattern) hp
    have hdrop : (pattern.drop i).length < r := by
      rw [List.length_drop]
      omega
    rw [hu _ htake, hv _ hdrop]
  · intro pattern hp
    simp only [magnusAppend, central_coeff_mul_eq_split_sum,
      FreeMonoid.length, FreeMonoid.toList_ofList, ← Finset.sum_sub_distrib]
    calc
      ∑ i ∈ Finset.range (pattern.length + 1),
          ((rationalMagnus u).coeff (FreeMonoid.ofList (pattern.take i)) *
              (rationalMagnus v).coeff (FreeMonoid.ofList (pattern.drop i)) -
            (rationalMagnus u0).coeff (FreeMonoid.ofList (pattern.take i)) *
              (rationalMagnus v0).coeff (FreeMonoid.ofList (pattern.drop i))) =
          ∑ i ∈ Finset.range (pattern.length + 1),
            (if i = 0 then
              (rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)
            else if i = pattern.length then
              (rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)
            else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hi0 : i = 0
              · subst i
                simp [coeffEmpty]
              · by_cases hilast : i = pattern.length
                · subst i
                  simp [hi0, coeffEmpty]
                · have hiLt : i < r := by
                    have : i < pattern.length + 1 := Finset.mem_range.mp hi
                    omega
                  have htake : (pattern.take i).length < r := by
                    rw [List.length_take, hp, Nat.min_eq_left (Nat.le_of_lt hiLt)]
                    exact hiLt
                  have hdrop : (pattern.drop i).length < r := by
                    rw [List.length_drop, hp]
                    omega
                  rw [hu _ htake, hv _ hdrop, if_neg hi0, if_neg hilast]
                  ring
      _ = ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)) +
          ((rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)) := by
            by_cases hempty : pattern = []
            · subst pattern
              simp [coeffEmpty]
            · have hn : pattern.length ≠ 0 := by
                intro hzero
                exact hempty (List.eq_nil_of_length_eq_zero hzero)
              let summand := fun i : ℕ ↦
                if i = 0 then
                  (rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
                    (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)
                else if i = pattern.length then
                  (rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                    (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)
                else 0
              have hzero : 0 ∈ Finset.range (pattern.length + 1) := by simp
              have hlast : pattern.length ∈
                  (Finset.range (pattern.length + 1)).erase 0 := by
                exact Finset.mem_erase.mpr ⟨hn, by simp⟩
              have hrest :
                  ∑ i ∈ ((Finset.range (pattern.length + 1)).erase 0).erase
                      pattern.length, summand i = 0 := by
                apply Finset.sum_eq_zero
                intro i hi
                have hiLast : i ≠ pattern.length := (Finset.mem_erase.mp hi).1
                have hi0 : i ≠ 0 :=
                  (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
                simp [summand, hi0, hiLast]
              change ∑ i ∈ Finset.range (pattern.length + 1), summand i = _
              rw [← Finset.sum_erase_add _ summand hzero,
                ← Finset.sum_erase_add _ summand hlast, hrest]
              simp [summand, hn]

private theorem repeatedWord_central_data
    (r n : ℕ) {u v : List A} (hu : AgreesBelow r u v) :
    AgreesBelow r (repeatedWord n u) (repeatedWord n v) ∧
      ∀ pattern : List A, pattern.length = r →
        (rationalMagnus (repeatedWord n u)).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus (repeatedWord n v)).coeff (FreeMonoid.ofList pattern) =
          (n : ℚ) *
            ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
              (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) := by
  classical
  induction n with
  | zero =>
      constructor
      · intro pattern _
        rfl
      · intro pattern _
        simp [repeatedWord]
  | succ n ih =>
      have happ := agreesBelow_append_and_degree_add r hu ih.1
      constructor
      · simpa [repeatedWord, List.replicate_succ] using happ.1
      · intro pattern hp
        have hdegree := happ.2 pattern hp
        rw [ih.2 pattern hp] at hdegree
        change
          (rationalMagnus (u ++ repeatedWord n u)).coeff
                (FreeMonoid.ofList pattern) -
              (rationalMagnus (v ++ repeatedWord n v)).coeff
                (FreeMonoid.ofList pattern) =
            ((n + 1 : ℕ) : ℚ) *
              ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern))
        calc
          _ = ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) +
              (n : ℚ) * ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) := hdegree
          _ = ((n + 1 : ℕ) : ℚ) *
              ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) := by
                push_cast
                ring


end D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords
