/- GID: D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Successor positive pairs have the actual leading commutator coefficients. -/

import D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairLeadingCoefficients

open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.VivionBinomialConverseFails

variable {A : Type*}

/-- In the successor cutoff, the actual full-family Magnus difference is the
commutator of the preceding leading difference with `ab(v) + X_a`.  Terms of
degree at least two in the two Magnus tails land beyond the cutoff. -/
theorem full_positivePair_successor_leading_bracket [Finite A] [DecidableEq A]
    (r : ℕ) (index : PositivePairIndex A (r + 2)) :
    let previous := positivePairWords (r + 1) (Fin.init index)
    let a := index (Fin.last (r + 1))
    let c := cutoffMagnus (r + 2) previous.1 -
      cutoffMagnus (r + 2) previous.2
    let x := cutoffRestriction (r + 2) <|
      toRationalWordPolynomial
        (wordAbelianization previous.2 + wordMonomial [a])
    cutoffMagnus (r + 2) (positivePairWords (r + 2) index).1 -
        cutoffMagnus (r + 2) (positivePairWords (r + 2) index).2 =
      cutoffMul (r + 2) c x - cutoffMul (r + 2) x c := by
  classical
  let cutoff := r + 2
  let previous := positivePairWords (r + 1) (Fin.init index)
  let a := index (Fin.last (r + 1))
  let rationalMagnus (source : List A) : RationalWordPolynomial A :=
    toRationalWordPolynomial (magnusPolynomial source)
  let linear (source : List A) : CutoffCoefficients A cutoff :=
    cutoffRestriction cutoff (toRationalWordPolynomial (wordAbelianization source))
  let difference := cutoffMagnus cutoff previous.1 - cutoffMagnus cutoff previous.2
  let x := linear previous.2 + linear [a]
  have rationalMagnus_append (left right : List A) :
      rationalMagnus (left ++ right) =
        rationalMagnus left * rationalMagnus right := by
    simp [rationalMagnus, magnusPolynomial, List.prod_append]
  have tail_vanishes (source : List A) :
      VanishesBelow cutoff 2
        (cutoffMagnus cutoff source - cutoffOne cutoff - linear source) := by
    intro w hw
    by_cases hzero : FreeMonoid.length w.1 = 0
    · have hword : w.1 = 1 := by
        apply FreeMonoid.toList.injective
        apply List.length_eq_zero_iff.mp
        simpa [FreeMonoid.length] using hzero
      have hm : (magnusPolynomial source).coeff 1 = 1 := by
        simpa only [FreeMonoid.ofList_nil, scatteredCount, Nat.cast_one] using
          magnusPolynomial_coeff_scatteredCount source []
      simp only [Pi.sub_apply, cutoffMagnus, cutoffOne, cutoffRestriction,
        linear, hword, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom]
      rw [hm, wordAbelianization_coeff_empty]
      norm_num
    · have hone : FreeMonoid.length w.1 = 1 := by omega
      obtain ⟨b, hlist⟩ := List.length_eq_one_iff.mp (by
        simpa [FreeMonoid.length] using hone)
      have hword : w.1 = FreeMonoid.ofList [b] := by
        apply FreeMonoid.toList.injective
        simpa using hlist
      have hm := magnusPolynomial_coeff_scatteredCount source [b]
      have ha := wordAbelianization_coeff_singleton source b
      have hletter : (FreeMonoid.of b : FreeMonoid A) =
          FreeMonoid.ofList [b] := rfl
      have hne : (FreeMonoid.of b : FreeMonoid A) ≠ 1 := by
        intro h
        have lists := congrArg FreeMonoid.toList h
        simp at lists
      simp only [Pi.sub_apply, cutoffMagnus, cutoffOne, cutoffRestriction,
        linear, hword, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom]
      rw [hm, ha]
      simp [MonoidAlgebra.one_def, ← hletter, hne]
  have hprevious : VanishesBelow cutoff (r + 1) difference := by
    simpa [cutoff, difference, previous] using
      (full_positivePair_ratio_filtration cutoff (r + 1)
        (Fin.init index)).1
  have hrightTail : VanishesBelow cutoff 2
      (cutoffRestriction cutoff
          (rationalMagnus ([a] ++ previous.2) - 1) - x) := by
    intro w hw
    have htail := tail_vanishes ([a] ++ previous.2) w hw
    simpa [cutoffMagnus, cutoffOne, rationalMagnus, linear, x,
      cutoffRestriction, wordAbelianization, List.sum_append,
      add_comm, add_left_comm, add_assoc] using htail
  have hleftTail : VanishesBelow cutoff 2
      (cutoffRestriction cutoff
          (rationalMagnus (previous.2 ++ [a]) - 1) - x) := by
    intro w hw
    have htail := tail_vanishes (previous.2 ++ [a]) w hw
    simpa [cutoffMagnus, cutoffOne, rationalMagnus, linear, x, cutoffRestriction,
      wordAbelianization, List.sum_append, add_comm,
      add_left_comm, add_assoc] using htail
  have hrightError := cutoffMul_vanishesBelow cutoff (r + 1) 2
    difference
    (cutoffRestriction cutoff
      (rationalMagnus ([a] ++ previous.2) - 1) - x)
    hprevious hrightTail
  have hleftError := cutoffMul_vanishesBelow cutoff 2 (r + 1)
    (cutoffRestriction cutoff
      (rationalMagnus (previous.2 ++ [a]) - 1) - x)
    difference hleftTail hprevious
  have hrightZero : cutoffMul cutoff difference
      (cutoffRestriction cutoff
        (rationalMagnus ([a] ++ previous.2) - 1) - x) = 0 := by
    funext w
    exact hrightError w (by have := w.2; omega)
  have hleftZero : cutoffMul cutoff
      (cutoffRestriction cutoff
        (rationalMagnus (previous.2 ++ [a]) - 1) - x)
      difference = 0 := by
    funext w
    exact hleftError w (by have := w.2; omega)
  have hrightMul : cutoffMul cutoff difference
      (cutoffRestriction cutoff
        (rationalMagnus ([a] ++ previous.2) - 1)) =
      cutoffMul cutoff difference x := by
    have hsub : cutoffMul cutoff difference
        (cutoffRestriction cutoff
          (rationalMagnus ([a] ++ previous.2) - 1) - x) =
        cutoffMul cutoff difference
            (cutoffRestriction cutoff
              (rationalMagnus ([a] ++ previous.2) - 1)) -
          cutoffMul cutoff difference x := by
      funext w
      simp [cutoffMul, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    rw [hsub] at hrightZero
    exact sub_eq_zero.mp hrightZero
  have hleftMul : cutoffMul cutoff
      (cutoffRestriction cutoff
        (rationalMagnus (previous.2 ++ [a]) - 1)) difference =
      cutoffMul cutoff x difference := by
    have hsub : cutoffMul cutoff
        (cutoffRestriction cutoff
          (rationalMagnus (previous.2 ++ [a]) - 1) - x) difference =
        cutoffMul cutoff
            (cutoffRestriction cutoff
              (rationalMagnus (previous.2 ++ [a]) - 1)) difference -
          cutoffMul cutoff x difference := by
      funext w
      simp [cutoffMul, Finset.sum_sub_distrib, sub_mul]
    rw [hsub] at hleftZero
    exact sub_eq_zero.mp hleftZero
  have hpolynomial :
      rationalMagnus (previous.1 ++ [a] ++ previous.2) -
          rationalMagnus (previous.2 ++ [a] ++ previous.1) =
        (rationalMagnus previous.1 - rationalMagnus previous.2) *
            (rationalMagnus ([a] ++ previous.2) - 1) -
          (rationalMagnus (previous.2 ++ [a]) - 1) *
            (rationalMagnus previous.1 - rationalMagnus previous.2) := by
    simp only [rationalMagnus_append]
    noncomm_ring
  have hdifferenceRestriction : difference = cutoffRestriction cutoff
      (rationalMagnus previous.1 - rationalMagnus previous.2) := by
    funext w
    rfl
  have hxRestriction : x = cutoffRestriction cutoff
      (toRationalWordPolynomial
        (wordAbelianization previous.2 + wordMonomial [a])) := by
    funext w
    simp [x, linear, cutoffRestriction, wordAbelianization]
  change cutoffMagnus cutoff (positivePairWords (r + 2) index).1 -
      cutoffMagnus cutoff (positivePairWords (r + 2) index).2 = _
  rw [show positivePairWords (r + 2) index =
      (previous.1 ++ [a] ++ previous.2,
        previous.2 ++ [a] ++ previous.1) by
      simp [positivePairWords, previous, a], cutoffMagnus]
  change cutoffRestriction cutoff
      (rationalMagnus (previous.1 ++ [a] ++ previous.2) -
        rationalMagnus (previous.2 ++ [a] ++ previous.1)) = _
  rw [hpolynomial]
  rw [show cutoffRestriction cutoff
        ((rationalMagnus previous.1 - rationalMagnus previous.2) *
            (rationalMagnus ([a] ++ previous.2) - 1) -
          (rationalMagnus (previous.2 ++ [a]) - 1) *
            (rationalMagnus previous.1 - rationalMagnus previous.2)) =
      cutoffMul cutoff difference
          (cutoffRestriction cutoff
            (rationalMagnus ([a] ++ previous.2) - 1)) -
        cutoffMul cutoff
          (cutoffRestriction cutoff
            (rationalMagnus (previous.2 ++ [a]) - 1)) difference by
      funext w
      rw [hdifferenceRestriction]
      rw [Pi.sub_apply, ← cutoffRestriction_mul, ← cutoffRestriction_mul]
      rfl,
    hrightMul, hleftMul]
  rw [hxRestriction]

/-- The finite inverse has constant coefficient one, so the preceding
commutator is also the actual leading term of the successor ratio. -/
theorem full_positivePair_successor_ratio_leading_bracket
    [Finite A] [DecidableEq A]
    (r : ℕ) (index : PositivePairIndex A (r + 2)) :
    let previous := positivePairWords (r + 1) (Fin.init index)
    let a := index (Fin.last (r + 1))
    let c := cutoffMagnus (r + 2) previous.1 -
      cutoffMagnus (r + 2) previous.2
    let x := cutoffRestriction (r + 2) <|
      toRationalWordPolynomial
        (wordAbelianization previous.2 + wordMonomial [a])
    positivePairRatio (r + 2) (r + 2) index - cutoffOne (r + 2) =
      cutoffMul (r + 2) c x - cutoffMul (r + 2) x c := by
  classical
  let cutoff := r + 2
  let pair := positivePairWords cutoff index
  let difference := cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2
  let tail := cutoffMagnus cutoff pair.2 - cutoffOne cutoff
  let inverse := cutoffGeometricInverse cutoff tail
  have htail : VanishesBelow cutoff 1 tail := by
    intro w hw
    have hlength : FreeMonoid.length w.1 = 0 := by omega
    have hword : w.1 = 1 := by
      apply FreeMonoid.toList.injective
      apply List.length_eq_zero_iff.mp
      simpa [FreeMonoid.length] using hlength
    have hm : (magnusPolynomial pair.2).coeff 1 = 1 := by
      simpa only [FreeMonoid.ofList_nil, scatteredCount, Nat.cast_one] using
        magnusPolynomial_coeff_scatteredCount pair.2 []
    simp [tail, cutoffMagnus, cutoffOne, cutoffRestriction, hword,
      toRationalWordPolynomial, hm]
  have hinverse : cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse =
      cutoffOne cutoff := by
    have hone : cutoffMagnus cutoff pair.2 = cutoffOne cutoff + tail := by
      simp [tail]
    rw [hone]
    exact cutoffMul_geometricInverse cutoff tail htail
  let emptyWord : CutoffWord A cutoff := ⟨1, by simp⟩
  have hinverseConstant : inverse emptyWord = 1 := by
    have hi := congrFun hinverse emptyWord
    have hm : (magnusPolynomial pair.2).coeff 1 = 1 := by
      simpa only [FreeMonoid.ofList_nil, scatteredCount, Nat.cast_one] using
        magnusPolynomial_coeff_scatteredCount pair.2 []
    simpa [cutoffMul, emptyWord, cutoffMagnus, cutoffOne,
      cutoffRestriction, toRationalWordPolynomial, hm] using hi
  have hdifference : VanishesBelow cutoff cutoff difference := by
    simpa [difference, pair] using
      (full_positivePair_ratio_filtration cutoff cutoff index).1
  have hmul : cutoffMul cutoff difference inverse = difference := by
    funext w
    rw [cutoffMul, Finset.sum_eq_single (FreeMonoid.length w.1)]
    · simp only [FreeMonoid.length, List.take_length, List.drop_length,
        FreeMonoid.ofList_toList]
      change difference w * inverse emptyWord = difference w
      rw [hinverseConstant, mul_one]
    · intro i hi hne
      have hi_le : i ≤ FreeMonoid.length w.1 := by
        simpa [Finset.mem_range] using hi
      have hi_lt : i < FreeMonoid.length w.1 := lt_of_le_of_ne hi_le hne
      rw [hdifference]
      · simp
      · simp only [FreeMonoid.length, FreeMonoid.toList_ofList,
          List.length_take]
        have hw := w.2
        omega
    · simp
  have hproduct : positivePairRatio cutoff cutoff index - cutoffOne cutoff =
      cutoffMul cutoff difference inverse := by
    change cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
        cutoffOne cutoff = _
    rw [show cutoffMul cutoff difference inverse =
        cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
          cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse by
        funext w
        simp [difference, cutoffMul, Finset.sum_sub_distrib, sub_mul],
      hinverse]
  rw [hproduct, hmul]
  simpa [cutoff, pair, difference] using
    full_positivePair_successor_leading_bracket r index

#print axioms full_positivePair_ratio_filtration
#print axioms full_positivePair_successor_leading_bracket
#print axioms full_positivePair_successor_ratio_leading_bracket
#print axioms cutoffMul_geometricInverse
#print axioms geometricInverse_cutoffMul


end D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairLeadingCoefficients
