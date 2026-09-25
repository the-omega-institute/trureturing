/- GID: D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full indexed positive-pair family has the required cutoff filtration. -/

import D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration

open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open private coeff_mul_eq_split_sum from
  D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra

variable {A : Type*}

/-- An index retains every recursive choice.  At level `r` it is a word of
`r` choices, so equal evaluated pairs are not identified. -/
abbrev PositivePairIndex (A : Type*) (r : ℕ) := Fin r → A

/-- Full recursively generated positive-pair family.  Level one is
`(a, [])`; every later level applies `(u,v,a) ↦ (uav,vau)`. -/
def positivePairWords : (r : ℕ) → PositivePairIndex A r → List A × List A
  | 0, _ => ([], [])
  | 1, index => ([index 0], [])
  | r + 2, index =>
      let previous := positivePairWords (r + 1) (Fin.init index)
      let a := index (Fin.last (r + 1))
      (previous.1 ++ [a] ++ previous.2,
        previous.2 ++ [a] ++ previous.1)

/-- The actual Magnus polynomial, restricted to the finite word cutoff. -/
noncomputable def cutoffMagnus [Finite A] (r : ℕ) (source : List A) :
    CutoffCoefficients A r :=
  cutoffRestriction r (toRationalWordPolynomial (magnusPolynomial source))

/-- The level-`r` full-family ratio `M(u) M(v)⁻¹`, observed through an
independent word cutoff.  The independent cutoff lets a level participate in
the construction of its successor without changing carriers. -/
noncomputable def positivePairRatio [Finite A] (cutoff r : ℕ)
    (index : PositivePairIndex A r) : CutoffCoefficients A cutoff :=
  let pair := positivePairWords r index
  cutoffMul cutoff (cutoffMagnus cutoff pair.1)
    (cutoffGeometricInverse cutoff
      (cutoffMagnus cutoff pair.2 - cutoffOne cutoff))

/-- Every recursively generated pair agrees below its level, and its actual
cutoff Magnus ratio consequently differs from one only in that level and
above.  The recursion retains the full indexed family, including duplicate
pairs and zero leading directions. -/
theorem full_positivePair_ratio_filtration [Finite A]
    (cutoff r : ℕ) (index : PositivePairIndex A r) :
    VanishesBelow cutoff r
        (cutoffMagnus cutoff (positivePairWords r index).1 -
          cutoffMagnus cutoff (positivePairWords r index).2) ∧
      VanishesBelow cutoff r
        (positivePairRatio cutoff r index - cutoffOne cutoff) := by
  classical
  let rationalMagnus (source : List A) : RationalWordPolynomial A :=
    toRationalWordPolynomial (magnusPolynomial source)
  have rationalMagnus_append (left right : List A) :
      rationalMagnus (left ++ right) =
        rationalMagnus left * rationalMagnus right := by
    simp [rationalMagnus, magnusPolynomial_append]
  have constant_coeff (source : List A) :
      (rationalMagnus source).coeff 1 = 1 := by
    induction source with
    | nil => simp [rationalMagnus, magnusPolynomial]
    | cons a source ih =>
        rw [show rationalMagnus (a :: source) =
          rationalMagnus [a] * rationalMagnus source by
            simpa using rationalMagnus_append [a] source]
        rw [coeff_mul_eq_split_sum]
        have hne : (FreeMonoid.of a : FreeMonoid A) ≠ 1 := by
          intro h
          have := congrArg FreeMonoid.toList h
          simp at this
        have hletter : (rationalMagnus [a]).coeff 1 = 1 := by
          simp [rationalMagnus, magnusPolynomial, toRationalWordPolynomial,
            MonoidAlgebra.coeff_mapRingHom, wordMonomial, hne]
        simpa [FreeMonoid.length, hletter, ih]
  have minus_one_vanishes (cutoff : ℕ) (source : List A) :
      VanishesBelow cutoff 1
        (cutoffRestriction cutoff (rationalMagnus source - 1)) := by
    intro w hw
    have hlength : FreeMonoid.length w.1 = 0 := by omega
    have hword : w.1 = 1 := by
      apply FreeMonoid.toList.injective
      apply List.length_eq_zero_iff.mp
      simpa [FreeMonoid.length] using hlength
    simp [cutoffRestriction, hword, constant_coeff]
  have filtration : ∀ level (familyIndex : PositivePairIndex A level)
      (cutoff : ℕ),
      VanishesBelow cutoff level
        (cutoffRestriction cutoff
          (rationalMagnus (positivePairWords level familyIndex).1 -
            rationalMagnus (positivePairWords level familyIndex).2)) := by
    intro level
    induction level using Nat.twoStepInduction with
    | zero =>
        intro familyIndex cutoff w hw
        omega
    | one =>
        intro familyIndex cutoff
        simpa [positivePairWords, rationalMagnus, magnusPolynomial] using
          minus_one_vanishes cutoff [familyIndex 0]
    | more level ih0 ih1 =>
        intro familyIndex cutoff
        let previous := positivePairWords (level + 1) (Fin.init familyIndex)
        let a := familyIndex (Fin.last (level + 1))
        let difference := rationalMagnus previous.1 - rationalMagnus previous.2
        have hdifference : VanishesBelow cutoff (level + 1)
            (cutoffRestriction cutoff difference) := by
          simpa [difference, previous] using
            ih1 (Fin.init familyIndex) cutoff
        have hright : VanishesBelow cutoff 1
            (cutoffRestriction cutoff
              (rationalMagnus ([a] ++ previous.2) - 1)) :=
          minus_one_vanishes cutoff ([a] ++ previous.2)
        have hleft : VanishesBelow cutoff 1
            (cutoffRestriction cutoff
              (rationalMagnus (previous.2 ++ [a]) - 1)) :=
          minus_one_vanishes cutoff (previous.2 ++ [a])
        have hfirst := cutoffMul_vanishesBelow cutoff (level + 1) 1
          (cutoffRestriction cutoff difference)
          (cutoffRestriction cutoff
            (rationalMagnus ([a] ++ previous.2) - 1)) hdifference hright
        have hsecond := cutoffMul_vanishesBelow cutoff 1 (level + 1)
          (cutoffRestriction cutoff
            (rationalMagnus (previous.2 ++ [a]) - 1))
          (cutoffRestriction cutoff difference) hleft hdifference
        have hpolynomial :
            rationalMagnus (previous.1 ++ [a] ++ previous.2) -
                rationalMagnus (previous.2 ++ [a] ++ previous.1) =
              difference * (rationalMagnus ([a] ++ previous.2) - 1) -
                (rationalMagnus (previous.2 ++ [a]) - 1) * difference := by
          simp only [rationalMagnus_append]
          dsimp [difference]
          noncomm_ring
        rw [show positivePairWords (level + 2) familyIndex =
            (previous.1 ++ [a] ++ previous.2,
              previous.2 ++ [a] ++ previous.1) by
              simp [positivePairWords, previous, a],
          hpolynomial]
        rw [show cutoffRestriction cutoff
              (difference * (rationalMagnus ([a] ++ previous.2) - 1) -
                (rationalMagnus (previous.2 ++ [a]) - 1) * difference) =
            cutoffMul cutoff (cutoffRestriction cutoff difference)
                (cutoffRestriction cutoff
                  (rationalMagnus ([a] ++ previous.2) - 1)) -
              cutoffMul cutoff
                (cutoffRestriction cutoff
                  (rationalMagnus (previous.2 ++ [a]) - 1))
                (cutoffRestriction cutoff difference) by
              funext w
              rw [Pi.sub_apply, ← cutoffRestriction_mul,
                ← cutoffRestriction_mul]
              rfl]
        intro w hw
        rw [Pi.sub_apply, hfirst w (by omega), hsecond w (by omega), sub_zero]
  have hdifference := filtration r index cutoff
  have hdifference' : VanishesBelow cutoff r
      (cutoffMagnus cutoff (positivePairWords r index).1 -
        cutoffMagnus cutoff (positivePairWords r index).2) := by
    intro w hw
    simpa [cutoffMagnus, rationalMagnus, cutoffRestriction] using
      hdifference w hw
  refine ⟨?_, ?_⟩
  · exact hdifference'
  · let pair := positivePairWords r index
    let denominatorTail := cutoffMagnus cutoff pair.2 - cutoffOne cutoff
    let inverse := cutoffGeometricInverse cutoff denominatorTail
    have htail : VanishesBelow cutoff 1 denominatorTail := by
      intro w hw
      simpa [denominatorTail, cutoffMagnus, rationalMagnus, cutoffOne,
        cutoffRestriction] using minus_one_vanishes cutoff pair.2 w hw
    have hinverse : cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse =
        cutoffOne cutoff := by
      have hone : cutoffMagnus cutoff pair.2 =
          cutoffOne cutoff + denominatorTail := by
        simp [denominatorTail]
      rw [hone]
      exact cutoffMul_geometricInverse cutoff denominatorTail htail
    have hproduct :
        positivePairRatio cutoff r index - cutoffOne cutoff =
          cutoffMul cutoff
            (cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2)
            inverse := by
      change cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
          cutoffOne cutoff = _
      rw [show cutoffMul cutoff
              (cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2) inverse =
            cutoffMul cutoff (cutoffMagnus cutoff pair.1) inverse -
              cutoffMul cutoff (cutoffMagnus cutoff pair.2) inverse by
            funext w
            simp [cutoffMul, Finset.sum_sub_distrib, sub_mul],
        hinverse]
    rw [hproduct]
    exact cutoffMul_vanishesBelow cutoff r 0
      (cutoffMagnus cutoff pair.1 - cutoffMagnus cutoff pair.2) inverse
      (by simpa [pair] using hdifference')
      (by intro w hw; omega)


end D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
