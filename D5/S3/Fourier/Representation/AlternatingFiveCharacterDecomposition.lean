/- GID: D5/S3/Fourier/Representation/AlternatingFiveCharacterDecomposition
   generality: I
   mirror-B: D5/B/S3/Fourier/Representation/AlternatingFiveCharacterDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The A5 seven-dimensional character is the sum of the 1, 3, and conjugate 3 rows. -/

/- Library-search audit trail (2026-08-28):
   * Repository searches found existing uses of `alternatingGroup (Fin 5)` but
     no A5 character table, no concrete three-dimensional representations,
     and no copy of this seven-dimensional decomposition.
   * Pinned Mathlib supplies generic `FDRep.character` and
     `Representation.character` APIs, but no concrete A5 irreducible character
     table. It does supply the exact identity
     `Real.goldenRatio_add_goldenConj`, which is applied below.
   * Loogle and LeanSearch found no exact whole-theorem result. GitHub found
     TauCeti's general character-table framework, but no A5 table instance;
     TauCeti is also not an admitted pinned dependency of this repository.
   * Consequently the class labels and character values are the closed data
     stated by the source atom. The theorem proves exactly their finite
     pointwise identity; it does not construct an isomorphism of representations. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S3.Fourier.Representation.AlternatingFiveCharacterDecomposition

noncomputable section

/-- The five conjugacy-class labels used by the A5 character table. -/
inductive AlternatingFiveClass
  | oneA
  | twoA
  | threeA
  | fiveA
  | fiveB
  deriving DecidableEq

/-- The source-given character row of the seven-dimensional representation. -/
def sevenDimensionalCharacter : AlternatingFiveClass -> Real
  | .oneA => 7
  | .twoA => -1
  | .threeA => 1
  | .fiveA => 2
  | .fiveB => 2

/-- The source-given trivial character row. -/
def trivialCharacter : AlternatingFiveClass -> Real
  | _ => 1

/-- The source-given character row of the first three-dimensional representation. -/
def threeDimensionalCharacter : AlternatingFiveClass -> Real
  | .oneA => 3
  | .twoA => -1
  | .threeA => 0
  | .fiveA => Real.goldenRatio
  | .fiveB => Real.goldenConj

/-- The Galois-conjugate source row of the other three-dimensional representation. -/
def conjugateThreeDimensionalCharacter : AlternatingFiveClass -> Real
  | .oneA => 3
  | .twoA => -1
  | .threeA => 0
  | .fiveA => Real.goldenConj
  | .fiveB => Real.goldenRatio

/-- On every A5 conjugacy class, the seven-dimensional character is the sum
of the trivial character and the two conjugate three-dimensional characters. -/
theorem alternating_five_character_decomposition :
    sevenDimensionalCharacter =
      trivialCharacter + threeDimensionalCharacter +
        conjugateThreeDimensionalCharacter := by
  funext conjugacyClass
  cases conjugacyClass <;>
    simp [sevenDimensionalCharacter, trivialCharacter,
      threeDimensionalCharacter, conjugateThreeDimensionalCharacter] <;>
    linarith [Real.goldenRatio_add_goldenConj]

#print axioms alternating_five_character_decomposition

/- Reverse probe: the public function equality recovers the non-rational 5A
class calculation without unfolding either three-dimensional character row. -/
example :
    trivialCharacter .fiveA + threeDimensionalCharacter .fiveA +
        conjugateThreeDimensionalCharacter .fiveA = 2 := by
  calc
    trivialCharacter .fiveA + threeDimensionalCharacter .fiveA +
          conjugateThreeDimensionalCharacter .fiveA =
        (trivialCharacter + threeDimensionalCharacter +
          conjugateThreeDimensionalCharacter) .fiveA := rfl
    _ = sevenDimensionalCharacter .fiveA :=
      congrFun alternating_five_character_decomposition .fiveA |>.symm
    _ = 2 := rfl

/- Trivialization probes: the closed target row cannot be replaced by the zero
or a constant character; its identity and involution values are fixed and distinct. -/
example : Not (sevenDimensionalCharacter = 0) := by
  intro zeroCharacter
  have identityValue := congrFun zeroCharacter AlternatingFiveClass.oneA
  norm_num [sevenDimensionalCharacter] at identityValue

example : Not (
    sevenDimensionalCharacter .oneA = sevenDimensionalCharacter .twoA) := by
  norm_num [sevenDimensionalCharacter]

end

end D5.S3.Fourier.Representation.AlternatingFiveCharacterDecomposition
