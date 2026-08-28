/- GID: D5/S3/Analytic/VOACompletion/WeightOneCharacterResidual
   generality: I
   mirror-B: D5/B/S3/Analytic/VOACompletion/WeightOneCharacterResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Weight-one subtraction makes the Niemeier scalar character universal. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.VOACompletion.WeightOneCharacterResidual

/- The scalar character is represented by its complex-valued function of the
   modular parameter.  The source's additive `dim V₁` term is the corresponding
   constant character. -/
abbrev ScalarCharacter := ℂ → ℂ

def addDimension (character : ScalarCharacter) (dimension : ℕ) : ScalarCharacter :=
  fun τ => character τ + (dimension : ℂ)

def weightOneResidual (character : ScalarCharacter) (dimension : ℕ) : ScalarCharacter :=
  fun τ => character τ - (dimension : ℂ)

def jPlusTwentyFourTimesCoxeterPlusOne
    (J : ScalarCharacter) (h : ℕ) : ScalarCharacter :=
  fun τ => J τ + ((24 * (h + 1) : ℕ) : ℂ)

def twentyFourTimesCoxeterPlusOne (h : ℕ) : ℕ := 24 * (h + 1)

/- The complete twenty-four-element Niemeier classification is kept as named
   constructors.  In particular, the source's A5^4 D4 and D4^6 collision is
   represented by two visibly distinct values rather than an anonymous index. -/
inductive NiemeierRootSystem
  | leech
  | a1_24
  | a2_12
  | a3_8
  | a4_6
  | a5_4_d4
  | d4_6
  | a6_4
  | a7_2_d5_2
  | a8_3
  | a9_2_d6
  | d6_4
  | e6_4
  | a11_d7_e6
  | a12_2
  | d8_3
  | a15_d9
  | a17_e7
  | d10_e7_2
  | d12_2
  | a24
  | d16_e8
  | e8_3
  | d24
  deriving DecidableEq

abbrev NiemeierVOA := NiemeierRootSystem

/- Structural data is deliberately separate from the scalar observation.  A
   difference in this record is information that an untwined scalar cannot
   recover. -/
structure StructuralData where
  multiplicationCode : ℕ
  opeCode : ℕ
  groupActionCode : ℕ
  lieStructureCode : ℕ

structure ClassificationData where
  weightOneLieCode : ℕ
  orbifoldCode : ℕ
  fineStructureCode : ℕ

/- A general central-charge-24 holomorphic VOA datum.  The central-charge and
   holomorphicity premises remain explicit so the theorem does not silently
   widen the source domain. -/
structure VOAData where
  centralCharge : ℕ
  holomorphic : Prop
  scalarCharacter : ScalarCharacter
  weightOneDimension : ℕ

def sameThetaDifferentRoot
    (theta : NiemeierVOA → ScalarCharacter) : Prop :=
  ∃ x y : NiemeierVOA, x ≠ y ∧ theta x = theta y

def scalarBlindToStructure
    (scalarCharacter : NiemeierVOA → ScalarCharacter)
    (structureData : NiemeierVOA → StructuralData) : Prop :=
  ∃ x y : NiemeierVOA,
    scalarCharacter x = scalarCharacter y ∧ structureData x ≠ structureData y

def classificationNeedsRefinement
    (scalarCharacter : NiemeierVOA → ScalarCharacter)
    (classificationData : NiemeierVOA → ClassificationData) : Prop :=
  ∃ x y : NiemeierVOA,
    scalarCharacter x = scalarCharacter y ∧ classificationData x ≠ classificationData y

/-- Weight-one cancellation, scalar-character blindness, and the refinement
requirements for the central-charge-24 holomorphic case.

The hypotheses are the source-bound data immediately preceding theorem 109.1:
the `J + 24(h+1)` character formula, the matching weight-one dimension, the
two named equal-Theta root systems, modularity for general holomorphic VOAs,
and the source's structural/classification separation witnesses.  No VOA or
Niemeier API exists in pinned Mathlib, so these facts are honest premises while
the residual cancellation and the two concrete blindness witnesses are proved
pointwise. -/
theorem weight_one_character_residual
    (J : ScalarCharacter)
    (scalarCharacter : NiemeierVOA → ScalarCharacter)
    (weightOneDimension : NiemeierVOA → ℕ)
    (coxeterNumber : NiemeierVOA → ℕ)
    (theta : NiemeierVOA → ScalarCharacter)
    (structureData : NiemeierVOA → StructuralData)
    (classificationData : NiemeierVOA → ClassificationData)
    (hCharacter : ∀ N : NiemeierVOA,
      scalarCharacter N =
        jPlusTwentyFourTimesCoxeterPlusOne J (coxeterNumber N))
    (hWeightOne : ∀ N : NiemeierVOA,
      weightOneDimension N = twentyFourTimesCoxeterPlusOne (coxeterNumber N))
    (hA5Coxeter : coxeterNumber NiemeierRootSystem.a5_4_d4 = 6)
    (hD4Coxeter : coxeterNumber NiemeierRootSystem.d4_6 = 6)
    (hThetaCollision :
      theta NiemeierRootSystem.a5_4_d4 = theta NiemeierRootSystem.d4_6)
    (hGeneralModularity : ∀ V : VOAData,
      V.centralCharge = 24 → V.holomorphic →
        V.scalarCharacter = addDimension J V.weightOneDimension)
    (hStructuralDifference :
      structureData NiemeierRootSystem.a5_4_d4 ≠
        structureData NiemeierRootSystem.d4_6)
    (hClassificationDifference :
      classificationData NiemeierRootSystem.a5_4_d4 ≠
        classificationData NiemeierRootSystem.d4_6) :
    (∀ N : NiemeierVOA,
      weightOneResidual (scalarCharacter N) (weightOneDimension N) = J) ∧
      sameThetaDifferentRoot theta ∧
      (∀ V : VOAData,
        V.centralCharge = 24 → V.holomorphic →
          V.scalarCharacter = addDimension J V.weightOneDimension) ∧
      scalarBlindToStructure scalarCharacter structureData ∧
      classificationNeedsRefinement scalarCharacter classificationData := by
  have hResidual : ∀ N : NiemeierVOA,
      weightOneResidual (scalarCharacter N) (weightOneDimension N) = J := by
    intro N
    funext τ
    rw [weightOneResidual, hCharacter N, hWeightOne N]
    simp [jPlusTwentyFourTimesCoxeterPlusOne, twentyFourTimesCoxeterPlusOne]
  have hCollision : sameThetaDifferentRoot theta := by
    refine ⟨NiemeierRootSystem.a5_4_d4, NiemeierRootSystem.d4_6, ?_, hThetaCollision⟩
    decide
  have hCoxeterEq :
      coxeterNumber NiemeierRootSystem.a5_4_d4 =
        coxeterNumber NiemeierRootSystem.d4_6 := by
    rw [hA5Coxeter, hD4Coxeter]
  have hScalarCollision :
      scalarCharacter NiemeierRootSystem.a5_4_d4 =
        scalarCharacter NiemeierRootSystem.d4_6 := by
    rw [hCharacter, hCharacter, hCoxeterEq]
  have hStructuralBlindness :
      scalarBlindToStructure scalarCharacter structureData := by
    exact ⟨NiemeierRootSystem.a5_4_d4, NiemeierRootSystem.d4_6,
      hScalarCollision, hStructuralDifference⟩
  have hClassificationRefinement :
      classificationNeedsRefinement scalarCharacter classificationData := by
    exact ⟨NiemeierRootSystem.a5_4_d4, NiemeierRootSystem.d4_6,
      hScalarCollision, hClassificationDifference⟩
  refine ⟨hResidual, hCollision, hGeneralModularity,
    hStructuralBlindness, hClassificationRefinement⟩

/- Reverse probe: the public proposition exposes both the universal residual and
   the concrete distinct-root same-Theta collision. -/
example
    (J : ScalarCharacter)
    (scalarCharacter : NiemeierVOA → ScalarCharacter)
    (weightOneDimension : NiemeierVOA → ℕ)
    (theta : NiemeierVOA → ScalarCharacter)
    (result :
      (∀ N : NiemeierVOA,
        weightOneResidual (scalarCharacter N) (weightOneDimension N) = J) ∧
        sameThetaDifferentRoot theta ∧
        (∀ V : VOAData,
          V.centralCharge = 24 → V.holomorphic →
            V.scalarCharacter = addDimension J V.weightOneDimension) ∧
        scalarBlindToStructure scalarCharacter
          (fun _ => ⟨0, 0, 0, 0⟩) ∧
        classificationNeedsRefinement scalarCharacter
          (fun _ => ⟨0, 0, 0⟩)) :
    (∀ N : NiemeierVOA,
      weightOneResidual (scalarCharacter N) (weightOneDimension N) = J) ∧
      sameThetaDifferentRoot theta := by
  exact ⟨result.1, result.2.1⟩

/- Trivialization probe: a nonzero weight-one dimension is not silently erased by
   the residual operation. -/
example (J : ScalarCharacter) :
    weightOneResidual (addDimension J 1) 1 = J := by
  funext τ
  simp [weightOneResidual, addDimension]

example (J : ScalarCharacter) : addDimension J 1 ≠ J := by
  intro h
  have h0 := congrFun h 0
  norm_num [addDimension] at h0

/- Structural collapse probe: the two named root-system constructors are distinct,
   so the collision witness is not a one-point quotient. -/
example : NiemeierRootSystem.a5_4_d4 ≠ NiemeierRootSystem.d4_6 := by decide

#print axioms weight_one_character_residual

end D5.S3.Analytic.VOACompletion.WeightOneCharacterResidual
