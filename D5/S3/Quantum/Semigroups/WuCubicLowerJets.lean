/- GID: D5/S3/Quantum/Semigroups/WuCubicLowerJets
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicLowerJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Directional rational jets for the lower near-Gibbs Wu cubic certificate. -/

import D5.S3.Quantum.Semigroups.WuCubicLowerOccupation
import D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational
import D5.S3.Quantum.Semigroups.WuCubicUpperPartition
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicLowerJets

noncomputable section

open scoped BigOperators
open WuCubicLowerCoefficients WuCubicLowerOccupation
open WuCubicUpperCornerJet
open WuCubicUpperPartition (Box)
open WuCubicHellingerMatrix (levels basis lowerWeight upperWeight lowerTilt upperTilt longCrossing)
open WuCubicRefinedHellinger (signedTiltRow)
open WuCubicOccupationTaylor (gibbsLevels)
open D5.S0.Certificates.BoxCover.RationalIntervalExpression (value)
open private Checked.expr from D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
open private Jet Jet.val Jet.add Jet.mul Jet.neg Jet.inv Jet.square Jet.add_value Jet.mul_value
  Jet.neg_value Jet.inv_value Jet.square_value Jet.coord_value Jet.const_value
  padBox jetConst jetCoord coord_cast_zero coord_cast_one coord_cast_two coord_cast_three
  normalizedLeftGapJet jetGamma jetGamma_value jetC jetC_value jetE jetE_value
  jetFieldOverGap jetFieldOverGap_value jetEndpointField jetEndpointField_value
  jetEndpointLinear jetEndpointLinear_value jetBasis jetBasis_value jetEdgeRow jetEdgeRow_value
  from D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational
open private gamma c e from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private leftGap middleGap rightGap scaledMixture fieldOverGap
  lowerTiltFactor upperTiltFactor endpointField endpointLinear edgeRows edgeWeights
  massWeights massChange massRow gibbsMass entropyWeights
  from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix

local infixl:65 " +ⱼ " => Jet.add
local infixl:70 " *ⱼ " => Jet.mul

private abbrev AxisJet (b : Box) (i : Fin 4) := Jet (padBox b) i.castSucc

variable (b : Box) (i : Fin 4)

private def offsetJet (k : Fin 3) : AxisJet b i :=
  let y₀ := jetCoord b i 1
  let y₁ := jetCoord b i 2
  let blend := jetCoord b i 3
  ![y₀, y₁, y₁ +ⱼ (jetConst b i radius +ⱼ Jet.neg y₁) *ⱼ blend] k

private def gibbsJet (k : Fin 3) : AxisJet b i :=
  let r := jetCoord b i 0
  ![Jet.inv (Jet.square r), Jet.inv r, Jet.inv r] k

private def levelJet (k : Fin 3) : AxisJet b i := gibbsJet b i k +ⱼ offsetJet b i k

private def tJet : AxisJet b i := jetCoord b i 0 +ⱼ jetConst b i (-1)

private def middleJet : AxisJet b i :=
  (jetConst b i radius +ⱼ Jet.neg (offsetJet b i 1)) *ⱼ jetCoord b i 3 *ⱼ Jet.inv (tJet b i)

private def rightJet : AxisJet b i :=
  Jet.inv (jetCoord b i 0) +ⱼ Jet.neg (offsetJet b i 2) *ⱼ Jet.inv (tJet b i)

private def biasFactorJet (u v s : AxisJet b i) : AxisJet b i :=
  jetFieldOverGap b i *ⱼ (Jet.square u +ⱼ u *ⱼ v +ⱼ Jet.square v) +ⱼ
    jetConst b i 2 *ⱼ jetE b i *ⱼ tJet b i *ⱼ Jet.square s

private def middleBiasJet : AxisJet b i :=
  biasFactorJet b i (levelJet b i 1) (levelJet b i 2) (middleJet b i)

private def ellJet : AxisJet b i := middleBiasJet b i *ⱼ jetConst b i (1 / 4)

private def mixtureJet : AxisJet b i :=
  middleBiasJet b i *ⱼ jetConst b i (1 / 2) +ⱼ
    Jet.neg (jetC b i *ⱼ middleJet b i *ⱼ (levelJet b i 1 +ⱼ levelJet b i 2))

private def adjacentJet (endGap outerSum : AxisJet b i) : AxisJet b i :=
  endGap *ⱼ (jetC b i *ⱼ outerSum +ⱼ
    Jet.neg (jetConst b i 3 *ⱼ jetE b i *ⱼ tJet b i *ⱼ (endGap +ⱼ middleJet b i)))

private def lowerAdjacentJet : AxisJet b i :=
  adjacentJet b i (normalizedLeftGapJet b i)
    (levelJet b i 0 +ⱼ jetConst b i 2 *ⱼ levelJet b i 1 +ⱼ levelJet b i 2)

private def upperAdjacentJet : AxisJet b i :=
  adjacentJet b i (rightJet b i)
    (levelJet b i 1 +ⱼ jetConst b i 2 *ⱼ levelJet b i 2 +ⱼ jetConst b i 1)

private def p₀Jet : AxisJet b i :=
  (jetC b i *ⱼ Jet.square (normalizedLeftGapJet b i) *ⱼ (levelJet b i 0 +ⱼ levelJet b i 1) +ⱼ
    middleJet b i *ⱼ (lowerAdjacentJet b i +ⱼ Jet.neg (mixtureJet b i))) *ⱼ jetConst b i (1 / 2)

private def p₂Jet : AxisJet b i :=
  (jetC b i *ⱼ Jet.square (rightJet b i) *ⱼ (levelJet b i 2 +ⱼ jetConst b i 1) +ⱼ
    middleJet b i *ⱼ (upperAdjacentJet b i +ⱼ Jet.neg (mixtureJet b i))) *ⱼ jetConst b i (1 / 2)

private def pkJet : AxisJet b i := p₀Jet b i +ⱼ Jet.neg (p₂Jet b i)

private def pJet : AxisJet b i :=
  p₀Jet b i +ⱼ p₂Jet b i +ⱼ middleJet b i *ⱼ middleBiasJet b i *ⱼ jetConst b i (1 / 2)

private def kJet : AxisJet b i := pkJet b i *ⱼ Jet.inv (pJet b i)

private def longJet : AxisJet b i :=
  let l := normalizedLeftGapJet b i
  let s := middleJet b i
  let u := rightJet b i
  l *ⱼ u *ⱼ (jetC b i *ⱼ (levelJet b i 0 +ⱼ levelJet b i 1 +ⱼ
    levelJet b i 2 +ⱼ jetConst b i 1) +ⱼ
    (jetConst b i 3 *ⱼ jetE b i *ⱼ tJet b i *ⱼ
      Jet.neg (l +ⱼ u +ⱼ jetConst b i 2 *ⱼ s)))

private def lowerFactorJet : AxisJet b i :=
  let gap := Jet.inv (Jet.square (jetCoord b i 0)) +ⱼ
    (offsetJet b i 2 +ⱼ Jet.neg (offsetJet b i 0)) *ⱼ Jet.inv (tJet b i)
  jetEndpointField b i *ⱼ gap *ⱼ jetEndpointLinear b i (levelJet b i 0) (levelJet b i 2)

private def upperFactorJet : AxisJet b i :=
  let r := jetCoord b i 0
  let gap := Jet.inv r +ⱼ Jet.neg (offsetJet b i 1) *ⱼ Jet.inv (tJet b i)
  jetEndpointField b i *ⱼ gap *ⱼ jetEndpointLinear b i (levelJet b i 1) (jetConst b i 1) *ⱼ r

private def g₀Jet : AxisJet b i :=
  lowerFactorJet b i *ⱼ (jetCoord b i 0 *ⱼ offsetJet b i 0 +ⱼ Jet.neg (offsetJet b i 2)) *ⱼ
    Jet.inv (tJet b i)

private def g₂Jet : AxisJet b i :=
  upperFactorJet b i *ⱼ offsetJet b i 1 *ⱼ Jet.inv (tJet b i)

private def residualJet : AxisJet b i :=
  (jetConst b i 1 +ⱼ Jet.neg (kJet b i)) *ⱼ g₀Jet b i +ⱼ
    Jet.neg ((jetConst b i 1 +ⱼ kJet b i) *ⱼ g₂Jet b i)

private def pivotJet : AxisJet b i := longJet b i +ⱼ Jet.neg (kJet b i *ⱼ residualJet b i)

def scalarJet (j : Fin 11) : AxisJet b i :=
  let q := jetConst b i
  let s := middleJet b i
  let l₀ := mixtureJet b i
  let ell := ellJet b i
  let mix := l₀ +ⱼ ell
  let p₀ := p₀Jet b i
  let p₂ := p₂Jet b i
  let g₀ := g₀Jet b i
  let g₂ := g₂Jet b i
  let qa := q (2 / 3) *ⱼ (p₀ +ⱼ p₂)
  let qb := g₀ +ⱼ Jet.neg g₂ +ⱼ Jet.neg (q (4 / 3) *ⱼ p₂)
  let qc := q (2 / 3) *ⱼ p₂ +ⱼ g₂
  let l := normalizedLeftGapJet b i
  let u := rightJet b i
  let b₀ := l *ⱼ biasFactorJet b i (levelJet b i 0) (levelJet b i 1) l
  let b₂ := u *ⱼ biasFactorJet b i (levelJet b i 2) (q 1) u
  ![l₀, lowerAdjacentJet b i +ⱼ Jet.neg mix, upperAdjacentJet b i +ⱼ Jet.neg mix, p₀, p₂,
    b₀ +ⱼ Jet.neg (s *ⱼ ell), b₂ +ⱼ Jet.neg (s *ⱼ ell), longJet b i +ⱼ Jet.neg (s *ⱼ l₀),
    pJet b i *ⱼ (p₀ +ⱼ p₂ +ⱼ Jet.neg (s *ⱼ (ell +ⱼ mix))) +ⱼ Jet.neg (Jet.square (pkJet b i)),
    pivotJet b i, q 4 *ⱼ qa *ⱼ qc +ⱼ Jet.neg (Jet.square qb)] j

private def massWeightJet (k : Fin 3) : AxisJet b i :=
  let g := gibbsJet b i k
  let y := offsetJet b i k
  let three := jetConst b i 3
  three *ⱼ Jet.square g +ⱼ y *ⱼ (three *ⱼ g +ⱼ y)

private def scaleJet : AxisJet b i :=
  let q := jetConst b i
  let r := jetCoord b i 0
  q 1 +ⱼ Jet.neg (Jet.square (tJet b i) *ⱼ
    Jet.inv (q 4 *ⱼ (Jet.square r +ⱼ r +ⱼ q 1)))

private def occupationJet (j k : Fin 3) : AxisJet b i :=
  let q := jetConst b i
  let r := jetCoord b i 0
  let x := levelJet b i
  let y := offsetJet b i
  let B := jetBasis b i
  let edge := fun l w => w *ⱼ jetEdgeRow b i l j *ⱼ jetEdgeRow b i l k
  let edges := edge 0 (r *ⱼ x 0 +ⱼ x 1) +ⱼ edge 1 (r *ⱼ x 0 +ⱼ x 2) +ⱼ
    edge 2 (r *ⱼ x 1 +ⱼ q 1) +ⱼ edge 3 (r *ⱼ x 2 +ⱼ q 1)
  let entropy := fun l => (x l +ⱼ q (1 / 3) *ⱼ Jet.square (y l)) *ⱼ B l j *ⱼ B l k
  let mass := massWeightJet b i
  let massDelta := y 0 *ⱼ mass 0 +ⱼ y 1 *ⱼ mass 1 +ⱼ y 2 *ⱼ mass 2
  let row := fun l => mass 0 *ⱼ B 0 l +ⱼ mass 1 *ⱼ B 1 l +ⱼ mass 2 *ⱼ B 2 l
  let total := Jet.square (q 1 +ⱼ Jet.inv (Jet.square r *ⱼ r))
  let massFactor := (q 1 +ⱼ Jet.neg (massDelta *ⱼ Jet.inv (q 3 *ⱼ total))) *ⱼ
    Jet.inv (q 4 *ⱼ total)
  jetGamma b i *ⱼ edges +ⱼ scaleJet b i *ⱼ
    ((q (-9 / 4) *ⱼ (entropy 0 +ⱼ entropy 1 +ⱼ entropy 2)) +ⱼ
      massFactor *ⱼ row j *ⱼ row k)

private def debitedOccupationJet (j k : Fin 3) : AxisJet b i :=
  let B := jetBasis b i
  occupationJet b i j k +ⱼ
    ((B 0 j *ⱼ B 0 k +ⱼ B 1 j *ⱼ B 1 k +ⱼ B 2 j *ⱼ B 2 k) *ⱼ
      Jet.neg (jetConst b i (1 / 1024)))

private def signedJet (j : Fin 3) : AxisJet b i :=
  let q := jetConst b i
  let v₀ := lowerFactorJet b i *ⱼ jetEdgeRow b i 1 j
  let v₂ := upperFactorJet b i *ⱼ jetBasis b i 1 j
  let res := residualJet b i *ⱼ Jet.inv (q 2 *ⱼ pivotJet b i)
  (v₀ +ⱼ v₂ +ⱼ (res *ⱼ
    Jet.neg ((q 1 +ⱼ Jet.neg (kJet b i)) *ⱼ v₀ +ⱼ
      Jet.neg ((q 1 +ⱼ kJet b i) *ⱼ v₂)))) *ⱼ q (1 / 2)

def matrixJet (k : Fin 10) : AxisJet b i :=
  ![debitedOccupationJet b i 0 0, debitedOccupationJet b i 0 1, debitedOccupationJet b i 0 2,
    signedJet b i 0, debitedOccupationJet b i 1 1, debitedOccupationJet b i 1 2, signedJet b i 1,
    debitedOccupationJet b i 2 2, signedJet b i 2, pJet b i] k

def blockIndex (i : Fin 4) : Fin 3 ⊕ Fin 1 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0] i

def entryIndices (k : Fin 10) : Fin 4 × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)] k

noncomputable def pointOffsets (z : Fin 5 → ℝ) := offsets (z 1) (z 2) (z 3)

noncomputable def matrixEntry (z : Fin 5 → ℝ) (k : Fin 10) : ℝ :=
  let (j, l) := entryIndices k
  lowerMatrix (z 0) (pointOffsets z) (blockIndex j) (blockIndex l)

private abbrev atPoint {b : Box} {i : Fin 4} (z : Fin 5 → ℝ) (j : AxisJet b i) : ℝ :=
  value z (Checked.expr (Jet.val j))

private theorem offsetJet_value (z : Fin 5 → ℝ) (k : Fin 3) :
    atPoint z (offsetJet b i k) = pointOffsets z k := by
  fin_cases k <;>
    simp [offsetJet, pointOffsets, offsets, jetCoord, jetConst, atPoint, Jet.coord_value,
      Jet.const_value, Jet.add_value, Jet.mul_value, Jet.neg_value, coord_cast_one, coord_cast_two,
      coord_cast_three, sub_eq_add_neg]

private theorem gibbsJet_value (z : Fin 5 → ℝ) (k : Fin 3) :
    atPoint z (gibbsJet b i k) = gibbsLevels (z 0) k.castSucc := by
  fin_cases k <;>
    simp [gibbsJet, gibbsLevels, jetCoord, atPoint, Jet.coord_value, Jet.inv_value,
      Jet.square_value, coord_cast_zero]

private theorem levelJet_value (z : Fin 5 → ℝ) (k : Fin 3) :
    atPoint z (levelJet b i k) = levels (z 0) (pointOffsets z) k := by
  change value z (Checked.expr (Jet.val (gibbsJet b i k +ⱼ offsetJet b i k))) = _
  rw [Jet.add_value]
  have hg : value z (Checked.expr (Jet.val (gibbsJet b i k))) =
      gibbsLevels (z 0) k.castSucc := by
    simpa only [atPoint] using (gibbsJet_value (b := b) (i := i) z k)
  have ho : value z (Checked.expr (Jet.val (offsetJet b i k))) = pointOffsets z k := by
    simpa only [atPoint] using (offsetJet_value (b := b) (i := i) z k)
  rw [hg, ho]
  rfl

private theorem tJet_value (z : Fin 5 → ℝ) : atPoint z (tJet b i) = z 0 - 1 := by
  simp [tJet, jetCoord, jetConst, atPoint, Jet.coord_value, Jet.const_value, Jet.add_value,
    coord_cast_zero, sub_eq_add_neg]

private theorem leftJet_value (z : Fin 5 → ℝ) :
    atPoint z (normalizedLeftGapJet b i) = leftGap (z 0) (pointOffsets z) := by
  simp [normalizedLeftGapJet, atPoint, pointOffsets, offsets, leftGap, Jet.add_value,
    Jet.inv_value, Jet.square_value, Jet.mul_value, Jet.neg_value, Jet.coord_value,
    Jet.const_value, sub_eq_add_neg, div_eq_mul_inv]

private theorem middleJet_value (z : Fin 5 → ℝ) :
    atPoint z (middleJet b i) = middleGap (z 0) (pointOffsets z) := by
  simp [middleJet, atPoint, Jet.mul_value, Jet.add_value, Jet.neg_value, Jet.inv_value,
    offsetJet_value, tJet_value, jetCoord, jetConst, Jet.const_value, Jet.coord_value,
    coord_cast_three, middleGap, pointOffsets, offsets, sub_eq_add_neg, div_eq_mul_inv] <;> ring

private theorem rightJet_value (z : Fin 5 → ℝ) :
    atPoint z (rightJet b i) = rightGap (z 0) (pointOffsets z) := by
  simp [rightJet, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.inv_value,
    offsetJet_value, tJet_value, jetCoord, Jet.coord_value, coord_cast_zero,
    rightGap, sub_eq_add_neg, div_eq_mul_inv] <;> ring

private theorem biasFactorJet_value (z : Fin 5 → ℝ) (u v s : AxisJet b i) :
    atPoint z (biasFactorJet b i u v s) =
      biasFactor (z 0) (atPoint z u) (atPoint z v) (atPoint z s) := by
  simp [biasFactorJet, atPoint, biasFactor, jetFieldOverGap_value, jetE_value, tJet_value,
    Jet.add_value, Jet.mul_value, Jet.square_value, jetConst, Jet.const_value]

private theorem middleBiasJet_value (z : Fin 5 → ℝ) :
    atPoint z (middleBiasJet b i) = middleBias (z 0) (pointOffsets z) := by
  simp only [middleBiasJet, middleBias, biasFactorJet_value, levelJet_value, middleJet_value]

private theorem mixtureJet_value (z : Fin 5 → ℝ) :
    atPoint z (mixtureJet b i) = mixture (z 0) (pointOffsets z) := by
  simp [mixtureJet, mixture, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value, jetConst,
    Jet.const_value, levelJet_value, middleBiasJet_value, jetC_value, middleJet_value,
    div_eq_mul_inv, sub_eq_add_neg] <;> ring

private theorem lowerAdjacentJet_value (z : Fin 5 → ℝ) :
    atPoint z (lowerAdjacentJet b i) = lowerAdjacent (z 0) (pointOffsets z) := by
  simp [lowerAdjacentJet, adjacentJet, lowerAdjacent, atPoint, Jet.add_value, Jet.mul_value,
    Jet.neg_value, leftJet_value, middleJet_value, levelJet_value, jetC_value, jetE_value,
    tJet_value, jetConst, Jet.const_value, sub_eq_add_neg] <;> ring

private theorem upperAdjacentJet_value (z : Fin 5 → ℝ) :
    atPoint z (upperAdjacentJet b i) = upperAdjacent (z 0) (pointOffsets z) := by
  simp [upperAdjacentJet, adjacentJet, upperAdjacent, atPoint, Jet.add_value, Jet.mul_value,
    Jet.neg_value, rightJet_value, middleJet_value, levelJet_value, jetC_value, jetE_value,
    tJet_value, jetConst, Jet.const_value, sub_eq_add_neg] <;> ring

private theorem p₀Jet_value (z : Fin 5 → ℝ) :
    atPoint z (p₀Jet b i) = lowerWeight (z 0) (pointOffsets z) := by
  simp [p₀Jet, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.square_value,
    leftJet_value, middleJet_value, levelJet_value, jetC_value, lowerAdjacentJet_value,
    mixtureJet_value, jetConst, Jet.const_value, lowerWeight, lowerAdjacent, mixture,
    middleBias, biasFactor, scaledMixture] <;> ring

private theorem p₂Jet_value (z : Fin 5 → ℝ) :
    atPoint z (p₂Jet b i) = upperWeight (z 0) (pointOffsets z) := by
  simp [p₂Jet, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.square_value,
    rightJet_value, middleJet_value, levelJet_value, jetC_value, upperAdjacentJet_value,
    mixtureJet_value, jetConst, Jet.const_value, upperWeight, upperAdjacent, mixture,
    middleBias, biasFactor, scaledMixture] <;> ring

private theorem pJet_value (z : Fin 5 → ℝ) :
    atPoint z (pJet b i) = weight (z 0) (pointOffsets z) := by
  simp [pJet, weight, atPoint, Jet.add_value, Jet.mul_value, p₀Jet_value, p₂Jet_value,
    middleJet_value, middleBiasJet_value, jetConst, Jet.const_value, div_eq_mul_inv]

private theorem kJet_value (z : Fin 5 → ℝ) :
    atPoint z (kJet b i) = asymmetry (z 0) (pointOffsets z) := by
  simp [kJet, pkJet, atPoint, asymmetry, Jet.add_value, Jet.neg_value, Jet.mul_value,
    Jet.inv_value, p₀Jet_value, p₂Jet_value, pJet_value, div_eq_mul_inv, sub_eq_add_neg]

private theorem longJet_value (z : Fin 5 → ℝ) :
    atPoint z (longJet b i) = longCrossing (z 0) (pointOffsets z) := by
  simp [longJet, longCrossing, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
    leftJet_value, middleJet_value, rightJet_value, jetC_value, jetE_value, levelJet_value,
    tJet_value, jetConst, Jet.const_value, sub_eq_add_neg] <;> (try ring) <;> simp

private theorem lowerFactorJet_value (z : Fin 5 → ℝ) :
    atPoint z (lowerFactorJet b i) = lowerTiltFactor (z 0) (pointOffsets z) := by
  simp [lowerFactorJet, lowerTiltFactor, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
    Jet.inv_value, Jet.square_value, jetEndpointLinear_value, jetEndpointField_value,
    levelJet_value, offsetJet_value, tJet_value, jetCoord, Jet.coord_value, coord_cast_zero,
    sub_eq_add_neg, div_eq_mul_inv]

private theorem upperFactorJet_value (z : Fin 5 → ℝ) :
    atPoint z (upperFactorJet b i) = upperTiltFactor (z 0) (pointOffsets z) := by
  simp [upperFactorJet, upperTiltFactor, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
    Jet.inv_value, jetEndpointLinear_value, jetEndpointField_value, levelJet_value,
    offsetJet_value, tJet_value, jetCoord, Jet.coord_value, coord_cast_zero,
    jetConst, Jet.const_value, sub_eq_add_neg, div_eq_mul_inv] <;> ring

private theorem g₀Jet_value (z : Fin 5 → ℝ) :
    atPoint z (g₀Jet b i) = lowerSlope (z 0) (pointOffsets z) := by
  simp [g₀Jet, lowerSlope, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.inv_value,
    lowerFactorJet_value, offsetJet_value, tJet_value, jetCoord, Jet.coord_value, coord_cast_zero,
    sub_eq_add_neg, div_eq_mul_inv, mul_assoc]

private theorem g₂Jet_value (z : Fin 5 → ℝ) :
    atPoint z (g₂Jet b i) = upperSlope (z 0) (pointOffsets z) := by
  simp [g₂Jet, upperSlope, atPoint, Jet.mul_value, Jet.inv_value, upperFactorJet_value,
    offsetJet_value, tJet_value, div_eq_mul_inv, mul_assoc]

private theorem residualJet_value (z : Fin 5 → ℝ) :
    atPoint z (residualJet b i) = residual (z 0) (pointOffsets z) := by
  simp [residualJet, WuCubicLowerCoefficients.residual, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
    kJet_value, g₀Jet_value, g₂Jet_value, jetConst, Jet.const_value, sub_eq_add_neg]

private theorem pivotJet_value (z : Fin 5 → ℝ) :
    atPoint z (pivotJet b i) = linearPivot (z 0) (pointOffsets z) := by
  simp [pivotJet, linearPivot, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
    longJet_value, kJet_value, residualJet_value, sub_eq_add_neg]

set_option maxHeartbeats 900000 in
theorem scalarJet_value (z : Fin 5 → ℝ) (j : Fin 11) :
    value z (Checked.expr (Jet.val (scalarJet b i j))) = tests (z 0) (pointOffsets z) j := by
  change atPoint z (scalarJet b i j) = _
  fin_cases j <;>
    simp [scalarJet, tests, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
      Jet.square_value, jetConst, Jet.const_value, leftJet_value, middleJet_value, rightJet_value,
      levelJet_value, biasFactorJet_value, lowerBias, upperBias, ellJet, middleBiasJet_value,
      mixtureJet_value, lowerAdjacentJet_value, upperAdjacentJet_value, p₀Jet_value, p₂Jet_value,
      pJet_value, pkJet, g₀Jet_value, g₂Jet_value, longJet_value, pivotJet_value,
      sub_eq_add_neg, div_eq_mul_inv] <;> ring

private theorem massWeightJet_value (z : Fin 5 → ℝ) (k : Fin 3) :
    atPoint z (massWeightJet b i k) = massWeights (z 0) (pointOffsets z) k := by
  simp [massWeightJet, massWeights, atPoint, Jet.add_value, Jet.mul_value, Jet.square_value,
    gibbsJet_value, offsetJet_value, jetConst, Jet.const_value]

private theorem scaleJet_value (z : Fin 5 → ℝ) :
    atPoint z (scaleJet b i) = entropyScale (z 0) := by
  simp [scaleJet, entropyScale, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
    Jet.inv_value, Jet.square_value, tJet_value, jetCoord, Jet.coord_value, coord_cast_zero,
    jetConst, Jet.const_value, sub_eq_add_neg, div_eq_mul_inv]

private theorem occupationJet_value (z : Fin 5 → ℝ) (j k : Fin 3) :
    atPoint z (occupationJet b i j k) = scaledOccupation (z 0) (pointOffsets z) j k := by
  simp [occupationJet, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.square_value,
    Jet.inv_value, jetConst, Jet.const_value, jetCoord, Jet.coord_value, coord_cast_zero,
    jetGamma_value, jetEdgeRow_value, jetBasis_value, levelJet_value, offsetJet_value,
    massWeightJet_value, scaleJet_value, scaledOccupation, edgeWeights, entropyWeights,
    levels, massRow, massChange, gibbsMass, Fin.sum_univ_three, Fin.sum_univ_four,
    pow_three, div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc] <;> (try ring) <;> simp

private theorem debitJet_value (z : Fin 5 → ℝ) (j k : Fin 3) :
    atPoint z (debitedOccupationJet b i j k) =
      scaledOccupation (z 0) (pointOffsets z) j k - (∑ l, basis l j * basis l k) / 1024 := by
  simp [debitedOccupationJet, atPoint, Jet.add_value, Jet.mul_value, Jet.neg_value,
    occupationJet_value, jetBasis_value, jetConst, Jet.const_value, Fin.sum_univ_three,
    sub_eq_add_neg, div_eq_mul_inv]

private theorem signedJet_value (z : Fin 5 → ℝ) (j : Fin 3) :
    atPoint z (signedJet b i j) = signedTiltRow (z 0) (pointOffsets z)
      (asymmetry (z 0) (pointOffsets z)) (residual (z 0) (pointOffsets z))
      (linearPivot (z 0) (pointOffsets z)) j / 2 := by
  simp [signedJet, signedTiltRow, lowerTilt, upperTilt, atPoint, Jet.add_value, Jet.mul_value,
    Jet.inv_value, Jet.neg_value, jetConst, Jet.const_value, lowerFactorJet_value,
    upperFactorJet_value, jetEdgeRow_value, jetBasis_value, residualJet_value, pivotJet_value,
    kJet_value, sub_eq_add_neg, div_eq_mul_inv] <;> ring

theorem matrixJet_value (z : Fin 5 → ℝ) (j : Fin 10) :
    value z (Checked.expr (Jet.val (matrixJet b i j))) = matrixEntry z j := by
  change atPoint z (matrixJet b i j) = _
  fin_cases j <;>
    simp [matrixJet, matrixEntry, entryIndices, blockIndex, lowerMatrix, Matrix.fromBlocks,
      debitJet_value, signedJet_value, pJet_value]

end

end D5.S3.Quantum.Semigroups.WuCubicLowerJets
