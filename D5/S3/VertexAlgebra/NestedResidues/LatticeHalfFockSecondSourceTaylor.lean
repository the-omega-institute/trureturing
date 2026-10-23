/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete current/second-source rational field and supported Taylor extraction. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
import D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction

/-! The local-coordinate calculation adapts the signed Laurent proof in
LatticeHalfFockOuterTaylorEvaluation to the original J/B diagonal.
Its Hahn and binomial infrastructure is from mathlib (Apache 2.0).
The actual field suppliers retain their attribution in the inherited owners.
No locality assertion is made for a numerator monomial or ordered half. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.FiniteConvolution
open CollisionRationalExpansions.OrderedRationalExpansion
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.HahnFiberScalar
open CollisionRationalExpansions.FullOrderSpectatorPole
open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.RationalFusedResidue
open OrderedCollisionCoordinates.ContextualLaurentKernel
open OrderedCollisionCoordinates.AdjacentFullOrders
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open LabelledRationalClearing.GlobalRationalCurry
open OrderedCollisionCoordinates.LocalResidueCurrying
open scoped BigOperators VertexOperator RatFunc
noncomputable section

private theorem translate_variable {E : Type*} [Field E] (a : E) :
    IsFractionRing.ringEquivOfRingEquiv
      (Polynomial.algEquivAevalXAddC a).toRingEquiv (RatFunc.X : RatFunc E) =
        RatFunc.X + RatFunc.C a := by
  rw [← RatFunc.algebraMap_X, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [Polynomial.algEquivAevalXAddC_apply]

/-- Currying a monomial at the current/second-source diagonal gives two
translated Laurent factors and the original independent spectator pole. -/
private theorem second_source_local_monomial (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (e : Exponent 3) (c : ℂ) (w : ℤ) :
    let E := LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)
    let v : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨1, by decide⟩
    let z : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨2, by decide⟩
    let C : E := algebraMap _ E
      (AddMonoidAlgebra.single
        (fun j : LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) => e j.val) c)
    OrderedCollisionCoordinates.LocalResidueCurrying.localRational ℂ (0 : Fin 3)
      ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨2, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e c) /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))) =
      RatFunc.C (C * (v - z) ^ (-(K : ℤ))) *
        (RatFunc.X + RatFunc.C z) ^ e 0 *
        RatFunc.X ^ (w - (vectorFrequencyBound D b + 1 : ℕ)) *
        (RatFunc.X + RatFunc.C (z - v)) ^ (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ)) := by
  classical
  dsimp only
  have pairs : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  have clear : weightedClearingPolynomial (threeOrders D a b K) =
      pairPolynomial (0 : Fin 3) 1 ^ (vectorFrequencyBound D a + 1) *
      pairPolynomial (0 : Fin 3) 2 ^ (vectorFrequencyBound D b + 1) *
      pairPolynomial (1 : Fin 3) 2 ^ K := by
    simp [weightedClearingPolynomial, pairs, threeOrders]
    ring_nf
  rw [clear]
  simp only [OrderedCollisionCoordinates.LocalResidueCurrying.localRational,
    RingHom.comp_apply, map_mul, map_div₀, map_pow, map_zpow₀,
    LabelledRationalClearing.WeightedActualQ.globalDiagonal,
    LabelledRationalClearing.GlobalRationalCurry.curryRational,
    IsFractionRing.lift_algebraMap]
  rw [LabelledRationalClearing.PairDifferenceLocalization.curryPolynomial_single]
  have mapcurrent :=
    LabelledRationalClearing.PairDifferenceLocalization.curry_variable_z ℂ (0 : Fin 3)
  have map0label := mapcurrent
  have mapv := LabelledRationalClearing.PairDifferenceLocalization.curry_variable_remaining
    ℂ (0 : Fin 3) ⟨1, by decide⟩
  have mapz := LabelledRationalClearing.PairDifferenceLocalization.curry_variable_remaining
    ℂ (0 : Fin 3) ⟨2, by decide⟩
  have mapzlabel := mapz
  change LabelledRationalClearing.GlobalRationalCurry.curryPolynomial ℂ (0 : Fin 3)
    (variablePolynomial (0 : Fin 3)) = _ at mapcurrent
  change LabelledRationalClearing.GlobalRationalCurry.curryPolynomial ℂ (0 : Fin 3)
    (variablePolynomial (1 : Fin 3)) = _ at mapv
  change LabelledRationalClearing.GlobalRationalCurry.curryPolynomial ℂ (0 : Fin 3)
    (variablePolynomial (2 : Fin 3)) = _ at mapz
  simp only [pairPolynomial,
    LabelledRationalClearing.PairDifferenceLocalization.pairPolynomial,
    map_sub, mapcurrent, mapv, mapz, map0label, mapzlabel]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_mul, map_zpow₀,
    OrderedCollisionResidues.LocalResidueLinear.translate_constant]
  simp only [OrderedCollisionCoordinates.LocalResidueCurrying.translate, translate_variable]
  simp only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]
  rw [zpow_add₀ RatFunc.X_ne_zero]
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Finite coefficient-field value of a signed monomial at the J/B diagonal. -/
def secondSourceMonomialValue (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (e : Exponent 3) (c : ℂ) (w : ℤ) :
    LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3) :=
    let E := LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)
    let v : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨1, by decide⟩
    let z : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
      ℂ (0 : Fin 3) ⟨2, by decide⟩
    let C : E := algebraMap _ E
      (AddMonoidAlgebra.single
        (fun j : LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) => e j.val) c)
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
      if w - (M : ℤ) < 0 then
        (C * (v - z) ^ (-(K : ℤ))) * (z ^ e 0 * (z - v) ^ (-(L : ℤ))) *
          ∑ u ∈ Finset.range ((-(w - (M : ℤ)) - 1).toNat + 1),
            z⁻¹ ^ u * ((Ring.choose (e 0) u : ℤ) : E) *
              ((z - v)⁻¹ ^ ((-(w - (M : ℤ)) - 1).toNat - u) *
                ((Ring.choose (-(L : ℤ)) ((-(w - (M : ℤ)) - 1).toNat - u) : ℤ) : E))
      else 0

/-- The genuine current/second-source local residue of a signed Laurent
monomial, before any spectator ordering. The remaining pole keeps its own K. -/
private theorem second_source_monomial_residue (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (e : Exponent 3) (c : ℂ) (w : ℤ) :
    OrderedCollisionCoordinates.LocalResidueCurrying.localResidue ℂ (0 : Fin 3)
      ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨2, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e c) /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))) =
      secondSourceMonomialValue D a b K e c w := by
  classical
  dsimp only [secondSourceMonomialValue]
  unfold OrderedCollisionCoordinates.LocalResidueCurrying.localResidue
  rw [second_source_local_monomial]
  let E := LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)
  let v : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
    ℂ (0 : Fin 3) ⟨1, by decide⟩
  let z : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
    ℂ (0 : Fin 3) ⟨2, by decide⟩
  have hz : z ≠ 0 := by
    change (algebraMap
      (LabelledRationalClearing.GlobalRationalCurry.CoefficientPolynomial ℂ (0 : Fin 3)) E)
      (AddMonoidAlgebra.single (Pi.single ⟨2, by decide⟩ (1 : ℤ)) (1 : ℂ)) ≠ 0
    have h : (AddMonoidAlgebra.single
        (Pi.single (⟨2, by decide⟩ :
          LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3)) (1 : ℤ) :
          LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) → ℤ)
        (1 : ℂ)) ≠ 0 := by simp
    simpa only [map_zero] using
      (IsFractionRing.injective
        (LabelledRationalClearing.GlobalRationalCurry.CoefficientPolynomial ℂ (0 : Fin 3)) E).ne h
  have hzv : z - v ≠ 0 := by
    apply sub_ne_zero.mpr
    intro equality
    have labels := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable_injective
      ℂ (0 : Fin 3) equality
    have impossible := congrArg Subtype.val labels
    exact (by decide : (2 : Fin 3) ≠ 1) impossible
  have mapC (h : E) : algebraMap (RatFunc E) (LaurentSeries E) (RatFunc.C h) =
      HahnSeries.C h := by
    rw [← RatFunc.algebraMap_C,
      ← IsScalarTower.algebraMap_apply (Polynomial E) (RatFunc E) (LaurentSeries E)]
    simp [Polynomial.algebraMap_hahnSeries_apply]
  dsimp only [E] at mapC
  simp only [map_mul, map_zpow₀, map_add, RatFunc.coe_X]
  simp_rw [mapC]
  rw [← map_zpow₀ (HahnSeries.C : E →+* LaurentSeries E),
    ← map_mul (HahnSeries.C : E →+* LaurentSeries E)]
  rw [show ∀ (h : E) (p k q : ℤ),
      HahnSeries.C h * (HahnSeries.single 1 1 + HahnSeries.C z) ^ p *
          (HahnSeries.single 1 1 : LaurentSeries E) ^ k *
          (HahnSeries.single 1 1 + HahnSeries.C (z - v)) ^ q =
        HahnSeries.single k h * ((HahnSeries.single 1 1 + HahnSeries.C z) ^ p *
          (HahnSeries.single 1 1 + HahnSeries.C (z - v)) ^ q) by
    intro h p k q
    rw [← RatFunc.single_zpow, HahnSeries.C_apply]
    calc
      _ = (HahnSeries.single 0 h * HahnSeries.single k (1 : E)) *
          ((HahnSeries.single 1 1 + HahnSeries.C z) ^ p *
            (HahnSeries.single 1 1 + HahnSeries.C (z - v)) ^ q) := by ring
      _ = _ := by rw [HahnSeries.single_mul_single, zero_add, mul_one]
  ]
  exact local_laurent_pair_residue z (z - v) _ hz hzv _ _ _

/-- Evaluate the original finite Laurent numerator at the actual J/B
local pole by its full finite monomial sum. Negative exponents are retained. -/
private theorem second_source_laurent_residue (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (w : ℤ) :
    OrderedCollisionCoordinates.LocalResidueCurrying.localResidue ℂ (0 : Fin 3)
      ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨2, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) P /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))) =
      ∑ e ∈ P.coeff.support, secondSourceMonomialValue D a b K e (P.coeff e) w := by
  classical
  let residue := OrderedCollisionResidues.CollisionResidueMaps.localResidueHom
    ℂ 1 0 (0 : Fin 3) ⟨2, by decide⟩
  have splitP : (∑ e ∈ P.coeff.support,
      AddMonoidAlgebra.single e (P.coeff e)) = P := by
    exact AddMonoidAlgebra.sum_coeff_single P
  have splitR :
      LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
          ⟨2, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) P /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) =
      ∑ e ∈ P.coeff.support,
        LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
          ⟨2, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e (P.coeff e)) /
          algebraMap _ (CommonRational ℂ 3)
            (weightedClearingPolynomial (threeOrders D a b K))) := by
    rw [← Finset.mul_sum, ← Finset.sum_div, ← map_sum, splitP]
  change residue _ = _
  rw [splitR, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact second_source_monomial_residue D a b K e (P.coeff e) w

abbrev SecondSourceField := CoefficientField ℂ (0 : Fin 3)

/-- The complete finite J/B residue in one rational coefficient field.
The fractional shift is multiplication by z^(-alpha), before either ordering. -/
def secondSourceRational (M j : ℕ) (R : CommonRational ℂ 3) : SecondSourceField :=
  ∑ alpha ∈ Finset.range (M - j),
    algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
      (AddMonoidAlgebra.single (Pi.single (⟨2, by decide⟩ : Remaining (0 : Fin 3)) (-(alpha : ℤ)))
        (Ring.choose (-(1 : ℂ) / 2) alpha)) *
      localResidue ℂ (0 : Fin 3) ⟨2, by decide⟩
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
          ⟨2, by decide⟩ ^ ((j : ℤ) + alpha) * R)

def secondSourceLeftOrder : Fin 2 ≃ Remaining (0 : Fin 3) := finSuccAboveEquiv 0
def secondSourceRightOrder : Fin 2 ≃ Remaining (0 : Fin 3) :=
  (Equiv.swap 0 1).trans secondSourceLeftOrder

private theorem coefficient_monomial (pre post : ℕ) (z : Fin ((pre + 1) + post))
    (tau : Fin (pre + post) ≃ Remaining z) (e : Remaining z → ℤ) (c : ℂ) :
    coefficientHahn ℂ pre post z tau (algebraMap _ (CoefficientField ℂ z)
      (AddMonoidAlgebra.single e c)) =
      HahnSeries.single (remainingExponents pre post z tau e) c := by
  simp only [coefficientHahn, IsFractionRing.lift_algebraMap,
    remainingPolynomial, polynomialViaEquiv, RingHom.comp_apply]
  change scalarPolynomial
    ((AddMonoidAlgebra.domCongr ℂ ℂ (remainingExponents pre post z tau))
      (AddMonoidAlgebra.single e c)) = _
  rw [AddMonoidAlgebra.domCongr_single, scalarPolynomial_single]

private theorem left_shift (alpha : ℕ) (T : SecondSourceField) (k l : ℤ) :
    (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder
      (algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
        (AddMonoidAlgebra.single (Pi.single (⟨2, by decide⟩ : Remaining (0 : Fin 3)) (-(alpha : ℤ)))
          (Ring.choose (-(1 : ℂ) / 2) alpha)) * T)).coeff
        (exponents 2 ![-l - 1, -k - 1]) =
      Ring.choose (-(1 : ℂ) / 2) alpha *
        (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder T).coeff
          (exponents 2 ![-l - 1, -k + alpha - 1]) := by
  rw [map_mul, coefficient_monomial, HahnSeries.coeff_single_mul]
  congr 2
  change toLex (-k - 1 - -(alpha : ℤ),
    toLex (-l - 1 - 0, ())) = toLex (-k + alpha - 1, toLex (-l - 1, ()))
  exact congrArg toLex (Prod.ext (by omega)
    (congrArg toLex (Prod.ext (by omega) rfl)))

private theorem right_shift (alpha : ℕ) (T : SecondSourceField) (k l : ℤ) :
    (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder
      (algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
        (AddMonoidAlgebra.single (Pi.single (⟨2, by decide⟩ : Remaining (0 : Fin 3)) (-(alpha : ℤ)))
          (Ring.choose (-(1 : ℂ) / 2) alpha)) * T)).coeff
        (exponents 2 ![-k - 1, -l - 1]) =
      Ring.choose (-(1 : ℂ) / 2) alpha *
        (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder T).coeff
          (exponents 2 ![-k + alpha - 1, -l - 1]) := by
  rw [map_mul, coefficient_monomial, HahnSeries.coeff_single_mul]
  congr 2
  change toLex (-l - 1 - 0,
    toLex (-k - 1 - -(alpha : ℤ), ())) = toLex (-l - 1, toLex (-k + alpha - 1, ()))
  exact congrArg toLex (Prod.ext (by omega)
    (congrArg toLex (Prod.ext (by omega) rfl)))

private theorem second_source_coefficients (M j : ℕ) (R : CommonRational ℂ 3)
    (k l : ℤ) :
    lastSourceLocalQ 0 true 1 j M k l R =
      (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder
        (secondSourceRational M j R)).coeff (exponents 2 ![-l - 1, -k - 1]) ∧
    lastSourceLocalQ 0 false 1 j M k l R =
      (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder
        (secondSourceRational M j R)).coeff (exponents 2 ![-k - 1, -l - 1]) := by
  have range_eq : ((M : ℤ) - j).toNat = M - j := by omega
  constructor
  · unfold lastSourceLocalQ secondSourceRational
    simp only [ite_true, range_eq, map_sum, HahnSeries.coeff_sum]
    apply Finset.sum_congr rfl
    intro alpha ha
    rw [left_shift, fused_residue_square]
    simp only [Int.cast_one]
    with_unfolding_all rfl
  · unfold lastSourceLocalQ secondSourceRational
    simp only [Bool.false_eq_true, ite_false, range_eq, map_sum, HahnSeries.coeff_sum]
    apply Finset.sum_congr rfl
    intro alpha ha
    rw [right_shift, fused_residue_square]
    simp only [Int.cast_one]
    with_unfolding_all rfl

/-- Explicit signed Laurent evaluation of the complete inner field. -/
def secondSourceTaylorRational (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (j : ℕ) : SecondSourceField :=
  ∑ alpha ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
    algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
      (AddMonoidAlgebra.single (Pi.single (⟨2, by decide⟩ : Remaining (0 : Fin 3)) (-(alpha : ℤ)))
        (Ring.choose (-(1 : ℂ) / 2) alpha)) *
      ∑ e ∈ P.coeff.support,
        secondSourceMonomialValue D a b K e (P.coeff e) ((j : ℤ) + alpha)

private theorem second_source_rational_evaluation (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) :
    secondSourceRational (vectorFrequencyBound D b + 1) j
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) =
      secondSourceTaylorRational D a b K P j := by
  unfold secondSourceRational secondSourceTaylorRational
  simp_rw [second_source_laurent_residue]

/- The local two-order expansion can only contribute on the sharp joint
support. This algebraic bridge is independent of any ordered-half locality
claim; it is the exponent calculation used after the complete field has been
expanded. -/
theorem second_source_sharp_joint_exponent
    (e : Exponent 3) (n degree : ℤ)
    (coefficient_degree : totalExponent e = degree - n - 1)
    (alpha a k beta b : ℕ)
    (joint_support : (alpha + a + beta + b : ℤ) = degree) :
    totalExponent e - alpha - a - beta - b = -n - 1 := by
  rw [coefficient_degree]
  norm_num at joint_support ⊢
  omega

/- The theorem keeps the original coefficient equation and signed target
degree. A support element of P therefore supplies the degree hypothesis, and
the preceding bridge gives the final z-mode exponent -n-1 for every sharp
inner/outer Taylor tuple. -/
theorem actual_second_source_sharp_support
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n degree : ℤ) (j : ℕ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (degree_equation : degree - n - 1 =
      (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0) :
    ∀ e ∈ P.coeff.support, ∀ alpha a' k beta b' : ℕ,
      (alpha + a' + k = vectorFrequencyBound D b + 1 - j - 1) →
      (alpha + a' + beta + b' : ℤ) = degree →
      totalExponent e - alpha - a' - beta - b' = -n - 1 ∧
      k < vectorFrequencyBound D b + 1 := by
  intro e he alpha a' k beta b' hinner hjoint
  have hcoeff : P.coeff e ≠ 0 := by
    exact Finsupp.mem_support_iff.mp he
  have hdegree : totalExponent e = degree - n - 1 := by
    have h := coefficients e
    by_contra hne
    rw [if_neg (by
      intro hEq
      apply hne
      simpa [degree_equation] using hEq)] at h
    exact hcoeff h
  exact ⟨second_source_sharp_joint_exponent e n degree hdegree alpha a' k beta b' hjoint, by omega⟩

/-- Coefficients in the v,z order of the complete rational inner field. -/
def secondSourceForward (T : SecondSourceField) (k l : ℤ) : ℂ :=
  (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder T).coeff
    (exponents 2 ![-k - 1, -l - 1])

/-- Coefficients in the z,v order of the same complete rational inner field. -/
def secondSourceBackward (T : SecondSourceField) (k l : ℤ) : ℂ :=
  (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder T).coeff
    (exponents 2 ![-k - 1, -l - 1])

private theorem rational_mode_fibers (T : SecondSourceField) (r n : ℤ) :
    Function.HasFiniteSupport (fun u : ℕ =>
      BinomialKernelDelta.chooseSign r u *
        secondSourceForward T (r - u) (n + u)) ∧
    Function.HasFiniteSupport (fun u : ℕ =>
      BinomialKernelDelta.chooseSign r u *
        secondSourceBackward T (r + n - u) u) := by
  open OrderedCollisionCoordinates.ContextualLaurentKernel in
  constructor
  · have finite := (ContextualKernelExtraction.contextual_kernel_extraction ℂ 0 0 r
      (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder T)
      (pairIndex 0 0 (toLex (-n - 1, -1)))).1
    have index (u : ℕ) :
        pairIndex 0 0 (toLex (-n - 1, -1)) -
          pairIndex 0 0 (toLex ((u : ℤ), r - u)) =
          exponents 2 ![-(r - u) - 1, -(n + u) - 1] := by
      change toLex (-n - 1 - u, toLex (-1 - (r - u), ())) =
        toLex (-(n + u) - 1, toLex (-(r - u) - 1, ()))
      exact congrArg toLex (Prod.ext (by omega)
    (congrArg toLex (Prod.ext (by omega) rfl)))
    simpa only [index, secondSourceForward, BinomialKernelDelta.chooseSign] using finite
  · have finite := (ContextualKernelExtraction.contextual_kernel_extraction ℂ 0 0 r
      (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder T)
      (pairIndex 0 0 (toLex (-1, -n - 1)))).1
    have index (u : ℕ) :
        pairIndex 0 0 (toLex (-1, -n - 1)) -
          pairIndex 0 0 (toLex ((u : ℤ), r - u)) =
          exponents 2 ![-(r + n - u) - 1, -(u : ℤ) - 1] := by
      change toLex ((-1 : ℤ) - u, toLex (-n - 1 - (r - u), ())) =
        toLex (-(u : ℤ) - 1, toLex (-(r + n - u) - 1, ()))
      exact congrArg toLex (Prod.ext (by omega)
    (congrArg toLex (Prod.ext (by omega) rfl)))
    simpa only [index, secondSourceBackward, BinomialKernelDelta.chooseSign] using finite

private theorem finite_range_fibers (B : ℕ) (f : ℕ → ℕ → ℂ)
    (finite : ∀ b, Function.HasFiniteSupport (f b)) :
    Function.HasFiniteSupport (fun p : ℕ × ℕ => if p.1 < B then f p.1 p.2 else 0) := by
  classical
  let S := (Finset.range B).biUnion fun b =>
    (finite b).toFinset.image (fun u => (b, u))
  apply S.finite_toSet.subset
  rintro ⟨b, u⟩ nonzero
  change (if b < B then f b u else 0) ≠ 0 at nonzero
  have hb : b < B := by
    by_contra outside
    exact nonzero (ite_eq_right outside)
  have hu : f b u ≠ 0 := by simpa only [ite_eq_left hb] using nonzero
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_range.mpr hb, Finset.mem_image.mpr ?_⟩
  exact ⟨u, (finite b).mem_toFinset.mpr hu, rfl⟩

/-- The actual joint mode fiber, with its finite fractional outer cutoff.
This definition does not assert a locality cutoff for an ordered half. -/
def secondSourceJointTerm (backward : Bool) (T : SecondSourceField)
    (r n : ℤ) (H : ℕ) (p : ℕ × ℕ) : ℂ :=
  if p.1 < ((H : ℤ) - r).toNat then
    BinomialKernelDelta.chooseSign (r + p.1) p.2 *
      (if backward then secondSourceBackward T (r + n - p.2) p.2
       else secondSourceForward T (r + p.1 - p.2) (n - p.1 + p.2))
  else 0

private theorem rational_joint_support (T : SecondSourceField) (r n : ℤ) (H : ℕ) :
    QReadoutSupported r H n (secondSourceForward T) (secondSourceBackward T) ∧
    Function.HasFiniteSupport (secondSourceJointTerm false T r n H) ∧
    Function.HasFiniteSupport (secondSourceJointTerm true T r n H) := by
  have fibers (beta : ℕ) := rational_mode_fibers T (r + beta) (n - beta)
  have fibers' (beta : ℕ) :
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign (r + beta) u *
          secondSourceForward T (r + beta - u) (n - beta + u)) ∧
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign (r + beta) u *
          secondSourceBackward T (r + n - u) u) := by
    simpa only [show ∀ u : ℕ, r + beta + (n - beta) - u = r + n - u by
      intro u; omega] using fibers beta
  refine ⟨fun beta _ => fibers' beta, ?_, ?_⟩
  · change Function.HasFiniteSupport (fun p : ℕ × ℕ =>
      if p.1 < ((H : ℤ) - r).toNat then
        BinomialKernelDelta.chooseSign (r + p.1) p.2 *
          secondSourceForward T (r + p.1 - p.2) (n - p.1 + p.2) else 0)
    exact finite_range_fibers ((H : ℤ) - r).toNat _ (fun beta => (fibers' beta).1)
  · change Function.HasFiniteSupport (fun p : ℕ × ℕ =>
      if p.1 < ((H : ℤ) - r).toNat then
        BinomialKernelDelta.chooseSign (r + p.1) p.2 *
          secondSourceBackward T (r + n - p.2) p.2 else 0)
    exact finite_range_fibers ((H : ℤ) - r).toNat _ (fun beta => (fibers' beta).2)

/-- One term of the finite rational numerator expansion, including its
fractional current shift before either Hahn expansion. -/
def secondSourceTerm (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (j alpha : ℕ) (e : Exponent 3) : SecondSourceField :=
  algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
    (AddMonoidAlgebra.single
      (Pi.single (⟨2, by decide⟩ : Remaining (0 : Fin 3)) (-(alpha : ℤ)))
      (Ring.choose (-(1 : ℂ) / 2) alpha)) *
    secondSourceMonomialValue D a b K e (P.coeff e) ((j : ℤ) + alpha)

/- The local inner Taylor index is exposed before any outer coefficient
calculation. This keeps the complete signed Laurent factors and the actual
finite cutoff visible, including the empty branch. -/
def secondSourceInnerTaylorTerm
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) : SecondSourceField :=
      let E := SecondSourceField
      let v : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
        ℂ (0 : Fin 3) ⟨1, by decide⟩
      let z : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
        ℂ (0 : Fin 3) ⟨2, by decide⟩
      let C : E := algebraMap _ E
        (AddMonoidAlgebra.single
          (fun q : LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) => e q.val)
          (P.coeff e))
      let L := vectorFrequencyBound D a + 1
      let M := vectorFrequencyBound D b + 1
      (algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) E
        (AddMonoidAlgebra.single
          (Pi.single (⟨2, by decide⟩ : Remaining (0 : Fin 3)) (-(alpha : ℤ)))
          (Ring.choose (-(1 : ℂ) / 2) alpha)) *
        ((C * (v - z) ^ (-(K : ℤ))) * (z ^ e 0 * (z - v) ^ (-(L : ℤ))) *
          ∑ u ∈ Finset.range (M - j - alpha),
            z⁻¹ ^ u * ((Ring.choose (e 0) u : ℤ) : E) *
              ((z - v)⁻¹ ^ (M - j - alpha - 1 - u) *
                ((Ring.choose (-(L : ℤ)) (M - j - alpha - 1 - u) : ℤ) : E))))

theorem second_source_monomial_taylor_index
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) (hα : alpha < vectorFrequencyBound D b + 1 - j) :
    secondSourceTerm D a b K P j alpha e =
      secondSourceInnerTaylorTerm D a b K P j alpha e := by
  classical
  dsimp only [secondSourceTerm, secondSourceMonomialValue]
  rw [if_pos (by omega : (j : ℤ) + alpha - (vectorFrequencyBound D b + 1 : ℕ) < 0)]
  congr 2
  have m : (-( (j : ℤ) + alpha - (vectorFrequencyBound D b + 1 : ℕ)) - 1).toNat =
      vectorFrequencyBound D b + 1 - j - alpha - 1 := by omega
  simp only [m]
  have hpos : 1 ≤ vectorFrequencyBound D b + 1 - j - alpha := by omega
  rw [Nat.sub_add_cancel hpos]

theorem second_source_taylor_inner_expansion
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j : ℕ) :
    secondSourceTaylorRational D a b K P j =
      ∑ alpha ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
        ∑ e ∈ P.coeff.support,
          secondSourceInnerTaylorTerm D a b K P j alpha e := by
  classical
  unfold secondSourceTaylorRational
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro alpha ha
  apply Finset.sum_congr rfl
  intro e he
  change secondSourceTerm D a b K P j alpha e = _
  rw [second_source_monomial_taylor_index D a b K P j alpha e
    (Finset.mem_range.mp ha)]

/-- Joint support includes the fractional inner index, the numerator
monomial, the fractional outer index and the outer mode-convolution index. -/
def secondSourceExpandedJointTerm (backward : Bool) (D : LatticeData)
    (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ)
    (r n : ℤ) (H : ℕ) (p : (ℕ × Exponent 3) × (ℕ × ℕ)) : ℂ :=
  if p.1 ∈ (Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support then
    secondSourceJointTerm backward (secondSourceTerm D a b K P j p.1.1 p.1.2) r n H p.2
  else 0

private theorem finite_parameter_fibers {ι κ : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → κ → ℂ)
    (finite : ∀ i, Function.HasFiniteSupport (f i)) :
    Function.HasFiniteSupport (fun p : ι × κ => if p.1 ∈ s then f p.1 p.2 else 0) := by
  classical
  let S := s.biUnion fun i => (finite i).toFinset.image (fun u => (i, u))
  apply S.finite_toSet.subset
  rintro ⟨i, u⟩ nonzero
  change (if i ∈ s then f i u else 0) ≠ 0 at nonzero
  have hi : i ∈ s := by
    by_contra outside
    exact nonzero (ite_eq_right outside)
  have hu : f i u ≠ 0 := by simpa only [ite_eq_left hi] using nonzero
  apply Finset.mem_biUnion.mpr
  exact ⟨i, hi, Finset.mem_image.mpr ⟨u, (finite i).mem_toFinset.mpr hu, rfl⟩⟩

set_option maxHeartbeats 1000000 in
private theorem second_source_expanded_support (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) (r n : ℤ) (H : ℕ) :
    Function.HasFiniteSupport (secondSourceExpandedJointTerm false D a b K P j r n H) ∧
    Function.HasFiniteSupport (secondSourceExpandedJointTerm true D a b K P j r n H) := by
  classical
  constructor
  · change Function.HasFiniteSupport (fun p : (ℕ × Exponent 3) × (ℕ × ℕ) =>
      if p.1 ∈ (Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support then
        secondSourceJointTerm false (secondSourceTerm D a b K P j p.1.1 p.1.2) r n H p.2
      else 0)
    exact finite_parameter_fibers
      ((Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support)
      (fun p : ℕ × Exponent 3 =>
        secondSourceJointTerm false (secondSourceTerm D a b K P j p.1 p.2) r n H)
      (fun p => (rational_joint_support
        (secondSourceTerm D a b K P j p.1 p.2) r n H).2.1)
  · change Function.HasFiniteSupport (fun p : (ℕ × Exponent 3) × (ℕ × ℕ) =>
      if p.1 ∈ (Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support then
        secondSourceJointTerm true (secondSourceTerm D a b K P j p.1.1 p.1.2) r n H p.2
      else 0)
    exact finite_parameter_fibers
      ((Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support)
      (fun p : ℕ × Exponent 3 =>
        secondSourceJointTerm true (secondSourceTerm D a b K P j p.1 p.2) r n H)
      (fun p => (rational_joint_support
        (secondSourceTerm D a b K P j p.1 p.2) r n H).2.2)

private theorem finite_rational_outer_readout {ι : Type*} (s : Finset ι)
    (T : ι → SecondSourceField) (gamma r n : ℤ) (H : ℕ) :
    supportedQReadout gamma r H n (secondSourceForward (∑ i ∈ s, T i))
        (secondSourceBackward (∑ i ∈ s, T i)) =
      ∑ i ∈ s, supportedQReadout gamma r H n
        (secondSourceForward (T i)) (secondSourceBackward (T i)) := by
  classical
  have forward (k l : ℤ) :
      secondSourceForward (∑ i ∈ s, T i) k l =
        ∑ i ∈ s, secondSourceForward (T i) k l := by
    simp only [secondSourceForward, map_sum, HahnSeries.coeff_sum]
  have backward (k l : ℤ) :
      secondSourceBackward (∑ i ∈ s, T i) k l =
        ∑ i ∈ s, secondSourceBackward (T i) k l := by
    simp only [secondSourceBackward, map_sum, HahnSeries.coeff_sum]
  unfold supportedQReadout
  calc
    _ = ∑ beta ∈ Finset.range ((H : ℤ) - r).toNat,
        ∑ i ∈ s, Ring.choose (-(gamma : ℂ) / 2) beta *
          ((∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + beta) u *
            secondSourceForward (T i) (r + beta - u) (n - beta + u)) -
           StateFieldResidueReconstruction.epsilon (r + beta) *
            ∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + beta) u *
              secondSourceBackward (T i) (r + n - u) u) := by
      apply Finset.sum_congr rfl
      intro beta hbeta
      have finite (i : ι) := (rational_joint_support (T i) r n H).1 beta hbeta
      simp_rw [forward, backward, Finset.mul_sum]
      rw [finsum_sum_comm s _ (fun i _ => (finite i).1),
        finsum_sum_comm s _ (fun i _ => (finite i).2)]
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := Finset.sum_comm

/-- A finite sum of supported complete outer readouts, retaining the actual
numerator monomials rather than interchanging unsupported mode sums. -/
def secondSourceTaylorOuterReadout (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (j : ℕ) (gamma r n : ℤ) (H : ℕ) : ℂ :=
  ∑ alpha ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
    ∑ e ∈ P.coeff.support,
      supportedQReadout gamma r H n
        (secondSourceForward (secondSourceTerm D a b K P j alpha e))
        (secondSourceBackward (secondSourceTerm D a b K P j alpha e))

private theorem second_source_outer_expansion (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) (gamma r n : ℤ) (H : ℕ) :
    supportedQReadout gamma r H n
        (secondSourceForward (secondSourceTaylorRational D a b K P j))
        (secondSourceBackward (secondSourceTaylorRational D a b K P j)) =
      secondSourceTaylorOuterReadout D a b K P j gamma r n H := by
  have field : secondSourceTaylorRational D a b K P j =
      ∑ alpha ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
        ∑ e ∈ P.coeff.support, secondSourceTerm D a b K P j alpha e := by
    unfold secondSourceTaylorRational secondSourceTerm
    simp_rw [Finset.mul_sum]
  rw [field, finite_rational_outer_readout]
  unfold secondSourceTaylorOuterReadout
  apply Finset.sum_congr rfl
  intro alpha ha
  exact finite_rational_outer_readout _ _ gamma r n H

/- The complete outer two-order collision is inherited at the rational-field
level. This local copy keeps the unrestricted Laurent numerator and its
origin-pole cancellation available to the second-source Taylor proof without
opening the frozen readout owner. -/
private theorem second_source_weighted_local_fiber (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃
      LabelledRationalClearing.GlobalRationalCurry.Remaining z)
    (x : LabelledRationalClearing.GlobalRationalCurry.Remaining z)
    (hx : tau (OrderedCollisionResidues.AdjacentLabelledCoordinates.boundarySlot pre post) = x)
    (P : LabelledPolynomial ℂ ((pre + 2) + post))
    (orders : Fin ((pre + 2) + post) × Fin ((pre + 2) + post) → ℕ)
    (r : ℤ) (g : Indices ((pre + 1) + post)) :
    let R := algebraMap _ (CommonRational ℂ ((pre + 2) + post)) P /
      algebraMap _ (CommonRational ℂ ((pre + 2) + post))
        (∏ p ∈ LabelledRationalClearing.PairDifferenceLocalization.labelledPairs
          ((pre + 2) + post),
          LabelledRationalClearing.PairDifferenceLocalization.pairPolynomial ℂ p.1 p.2 ^ orders p)
    (pullFiber (firstEmbedding pre post (-1))
      (contextPair ℂ pre post (kernelZX ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau R)).coeff g -
    (residue (pre + 1) post
      (contextPair ℂ pre post (kernelXZ ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau R)).coeff g =
    ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ (pre + 1) post z x tau
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R)).coeff (-1)).coeff g := by
  dsimp only
  have equality := RationalCollision.LaurentNumerator.weighted_laurent_collision
    ℂ pre post z tau x hx P orders r
  have first : ∀ R : CommonRational ℂ ((pre + 2) + post),
      OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R) =
      contextPair ℂ pre post (kernelZX ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau R := by
    intro R
    simp only [LabelledRationalClearing.WeightedActualQ.globalDiagonal, map_mul, map_zpow₀,
      OrderedCollisionResidues.LabelledDiagonalResidue.first_diagonal ℂ pre post z tau x hx,
      iotaZX_diagonal, kernelZX_zpow]
  have second : ∀ R : CommonRational ℂ ((pre + 2) + post),
      OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R) =
      contextPair ℂ pre post (kernelXZ ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau R := by
    intro R
    simp only [LabelledRationalClearing.WeightedActualQ.globalDiagonal, map_mul, map_zpow₀,
      OrderedCollisionResidues.LabelledDiagonalResidue.second_diagonal ℂ pre post z tau x hx,
      iotaXZ_diagonal, kernelXZ_zpow]
  dsimp only at equality
  rw [first, second] at equality
  exact congrArg (fun F : HahnSeries (Indices ((pre + 1) + post)) ℂ => F.coeff g) equality.symm

/- The preceding collision is now instantiated on the original labelled
numerator and its actual three pair orders. This is the complete signed outer
two-order identity; the remaining step is its coefficient identification with
the local Taylor terms above. -/
theorem actual_second_source_outer_collision
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (rho : ℤ) (g : Indices 2) :
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3)
        (weightedClearingPolynomial (threeOrders D a b K))
    let z : Fin 3 := 1
    let x : LabelledRationalClearing.GlobalRationalCurry.Remaining z := ⟨2, by decide⟩
    let tau : Fin 2 ≃ LabelledRationalClearing.GlobalRationalCurry.Remaining z :=
      finSuccAboveEquiv z
    (pullFiber (firstEmbedding 1 0 (-1))
      (contextPair ℂ 1 0 (kernelZX ℂ rho) *
        OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ 1 0 z tau R)).coeff g -
    (residue 2 0
      (contextPair ℂ 1 0 (kernelXZ ℂ rho) *
        OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ 1 0 z tau R)).coeff g =
    ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 2 0 z x tau
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ rho * R)).coeff (-1)).coeff g := by
  dsimp only
  exact second_source_weighted_local_fiber 1 0 1
    (finSuccAboveEquiv (1 : Fin 3)) ⟨2, by decide⟩ (by rfl) P
    (threeOrders D a b K) rho g

/- Complete-field padding reuses the finite-tail proof in LeftCurrentTransport. -/
section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
private theorem complete_q_pad (s r : ℤ) (A B : VertexOperator ℂ V) (K L : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator A B) = 0)
    (enlarges : K ≤ L) : qField s r K A B = qField s r L A B := by
  classical
  unfold qField
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro ell hL hK
  have high : (K : ℤ) ≤ r + ell := by
    simp only [Finset.mem_range, not_lt] at hK
    omega
  rw [ordinaryResidue_tail A B K locality (r + ell) high]
  suffices modeShift (ell : ℤ) (0 : VertexOperator ℂ V) = 0 by simp [this]
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    modeShift, VertexOperator.ncoeff_of_coeff]
  rfl

end

/- proof_shape: actual_current_second_source_rational_field: content
   admission_basis: escape-witness
   escape_witness: Signed Laurent currying at the original J/B diagonal
   computes a finite rational inner field. Both full coefficient maps,
   fractional shifts, supported outer fibers and actual complete-field
   padding are proved together, retaining the supplied P and arbitrary K. -/
/-- The actual complete current/second-source inner field is a single rational
G_j in v,z. Its two ordered mode maps and joint finite mode support agree
with the original nested-Q readout after complete-field padding.
This is the rational-field bridge; the final local outer Taylor contraction
and the full sameNumeratorCollisionBridge are not asserted. -/
theorem actual_current_second_source_rational_field
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H j : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ H)
      (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0) :
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let H' := max H (L + M + K)
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    let G := secondSourceTaylorRational D a b K P j
    (qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)) =
      qField gamma (d + r - j) H' (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1))) ∧
    (secondSourceRational M j R = G) ∧
    (∀ k l : ℤ,
      lastSourceLocalQ 0 true 1 j M l k R = secondSourceForward G k l ∧
      lastSourceLocalQ 0 false 1 j M k l R = secondSourceBackward G k l) ∧
    QReadoutSupported (d + r - j) H' n
      (secondSourceForward G) (secondSourceBackward G) ∧
    Function.HasFiniteSupport (secondSourceJointTerm false G (d + r - j) n H') ∧
    Function.HasFiniteSupport (secondSourceJointTerm true G (d + r - j) n H') ∧
    Function.HasFiniteSupport
      (secondSourceExpandedJointTerm false D a b K P j (d + r - j) n H') ∧
    Function.HasFiniteSupport
      (secondSourceExpandedJointTerm true D a b K P j (d + r - j) n H') ∧
    (phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      supportedQReadout gamma (d + r - j) H' n
        (secondSourceForward G) (secondSourceBackward G)) ∧
    (phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      secondSourceTaylorOuterReadout D a b K P j gamma (d + r - j) n H') ∧
    OuterQCompletion gamma (d + r - j) n H
      (secondSourceForward G) (secondSourceBackward G) := by
  dsimp only
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let H' := max H (L + M + K)
  let R := algebraMap _ (CommonRational ℂ 3) P /
    algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
  let G := secondSourceTaylorRational D a b K P j
  have pad := complete_q_pad gamma (d + r - j)
    (targetSlice D hu a gamma) (targetSlice D hu (neutralMode D i j b) (delta + 1))
    H H' locality (Nat.le_max_left _ _)
  have comparison := LatticeHalfFockSliceQuotient.actual_slice_quotient_compat
    D hu i a b K K gamma delta d r n x phi P P coefficients coefficients
  have original := (comparison.2.2 0 H j).2
  have enlarged := (comparison.2.2 0 H' j).2.1
  have padded_readout :
      phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      nestedRightLocalReadout 0 gamma 1 j (d + r - j) n M H' R := by
    rw [pad]
    exact enlarged
  have evaluate := second_source_rational_evaluation D a b K P j
  have callbacks (k l : ℤ) :
      lastSourceLocalQ 0 true 1 j M l k R = secondSourceForward G k l ∧
      lastSourceLocalQ 0 false 1 j M k l R = secondSourceBackward G k l := by
    constructor
    · have h := (second_source_coefficients M j R l k).1
      rw [evaluate] at h
      exact h
    · have h := (second_source_coefficients M j R k l).2
      rw [evaluate] at h
      exact h
  have forward : (fun k l => lastSourceLocalQ 0 true 1 j M l k R) =
      secondSourceForward G := by
    funext k l
    exact (callbacks k l).1
  have backward : (fun k l => lastSourceLocalQ 0 false 1 j M k l R) =
      secondSourceBackward G := by
    funext k l
    exact (callbacks k l).2
  have readout :
      nestedRightLocalReadout 0 gamma 1 j (d + r - j) n M H' R =
      supportedQReadout gamma (d + r - j) H' n
        (secondSourceForward G) (secondSourceBackward G) := by
    unfold nestedRightLocalReadout
    rw [forward, backward]
  have completion : OuterQCompletion gamma (d + r - j) n H
      (secondSourceForward G) (secondSourceBackward G) := by
    have h := original.2 locality
    change OuterQCompletion gamma (d + r - j) n H
      (fun k l => lastSourceLocalQ 0 true 1 j M l k R)
      (fun k l => lastSourceLocalQ 0 false 1 j M k l R) at h
    rw [forward, backward] at h
    exact h
  have support := rational_joint_support G (d + r - j) n H'
  have expandedSupport := second_source_expanded_support D a b K P j (d + r - j) n H'
  have expansion := second_source_outer_expansion D a b K P j gamma (d + r - j) n H'
  exact ⟨pad, evaluate, callbacks, support.1, support.2.1, support.2.2,
    expandedSupport.1, expandedSupport.2, padded_readout.trans readout,
    (padded_readout.trans readout).trans expansion, completion⟩

/- The final reverse outer contraction is independent of the lattice carrier.
It consumes the complete-field local evaluation for each original j and keeps
the signed diagonal and origin-pole weights unchanged. -/
theorem second_source_reverse_outer_contraction
    (P : LabelledPolynomial ℂ 3) (gamma d degree : ℤ) (L M : ℕ)
    (T : ℕ → ℂ)
    (hlocal : ∀ j ∈ Finset.range M,
      T j = StateFieldResidueReconstruction.epsilon (-(L : ℤ)) *
        ∑ u ∈ Finset.range (M - j),
          (if (u : ℤ) ≤ degree then
            collisionTaylor P gamma u (degree - u).toNat else 0) *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u))
    (hM : 0 < M) :
    StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range M,
          BinomialKernelDelta.chooseSign d j * T j) =
      StateFieldResidueReconstruction.epsilon (d - L) *
        ∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) ((u : ℤ) - M) := by
  have range_eq : (M - 1) + 1 = M := by omega
  have inner_eq (j : ℕ) (hj : j ∈ Finset.range M) :
      M - 1 - j + 1 = M - j := by
    have hj' := Finset.mem_range.mp hj
    omega
  have reverse := finite_reverse_outer_taylor P gamma d degree L (M - 1)
  have epsilon_product :
      StateFieldResidueReconstruction.epsilon d *
          StateFieldResidueReconstruction.epsilon (-(L : ℤ)) =
        StateFieldResidueReconstruction.epsilon (d - L) := by
    unfold StateFieldResidueReconstruction.epsilon
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
  have epsilon_mul (j : ℕ) (S : ℂ) :
      StateFieldResidueReconstruction.epsilon d *
          (BinomialKernelDelta.chooseSign d j *
            (StateFieldResidueReconstruction.epsilon (-(L : ℤ)) * S)) =
        StateFieldResidueReconstruction.epsilon (d - L) *
          (BinomialKernelDelta.chooseSign d j * S) := by
    calc
      _ = (StateFieldResidueReconstruction.epsilon d *
          StateFieldResidueReconstruction.epsilon (-(L : ℤ))) *
          (BinomialKernelDelta.chooseSign d j * S) := by ring
      _ = _ := by rw [epsilon_product]
  calc
    StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range M,
          BinomialKernelDelta.chooseSign d j * T j) =
      StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range ((M - 1) + 1),
          BinomialKernelDelta.chooseSign d j * T j) := by rw [range_eq]
    _ = ∑ j ∈ Finset.range ((M - 1) + 1),
        StateFieldResidueReconstruction.epsilon d *
          (BinomialKernelDelta.chooseSign d j * T j) := by
      rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range ((M - 1) + 1),
        StateFieldResidueReconstruction.epsilon (d - L) *
          (BinomialKernelDelta.chooseSign d j *
            ∑ u ∈ Finset.range (M - j),
              (if (u : ℤ) ≤ degree then
                collisionTaylor P gamma u (degree - u).toNat else 0) *
                BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ∈ Finset.range M := by simpa only [range_eq] using hj
      rw [hlocal j hjM]
      exact epsilon_mul j _
    _ = StateFieldResidueReconstruction.epsilon (d - L) *
        (∑ j ∈ Finset.range ((M - 1) + 1),
          BinomialKernelDelta.chooseSign d j *
            ∑ u ∈ Finset.range (M - j),
              (if (u : ℤ) ≤ degree then
                collisionTaylor P gamma u (degree - u).toNat else 0) *
                BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u)) := by
      rw [Finset.mul_sum]
    _ = StateFieldResidueReconstruction.epsilon (d - L) *
        (∑ j ∈ Finset.range ((M - 1) + 1),
          BinomialKernelDelta.chooseSign d j *
            ∑ u ∈ Finset.range ((M - 1) - j + 1),
              (if (u : ℤ) ≤ degree then
                collisionTaylor P gamma u (degree - u).toNat else 0) *
                BinomialKernelDelta.chooseSign (-(L : ℤ)) ((M - 1) - j - u)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ∈ Finset.range M := by simpa only [range_eq] using hj
      have hidx : M - j - 1 = M - 1 - j := by
        have hj' := Finset.mem_range.mp hjM
        omega
      rw [inner_eq j hjM, hidx]
    _ = StateFieldResidueReconstruction.epsilon (d - L) *
        ∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) ((u : ℤ) - M) := by
      rw [reverse]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      have hM' : 1 ≤ M := by omega
      have hcast : ((M - 1 : ℕ) : ℤ) + 1 = (M : ℤ) := by
        exact_mod_cast range_eq
      have harg : (u : ℤ) - ((M - 1 : ℕ) : ℤ) - 1 = (u : ℤ) - (M : ℤ) := by
        omega
      rw [harg]

/- The inner finite Taylor index has sharp support before any outer mode
calculation. This is the arithmetic equality used by the complete-field
expansion, including the empty cutoff branch. -/
theorem second_source_inner_sharp_support
    (j M alpha a k : ℕ)
    (ha : a < M - j - alpha)
    (hk : k = M - j - alpha - 1 - a) :
    alpha + a + k = M - j - 1 := by
  omega

/- The two independent Vandermonde contractions used after the sharp support
conditions are imposed. They are stated for arbitrary integer Laurent
exponents, so negative and zero numerator powers remain in scope. -/
theorem second_source_inner_vandermonde (q : ℤ) (u : ℕ) :
    (∑ alpha ∈ Finset.range (u + 1),
      Ring.choose (-(1 : ℂ) / 2) alpha *
        Ring.choose (q : ℂ) (u - alpha)) =
      Ring.choose (q - (1 : ℂ) / 2) u := by
  have h := Ring.add_choose_eq (R := ℂ)
    (r := -(1 : ℂ) / 2) (s := (q : ℂ)) u (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [show q - (1 : ℂ) / 2 = -(1 : ℂ) / 2 + q by ring] using h.symm

theorem second_source_outer_vandermonde (q gamma : ℤ) (u : ℕ) :
    (∑ beta ∈ Finset.range (u + 1),
      Ring.choose (-(gamma : ℂ) / 2) beta *
        Ring.choose (q : ℂ) (u - beta)) =
      Ring.choose ((q : ℂ) - (gamma : ℂ) / 2) u := by
  have h := Ring.add_choose_eq (R := ℂ)
    (r := -(gamma : ℂ) / 2) (s := (q : ℂ)) u (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [show (q : ℂ) - (gamma : ℂ) / 2 =
      -(gamma : ℂ) / 2 + q by ring] using h.symm
/- The two independent finite Vandermonde contractions expand the exact
collisionTaylor coefficient on the original signed exponent support. This
helper is consumed by the actual third-telescope composition below. -/
private theorem second_source_collision_taylor_sum
    (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) :
    collisionTaylor P gamma u v =
      P.coeff.sum (fun e c =>
        c *
          (∑ alpha ∈ Finset.range (u + 1),
            Ring.choose (-(1 : ℂ) / 2) alpha *
              Ring.choose (e 0 : ℂ) (u - alpha)) *
          (∑ beta ∈ Finset.range (v + 1),
            Ring.choose (-(gamma : ℂ) / 2) beta *
              Ring.choose (e 1 : ℂ) (v - beta))) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero =>
      simp [collisionTaylor, Finsupp.linearCombination_apply]
  | add P Q hP hQ =>
      simp only [collisionTaylor, AddMonoidAlgebra.coeff_add,
        Finsupp.linearCombination_apply, smul_eq_mul]
      conv_rhs =>
        rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
      conv_lhs =>
        rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
      have hP' := hP
      have hQ' := hQ
      simp only [collisionTaylor, Finsupp.linearCombination_apply,
        smul_eq_mul] at hP' hQ'
      rw [hP', hQ']
  | single e c =>
      simp only [collisionTaylor, AddMonoidAlgebra.coeff_single,
        Finsupp.linearCombination_single, smul_eq_mul]
      rw [Finsupp.sum_single_index (by simp)]
      rw [second_source_inner_vandermonde (e 0) u,
        second_source_outer_vandermonde (e 1) gamma v]
      ring_nf

private theorem second_source_third_conjunct_of_local_taylor
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H₃ : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range (vectorFrequencyBound D b + 1),
      (FieldNormalProductLocality.deltaEnd ^ H₃ j)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0)
    (local_taylor : ∀ j ∈ Finset.range (vectorFrequencyBound D b + 1),
      secondSourceTaylorOuterReadout D a b K P j gamma (d + r - j) n
        (max (H₃ j) (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K)) =
      StateFieldResidueReconstruction.epsilon
          (-(vectorFrequencyBound D a + 1 : ℤ)) *
        ∑ u ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
          (if (u : ℤ) ≤
              (vectorFrequencyBound D a + 1 : ℤ) +
                (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 then
            collisionTaylor P gamma u
              ((vectorFrequencyBound D a + 1 : ℤ) +
                (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 - u).toNat
           else 0) *
          BinomialKernelDelta.chooseSign (-(vectorFrequencyBound D a + 1 : ℤ))
            (vectorFrequencyBound D b + 1 - j - 1 - u)) :
    StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range (vectorFrequencyBound D b + 1),
          BinomialKernelDelta.chooseSign d j *
            phi (((qField gamma (d + r - j) (H₃ j)
              (targetSlice D hu a gamma)
              (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x)) =
      StateFieldResidueReconstruction.epsilon
          (d - (vectorFrequencyBound D a + 1 : ℤ)) *
        ∑ u ∈ Finset.range
            ((vectorFrequencyBound D a + 1 : ℤ) +
              (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 + 1).toNat,
          collisionTaylor P gamma u
              ((vectorFrequencyBound D a + 1 : ℤ) +
                (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 - u).toNat *
            orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℤ))
              ((u : ℤ) - (vectorFrequencyBound D b + 1 : ℤ)) := by
  let L : ℕ := vectorFrequencyBound D a + 1
  let M : ℕ := vectorFrequencyBound D b + 1
  let degree : ℤ := (L : ℤ) + M + K - d - r - 2
  let T : ℕ → ℂ := fun j =>
    phi (((qField gamma (d + r - j) (H₃ j)
      (targetSlice D hu a gamma)
      (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x)
  have hlocal (j : ℕ) (hj : j ∈ Finset.range M) :
      T j = StateFieldResidueReconstruction.epsilon (-(L : ℤ)) *
        ∑ u ∈ Finset.range (M - j),
          (if (u : ℤ) ≤ degree then
            collisionTaylor P gamma u (degree - u).toNat else 0) *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u) := by
    have hbridge := actual_current_second_source_rational_field D hu i a b K
      gamma delta d r n x phi P coefficients (H₃ j) j (locality j hj)
    rcases hbridge with ⟨_, _, _, _, _, _, _, _, _, hreadout, _⟩
    dsimp [T, L, M, degree]
    rw [hreadout]
    simpa only [second_source_collision_taylor_sum] using local_taylor j hj
  have hM : 0 < M := by dsimp [M]; omega
  have contracted := second_source_reverse_outer_contraction P gamma d degree L M T hlocal hM
  simpa only [T, L, M, degree, Nat.cast_add, Nat.cast_one] using contracted

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
