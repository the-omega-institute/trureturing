/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed local current/second-source residues and both supported Hahn orders. -/

import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockOuterTaylorEvaluation
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor.LocalResidues
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
import D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction

/-! The local-coordinate calculation adapts the signed Laurent proof in
LatticeHalfFockOuterTaylorEvaluation to the original J/B diagonal.
Its Hahn and binomial infrastructure is from mathlib (Apache 2.0).
The actual field suppliers retain their attribution in the inherited owners.
No locality assertion is made for a numerator monomial or ordered half. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
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

local macro "translate_variable" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockOuterTaylorEvaluation 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation.translate_variable))

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

theorem second_source_coefficients (M j : ℕ) (R : CommonRational ℂ 3)
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

theorem second_source_rational_evaluation (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) :
    secondSourceRational (vectorFrequencyBound D b + 1) j
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) =
      secondSourceTaylorRational D a b K P j := by
  unfold secondSourceRational secondSourceTaylorRational
  simp_rw [second_source_laurent_residue]

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

theorem rational_joint_support (T : SecondSourceField) (r n : ℤ) (H : ℕ) :
    (∀ ell ∈ Finset.range ((H : ℤ) - (r)).toNat,
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((r) + ell) u *
          secondSourceForward T ((r) + ell - u) ((n) - ell + u)) ∧
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((r) + ell) u *
          secondSourceBackward T ((r) + (n) - u) u)) ∧
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


abbrev vVar : SecondSourceField :=
  LabelledRationalClearing.PairDifferenceLocalization.remainingVariable ℂ (0 : Fin 3) ⟨1, by decide⟩
abbrev zVar : SecondSourceField :=
  LabelledRationalClearing.PairDifferenceLocalization.remainingVariable ℂ (0 : Fin 3) ⟨2, by decide⟩

def sourceMonomial (p q : ℤ) (c : ℂ) : SecondSourceField :=
  algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
    (AddMonoidAlgebra.single
      (fun i : Remaining (0 : Fin 3) => if i.val = 1 then p else q) c)

private theorem source_monomial_maps (p q : ℤ) (c : ℂ) :
    coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder (sourceMonomial p q c) =
      HahnSeries.single (exponents 2 ![p, q]) c ∧
    coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder (sourceMonomial p q c) =
      HahnSeries.single (exponents 2 ![q, p]) c := by
  constructor <;> rw [sourceMonomial, coefficient_monomial] <;> rfl

private theorem source_variable_maps :
    coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder vVar =
      HahnSeries.single (exponents 2 ![1, 0]) 1 ∧
    coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder zVar =
      HahnSeries.single (exponents 2 ![0, 1]) 1 ∧
    coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder vVar =
      HahnSeries.single (exponents 2 ![0, 1]) 1 ∧
    coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder zVar =
      HahnSeries.single (exponents 2 ![1, 0]) 1 := by
  dsimp only [vVar, zVar,
    LabelledRationalClearing.PairDifferenceLocalization.remainingVariable]
  constructor
  · rw [coefficient_monomial]; rfl
  constructor
  · rw [coefficient_monomial]; rfl
  constructor <;> rw [coefficient_monomial] <;> rfl

private theorem source_diagonal_maps (t : ℤ) :
    coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder ((vVar - zVar) ^ t) =
      contextPair ℂ 0 0 (kernelZX ℂ t) ∧
    coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder ((vVar - zVar) ^ t) =
      contextPair ℂ 0 0 (kernelXZ ℂ t) := by
  constructor
  · rw [map_zpow₀, map_sub, source_variable_maps.1, source_variable_maps.2.1,
      kernelZX_zpow, map_zpow₀]
    congr 1
    simp only [deltaZX, T, map_sub, HahnSeries.C_apply]
    change _ = contextPair ℂ 0 0 (HahnSeries.single 0 (HahnSeries.single 1 1)) -
      contextPair ℂ 0 0 (HahnSeries.single 1 (HahnSeries.single 0 1))
    rw [OrderedCollisionResidues.LabelledDiagonalResidue.context_single,
      OrderedCollisionResidues.LabelledDiagonalResidue.context_single]
    rfl
  · rw [map_zpow₀, map_sub, source_variable_maps.2.2.1, source_variable_maps.2.2.2,
      kernelXZ_zpow, map_zpow₀]
    congr 1
    simp only [deltaXZ, T, map_sub, HahnSeries.C_apply]
    change _ = contextPair ℂ 0 0 (HahnSeries.single 1 (HahnSeries.single 0 1)) -
      contextPair ℂ 0 0 (HahnSeries.single 0 (HahnSeries.single 1 1))
    rw [OrderedCollisionResidues.LabelledDiagonalResidue.context_single,
      OrderedCollisionResidues.LabelledDiagonalResidue.context_single]
    rfl

private theorem reverse_kernel_coefficient (t x y : ℤ) :
    (contextPair ℂ 0 0 (kernelXZ ℂ t)).coeff (pairIndex 0 0 (toLex (x, y))) =
      StateFieldResidueReconstruction.epsilon t *
        (if 0 ≤ x then if y = t - x then
          BinomialKernelDelta.chooseSign t x.toNat else 0 else 0) := by
  have constant : contextPair ℂ 0 0
      (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon t))) =
      HahnSeries.C (StateFieldResidueReconstruction.epsilon t) := by
    simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
  rw [reverse_kernel, map_mul, constant, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, binary_kernel_coeff]

private theorem source_binary_residue (T : SecondSourceField) (r n : ℤ) :
    completeOuterResidue r n (secondSourceForward T) (secondSourceBackward T) 0 =
      (contextPair ℂ 0 0 (kernelZX ℂ r) *
        coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder T).coeff
          (pairIndex 0 0 (toLex (-n - 1, -1))) -
      (contextPair ℂ 0 0 (kernelXZ ℂ r) *
        coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder T).coeff
          (pairIndex 0 0 (toLex (-1, -n - 1))) := by
  have left := (ContextualKernelExtraction.contextual_kernel_extraction ℂ 0 0 r
    (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder T)
    (pairIndex 0 0 (toLex (-n - 1, -1)))).2
  have right := (ContextualKernelExtraction.contextual_kernel_extraction ℂ 0 0 r
    (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder T)
    (pairIndex 0 0 (toLex (-1, -n - 1)))).2
  have li (u : ℕ) :
      pairIndex 0 0 (toLex (-n - 1, -1)) -
        pairIndex 0 0 (toLex ((u : ℤ), r - u)) =
      exponents 2 ![-(r - u) - 1, -(n + u) - 1] := by
    change toLex (-n - 1 - u, toLex (-1 - (r - u), ())) =
      toLex (-(n + u) - 1, toLex (-(r - u) - 1, ()))
    exact congrArg toLex (Prod.ext (by omega)
      (congrArg toLex (Prod.ext (by omega) rfl)))
  have ri (u : ℕ) :
      pairIndex 0 0 (toLex (-1, -n - 1)) -
        pairIndex 0 0 (toLex ((u : ℤ), r - u)) =
      exponents 2 ![-(r + n - u) - 1, -(u : ℤ) - 1] := by
    change toLex (-1 - (u : ℤ), toLex (-n - 1 - (r - u), ())) =
      toLex (-(u : ℤ) - 1, toLex (-(r + n - u) - 1, ()))
    exact congrArg toLex (Prod.ext (by omega)
      (congrArg toLex (Prod.ext (by omega) rfl)))
  have constant : contextPair ℂ 0 0
      (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon r))) =
      HahnSeries.C (StateFieldResidueReconstruction.epsilon r) := by
    simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
  rw [reverse_kernel, map_mul, constant, mul_assoc, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, left, right]
  simp only [li, ri, completeOuterResidue, secondSourceForward, secondSourceBackward,
    BinomialKernelDelta.chooseSign, Nat.cast_zero, add_zero, sub_zero]

private theorem source_kernel_product (p q t r : ℤ) (c : ℂ) :
    contextPair ℂ 0 0 (kernelZX ℂ r) *
      coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder
        (sourceMonomial p q c * (vVar - zVar) ^ t) =
      HahnSeries.single (exponents 2 ![p, q]) c *
        contextPair ℂ 0 0 (kernelZX ℂ (r + t)) ∧
    contextPair ℂ 0 0 (kernelXZ ℂ r) *
      coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder
        (sourceMonomial p q c * (vVar - zVar) ^ t) =
      HahnSeries.single (exponents 2 ![q, p]) c *
        contextPair ℂ 0 0 (kernelXZ ℂ (r + t)) := by
  constructor
  · rw [map_mul, (source_monomial_maps p q c).1, (source_diagonal_maps t).1,
      kernelZX_zpow, kernelZX_zpow, kernelZX_zpow,
      zpow_add₀ (deltaZX_ne_zero ℂ), map_mul]
    ring
  · rw [map_mul, (source_monomial_maps p q c).2, (source_diagonal_maps t).2,
      kernelXZ_zpow, kernelXZ_zpow, kernelXZ_zpow,
      zpow_add₀ (deltaXZ_ne_zero ℂ), map_mul]
    ring

private theorem source_negative_diagonal_residue
    (p q t r n : ℤ) (c : ℂ) (negative : r + t < 0) :
    completeOuterResidue r n
      (secondSourceForward (sourceMonomial p q c * (vVar - zVar) ^ t))
      (secondSourceBackward (sourceMonomial p q c * (vVar - zVar) ^ t)) 0 =
      if p + q = -(r + t) - n - 2 then
        c * ((Ring.choose p (-(r + t) - 1).toNat : ℤ) : ℂ) else 0 := by
  rw [source_binary_residue, (source_kernel_product p q t r c).1,
    (source_kernel_product p q t r c).2, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_single_mul]
  have li : pairIndex 0 0 (toLex (-n - 1, -1)) - exponents 2 ![p, q] =
      pairIndex 0 0 (toLex (-n - 1 - q, -1 - p)) := rfl
  have ri : pairIndex 0 0 (toLex (-1, -n - 1)) - exponents 2 ![q, p] =
      pairIndex 0 0 (toLex (-1 - p, -n - 1 - q)) := rfl
  rw [li, ri, binary_kernel_coeff, reverse_kernel_coefficient]
  by_cases homogeneous : p + q = -(r + t) - n - 2
  · rw [if_pos homogeneous,
      if_pos (show -1 - p = r + t - (-n - 1 - q) by omega),
      if_pos (show -n - 1 - q = r + t - (-1 - p) by omega)]
    let k := (-(r + t) - 1).toNat
    have kt : r + t = -(k : ℤ) - 1 := by dsimp [k]; omega
    have ix : -n - 1 - q = p - k := by dsimp [k]; omega
    rw [kt, ix, show -1 - p = -p - 1 by omega]
    rw [show (-(-(k : ℤ) - 1) - 1).toNat = k by omega]
    have signed := LatticeHalfFockClearedTaylorReadout.signed_kernel_choose k p
    linear_combination c * signed
  · rw [if_neg homogeneous,
      if_neg (show -1 - p ≠ r + t - (-n - 1 - q) by omega),
      if_neg (show -n - 1 - q ≠ r + t - (-1 - p) by omega)]
    simp



private theorem source_nonnegative_kernel_cancel (s : ℕ) (p : ℤ) :
    (if 0 ≤ (s : ℤ) + p + 1 then
      BinomialKernelDelta.chooseSign s ((s : ℤ) + p + 1).toNat else 0) -
    StateFieldResidueReconstruction.epsilon s *
      (if 0 ≤ -p - 1 then
        BinomialKernelDelta.chooseSign s (-p - 1).toNat else 0) = 0 := by
  by_cases hp : 0 ≤ -p - 1
  · by_cases hl : -p - 1 ≤ s
    · rw [if_pos hp, if_pos (by omega)]
      let a := (-p - 1).toNat
      have ha : a ≤ s := by dsimp [a]; omega
      have index : ((s : ℤ) + p + 1).toNat = s - a := by dsimp [a]; omega
      rw [index]
      simp only [BinomialKernelDelta.chooseSign, Ring.choose_natCast, Int.cast_natCast,
        StateFieldResidueReconstruction.epsilon, zpow_natCast]
      rw [Nat.choose_symm ha]
      have sign : (-1 : ℂ) ^ (s - a) = (-1 : ℂ) ^ s * (-1 : ℂ) ^ a := by
        rw [pow_sub₀ (-1 : ℂ) (by norm_num) ha, ← inv_pow, inv_neg_one]
      change (-1 : ℂ) ^ (s - a) * (s.choose a : ℂ) -
        (-1 : ℂ) ^ s * ((-1 : ℂ) ^ a * (s.choose a : ℂ)) = 0
      rw [sign]
      ring
    · rw [if_pos hp, if_neg (by omega)]
      simp only [BinomialKernelDelta.chooseSign, Ring.choose_natCast, Int.cast_natCast,
        Nat.choose_eq_zero_of_lt (show s < (-p - 1).toNat by omega),
        Nat.cast_zero, Int.cast_zero, mul_zero, sub_self]
  · rw [if_neg hp, if_pos (by omega)]
    simp only [BinomialKernelDelta.chooseSign, Ring.choose_natCast, Int.cast_natCast,
      Nat.choose_eq_zero_of_lt (show s < ((s : ℤ) + p + 1).toNat by omega),
      Nat.cast_zero, Int.cast_zero, mul_zero, sub_zero]

private theorem source_nonnegative_diagonal_residue
    (p q t r n : ℤ) (c : ℂ) (positive : 0 ≤ r + t) :
    completeOuterResidue r n
      (secondSourceForward (sourceMonomial p q c * (vVar - zVar) ^ t))
      (secondSourceBackward (sourceMonomial p q c * (vVar - zVar) ^ t)) 0 = 0 := by
  rw [source_binary_residue, (source_kernel_product p q t r c).1,
    (source_kernel_product p q t r c).2, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_single_mul]
  have li : pairIndex 0 0 (toLex (-n - 1, -1)) - exponents 2 ![p, q] =
      pairIndex 0 0 (toLex (-n - 1 - q, -1 - p)) := rfl
  have ri : pairIndex 0 0 (toLex (-1, -n - 1)) - exponents 2 ![q, p] =
      pairIndex 0 0 (toLex (-1 - p, -n - 1 - q)) := rfl
  rw [li, ri, binary_kernel_coeff, reverse_kernel_coefficient]
  by_cases homogeneous : p + q = -(r + t) - n - 2
  · rw [if_pos (show -1 - p = r + t - (-n - 1 - q) by omega),
      if_pos (show -n - 1 - q = r + t - (-1 - p) by omega)]
    have s : r + t = ((r + t).toNat : ℤ) := by omega
    have ix : -n - 1 - q = (r + t).toNat + p + 1 := by omega
    rw [s, ix, show -1 - p = -p - 1 by omega]
    have cancel := source_nonnegative_kernel_cancel (r + t).toNat p
    linear_combination c * cancel
  · rw [if_neg (show -1 - p ≠ r + t - (-n - 1 - q) by omega),
      if_neg (show -n - 1 - q ≠ r + t - (-1 - p) by omega)]
    simp

theorem source_monomial_complete_residue
    (p q t r n : ℤ) (c : ℂ) :
    completeOuterResidue r n
      (secondSourceForward (sourceMonomial p q c * (vVar - zVar) ^ t))
      (secondSourceBackward (sourceMonomial p q c * (vVar - zVar) ^ t)) 0 =
      if r + t < 0 then
        if p + q = -(r + t) - n - 2 then
          c * ((Ring.choose p (-(r + t) - 1).toNat : ℤ) : ℂ) else 0
      else 0 := by
  by_cases negative : r + t < 0
  · rw [if_pos negative, source_negative_diagonal_residue p q t r n c negative]
  · rw [if_neg negative, source_nonnegative_diagonal_residue p q t r n c (by omega)]

private theorem remaining_cases (i : Remaining (0 : Fin 3)) :
    i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ := by
  rcases i with ⟨i, hi⟩
  fin_cases i
  · exact (hi rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem source_monomial_mul (p q p' q' : ℤ) (c c' : ℂ) :
    sourceMonomial p q c * sourceMonomial p' q' c' =
      sourceMonomial (p + p') (q + q') (c * c') := by
  unfold sourceMonomial
  rw [← map_mul, AddMonoidAlgebra.single_mul_single]
  congr 2
  funext i
  simp only [Pi.add_apply]
  split_ifs <;> rfl

private theorem source_monomial_one : sourceMonomial 0 0 1 = 1 := by
  unfold sourceMonomial
  convert map_one (algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField) using 1
  congr 1
  simp only [ite_self]
  rfl

private theorem source_monomial_inv (p q : ℤ) :
    (sourceMonomial p q 1)⁻¹ = sourceMonomial (-p) (-q) 1 := by
  apply inv_eq_of_mul_eq_one_left
  rw [source_monomial_mul]
  simpa only [neg_add_cancel, one_mul] using source_monomial_one

private theorem source_monomial_pow (p q : ℤ) (n : ℕ) :
    sourceMonomial p q 1 ^ n = sourceMonomial ((n : ℤ) * p) ((n : ℤ) * q) 1 := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, source_monomial_one]
  | succ n ih =>
    rw [pow_succ, ih, source_monomial_mul]
    simp only [one_mul, Nat.cast_add, Nat.cast_one, add_mul]

private theorem source_monomial_zpow (p q n : ℤ) :
    sourceMonomial p q 1 ^ n = sourceMonomial (n * p) (n * q) 1 := by
  cases n with
  | ofNat n =>
    change sourceMonomial p q 1 ^ (n : ℤ) = _
    rw [zpow_natCast, source_monomial_pow, Int.ofNat_eq_natCast]
  | negSucc n =>
    change sourceMonomial p q 1 ^ (-((n + 1 : ℕ) : ℤ)) = _
    rw [zpow_neg, zpow_natCast, source_monomial_pow, source_monomial_inv]
    simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    congr 2 <;> ring

private theorem source_z_monomial : zVar = sourceMonomial 0 1 1 := by
  unfold zVar LabelledRationalClearing.PairDifferenceLocalization.remainingVariable sourceMonomial
  congr 2
  funext i
  rcases remaining_cases i with rfl | rfl <;> simp

private theorem source_c_monomial (c : ℂ) : algebraMap ℂ SecondSourceField c = sourceMonomial 0 0 c := by
  have h : algebraMap ℂ (CoefficientPolynomial ℂ (0 : Fin 3)) c =
      AddMonoidAlgebra.single (fun _ : Remaining (0 : Fin 3) => (0 : ℤ)) c := rfl
  rw [IsScalarTower.algebraMap_apply ℂ (CoefficientPolynomial ℂ (0 : Fin 3))
      SecondSourceField, h, sourceMonomial]
  congr 2
  funext i
  simp only [ite_self]

private theorem source_original_monomial (e : Exponent 3) (c : ℂ) :
    algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
      (AddMonoidAlgebra.single (fun i : Remaining (0 : Fin 3) => e i.val) c) =
      sourceMonomial (e 1) (e 2) c := by
  unfold sourceMonomial
  congr 2
  funext i
  rcases remaining_cases i with rfl | rfl <;> simp

private theorem source_shift_monomial (alpha : ℕ) :
    algebraMap (CoefficientPolynomial ℂ (0 : Fin 3)) SecondSourceField
      (AddMonoidAlgebra.single (Pi.single (⟨2, by decide⟩ : Remaining (0 : Fin 3))
        (-(alpha : ℤ))) (Ring.choose (-(1 : ℂ) / 2) alpha)) =
      sourceMonomial 0 (-(alpha : ℤ)) (Ring.choose (-(1 : ℂ) / 2) alpha) := by
  unfold sourceMonomial
  congr 2
  funext i
  rcases remaining_cases i with rfl | rfl <;> simp

private theorem source_diagonal_ne : vVar - zVar ≠ 0 := by
  apply sub_ne_zero.mpr
  intro eq
  have h := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable_injective
    ℂ (0 : Fin 3) eq
  have impossible := congrArg Subtype.val h
  exact (by decide : (1 : Fin 3) ≠ 2) impossible

/- A genuine inner Taylor summand in the original rational coefficient field.
The orientation factor is retained when z-v is replaced by v-z. -/
theorem source_inner_monomial_normal_form
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) :
    secondSourceInnerTaylorTerm D a b K P j alpha e =
      ∑ h ∈ Finset.range (vectorFrequencyBound D b + 1 - j - alpha),
        let k := vectorFrequencyBound D b + 1 - j - alpha - 1 - h
        sourceMonomial (e 1) (e 0 + e 2 - alpha - h)
          (Ring.choose (-(1 : ℂ) / 2) alpha * P.coeff e *
            ((Ring.choose (e 0) h : ℤ) : ℂ) *
            ((Ring.choose (-(vectorFrequencyBound D a + 1 : ℤ)) k : ℤ) : ℂ) *
            StateFieldResidueReconstruction.epsilon
              (-(vectorFrequencyBound D a + 1 : ℤ) - k)) *
          (vVar - zVar) ^
            (-(K : ℤ) - (vectorFrequencyBound D a + 1 : ℤ) - k) := by
  classical
  dsimp only [secondSourceInnerTaylorTerm]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  change _ * ((_ * (vVar - zVar) ^ (-(K : ℤ))) *
      (zVar ^ e 0 * (zVar - vVar) ^ (-(vectorFrequencyBound D a + 1 : ℤ))) *
      (zVar⁻¹ ^ h * _ * ((zVar - vVar)⁻¹ ^ _ * _))) = _
  let k := vectorFrequencyBound D b + 1 - j - alpha - 1 - h
  have orientation :
      (zVar - vVar) ^ (-(vectorFrequencyBound D a + 1 : ℤ)) *
        (zVar - vVar)⁻¹ ^ k =
      algebraMap ℂ SecondSourceField (StateFieldResidueReconstruction.epsilon
          (-(vectorFrequencyBound D a + 1 : ℤ) - k)) *
        (vVar - zVar) ^ (-(vectorFrequencyBound D a + 1 : ℤ) - k) := by
    rw [← zpow_neg_one, ← zpow_natCast, ← zpow_mul, neg_one_mul,
      ← zpow_add₀ (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp source_diagonal_ne)))]
    rw [show zVar - vVar = (-1 : SecondSourceField) * (vVar - zVar) by ring, mul_zpow]
    congr 1
    simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one,
      sub_eq_add_neg]
  have regroup : ∀ (A C Z F G : SecondSourceField),
      A * ((C * (vVar - zVar) ^ (-(K : ℤ))) *
        (Z * (zVar - vVar) ^ (-(vectorFrequencyBound D a + 1 : ℤ))) *
        (zVar⁻¹ ^ h * F * ((zVar - vVar)⁻¹ ^ k * G))) =
      A * C * Z * zVar⁻¹ ^ h * F * G *
        ((zVar - vVar) ^ (-(vectorFrequencyBound D a + 1 : ℤ)) *
          (zVar - vVar)⁻¹ ^ k) * (vVar - zVar) ^ (-(K : ℤ)) := by intros; ring
  rw [regroup, orientation]
  rw [show ∀ A B : SecondSourceField,
      A * (B * (vVar - zVar) ^ (-(vectorFrequencyBound D a + 1 : ℤ) - k)) *
        (vVar - zVar) ^ (-(K : ℤ)) =
      A * B * (vVar - zVar) ^
        (-(K : ℤ) - (vectorFrequencyBound D a + 1 : ℤ) - k) by
      intro A B
      calc
        _ = (A * B) * ((vVar - zVar) ^
              (-(vectorFrequencyBound D a + 1 : ℤ) - k) *
              (vVar - zVar) ^ (-(K : ℤ))) := by ring
        _ = _ := by
          rw [← zpow_add₀ source_diagonal_ne]
          congr 2 <;> omega]
  congr 1
  have zp (q : ℤ) : zVar ^ q = sourceMonomial 0 q 1 := by
    rw [source_z_monomial, source_monomial_zpow]
    simp only [mul_zero, mul_one]
  have zi : zVar⁻¹ ^ h = sourceMonomial 0 (-(h : ℤ)) 1 := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg, zp]
  rw [source_shift_monomial, source_original_monomial, zp, zi]
  simp only [← map_intCast (algebraMap ℂ SecondSourceField), source_c_monomial,
    source_monomial_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1 <;> first | omega | ring

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

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues
