/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockOuterTaylorEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockOuterTaylorEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed J/A Laurent residues and the fused finite Taylor contraction. -/

import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionTaylor

/-! Signed Laurent powers include empty cases. Classical formal local-field calculus:
Matsuo--Nagatomo; Bakalov--Kac, math/0402315. Hahn/Laurent/binomial infrastructure:
mathlib, Apache 2.0 (Aaron Anderson, María Inés de Frutos-Fernández,
Filippo A. E. Nuccio). Actual field composition: Scott Carnahan, vertexAlg
4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open CollisionLaurentKernels.LaurentCollision
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open scoped BigOperators VertexOperator RatFunc
noncomputable section

/-! Finite local-coordinate evaluation. The binomial series below have
nonnegative local support even when their original Laurent exponents are
negative. No global numerator coordinate is restricted. -/

private theorem translated_laurent_power {E : Type*} [Field E]
    (a : E) (ha : a ≠ 0) (p : ℤ) :
    (HahnSeries.single (1 : ℤ) (1 : E) + HahnSeries.C a : LaurentSeries E) ^ p =
      HahnSeries.C (a ^ p) * binomial E a⁻¹ p := by
  rw [binomial_zpow, map_zpow₀, ← mul_zpow]
  congr 1
  simp [mul_add, HahnSeries.C_apply, HahnSeries.single_mul_single,
    mul_inv_cancel₀ ha, add_comm]

/-- The actual coefficient of two translated signed Laurent factors at a
local pole. Only the local Taylor indices are natural. -/
theorem local_laurent_pair_residue {E : Type*} [Field E]
    (a b c : E) (ha : a ≠ 0) (hb : b ≠ 0) (p q k : ℤ) :
    ((HahnSeries.single k c : LaurentSeries E) *
      ((HahnSeries.single 1 1 + HahnSeries.C a) ^ p *
       (HahnSeries.single 1 1 + HahnSeries.C b) ^ q)).coeff (-1) =
      if k < 0 then
        c * (a ^ p * b ^ q) *
          ∑ u ∈ Finset.range ((-k - 1).toNat + 1),
            a⁻¹ ^ u * ((Ring.choose p u : ℤ) : E) *
              (b⁻¹ ^ ((-k - 1).toNat - u) *
                ((Ring.choose q ((-k - 1).toNat - u) : ℤ) : E))
      else 0 := by
  rw [translated_laurent_power a ha p, translated_laurent_power b hb q]
  have regroup :
      HahnSeries.C (a ^ p) * binomial E a⁻¹ p *
          (HahnSeries.C (b ^ q) * binomial E b⁻¹ q) =
        HahnSeries.C (a ^ p * b ^ q) *
          (binomial E a⁻¹ p * binomial E b⁻¹ q) := by
    rw [map_mul]
    ring
  rw [regroup, ← mul_assoc, HahnSeries.C_apply,
    HahnSeries.single_mul_single, add_zero, HahnSeries.coeff_single_mul]
  unfold binomial
  rw [← map_mul]
  by_cases negative : k < 0
  · rw [if_pos negative]
    have index : (-1 : ℤ) - k = ((-k - 1).toNat : ℤ) := by omega
    rw [index, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
      zsmul_eq_mul, mul_one]
  · rw [if_neg negative]
    simp only [PowerSeries.coeff_coe, show (-1 : ℤ) - k < 0 by omega,
      if_pos, mul_zero]

private theorem translate_variable {E : Type*} [Field E] (a : E) :
    IsFractionRing.ringEquivOfRingEquiv
      (Polynomial.algEquivAevalXAddC a).toRingEquiv (RatFunc.X : RatFunc E) =
        RatFunc.X + RatFunc.C a := by
  rw [← RatFunc.algebraMap_X, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [Polynomial.algEquivAevalXAddC_apply]

/-- Currying a monomial at the current/first-source diagonal gives two
translated Laurent factors and the original independent spectator pole. -/
theorem current_source_local_monomial (D : LatticeData) (a b : Carrier D)
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
      ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e c) /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))) =
      RatFunc.C (C * (v - z) ^ (-(K : ℤ))) *
        (RatFunc.X + RatFunc.C v) ^ e 0 *
        RatFunc.X ^ (w - (vectorFrequencyBound D a + 1 : ℕ)) *
        (RatFunc.X + RatFunc.C (v - z)) ^ (-((vectorFrequencyBound D b + 1 : ℕ) : ℤ)) := by
  classical
  dsimp only
  have pairs : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  have clear : weightedClearingPolynomial (threeOrders D a b K) =
      pairPolynomial (0 : Fin 3) 1 ^ (vectorFrequencyBound D a + 1) *
      pairPolynomial (0 : Fin 3) 2 ^ (vectorFrequencyBound D b + 1) *
      pairPolynomial (1 : Fin 3) 2 ^ K := by
    simp [weightedClearingPolynomial, pairs, threeOrders]
    ring
  rw [clear]
  simp only [OrderedCollisionCoordinates.LocalResidueCurrying.localRational,
    RingHom.comp_apply, map_mul, map_div₀, map_pow, map_zpow₀,
    LabelledRationalClearing.WeightedActualQ.globalDiagonal,
    LabelledRationalClearing.GlobalRationalCurry.curryRational,
    IsFractionRing.lift_algebraMap]
  rw [LabelledRationalClearing.PairDifferenceLocalization.curryPolynomial_single]
  have mapcurrent := LabelledRationalClearing.PairDifferenceLocalization.curry_variable_z ℂ (0 : Fin 3)
  have map0label := mapcurrent
  have mapv := LabelledRationalClearing.PairDifferenceLocalization.curry_variable_remaining
    ℂ (0 : Fin 3) ⟨1, by decide⟩
  have mapz := LabelledRationalClearing.PairDifferenceLocalization.curry_variable_remaining
    ℂ (0 : Fin 3) ⟨2, by decide⟩
  have mapvlabel := mapv
  have mapzlabel := mapz
  change LabelledRationalClearing.GlobalRationalCurry.curryPolynomial ℂ (0 : Fin 3)
    (variablePolynomial (0 : Fin 3)) = _ at mapcurrent
  change LabelledRationalClearing.GlobalRationalCurry.curryPolynomial ℂ (0 : Fin 3)
    (variablePolynomial (1 : Fin 3)) = _ at mapv
  change LabelledRationalClearing.GlobalRationalCurry.curryPolynomial ℂ (0 : Fin 3)
    (variablePolynomial (2 : Fin 3)) = _ at mapz
  simp only [pairPolynomial,
    LabelledRationalClearing.PairDifferenceLocalization.pairPolynomial,
    map_sub, mapcurrent, mapv, mapz, map0label, mapvlabel, mapzlabel]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_mul, map_pow, map_zpow₀, map_sub,
    OrderedCollisionResidues.LocalResidueLinear.translate_constant]
  simp only [OrderedCollisionCoordinates.LocalResidueCurrying.translate, translate_variable,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  simp only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]
  rw [zpow_add₀ RatFunc.X_ne_zero]
  simp only [zpow_neg, zpow_natCast, map_mul, map_inv₀, map_pow,
    div_eq_mul_inv, mul_inv_rev, sub_eq_add_neg, add_assoc]
  ring

/-- Finite coefficient-field value of a signed monomial at the J/A diagonal. -/
def currentSourceMonomialValue (D : LatticeData) (a b : Carrier D)
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
      if w - (L : ℤ) < 0 then
        (C * (v - z) ^ (-(K : ℤ))) * (v ^ e 0 * (v - z) ^ (-(M : ℤ))) *
          ∑ u ∈ Finset.range ((-(w - (L : ℤ)) - 1).toNat + 1),
            v⁻¹ ^ u * ((Ring.choose (e 0) u : ℤ) : E) *
              ((v - z)⁻¹ ^ ((-(w - (L : ℤ)) - 1).toNat - u) *
                ((Ring.choose (-(M : ℤ)) ((-(w - (L : ℤ)) - 1).toNat - u) : ℤ) : E))
      else 0

/-- The genuine current/first-source local residue of a signed Laurent
monomial, before any spectator ordering. The remaining pole keeps its own K. -/
theorem current_source_monomial_residue (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (e : Exponent 3) (c : ℂ) (w : ℤ) :
    OrderedCollisionCoordinates.LocalResidueCurrying.localResidue ℂ (0 : Fin 3)
      ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e c) /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))) =
      currentSourceMonomialValue D a b K e c w := by
  classical
  dsimp only [currentSourceMonomialValue]
  unfold OrderedCollisionCoordinates.LocalResidueCurrying.localResidue
  rw [current_source_local_monomial]
  let E := LabelledRationalClearing.GlobalRationalCurry.CoefficientField ℂ (0 : Fin 3)
  let v : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
    ℂ (0 : Fin 3) ⟨1, by decide⟩
  let z : E := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable
    ℂ (0 : Fin 3) ⟨2, by decide⟩
  have hv : v ≠ 0 := by
    change (algebraMap
      (LabelledRationalClearing.GlobalRationalCurry.CoefficientPolynomial ℂ (0 : Fin 3)) E)
      (AddMonoidAlgebra.single (Pi.single ⟨1, by decide⟩ (1 : ℤ)) (1 : ℂ)) ≠ 0
    have h : (AddMonoidAlgebra.single
        (Pi.single (⟨1, by decide⟩ :
          LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3)) (1 : ℤ) :
          LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) → ℤ)
        (1 : ℂ)) ≠ 0 := by simp
    simpa only [map_zero] using
      (IsFractionRing.injective
        (LabelledRationalClearing.GlobalRationalCurry.CoefficientPolynomial ℂ (0 : Fin 3)) E).ne h
  have hvz : v - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro equality
    have labels := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable_injective
      ℂ (0 : Fin 3) equality
    have impossible := congrArg Subtype.val labels
    exact (by decide : (1 : Fin 3) ≠ 2) impossible
  have mapC (h : E) : algebraMap (RatFunc E) (LaurentSeries E) (RatFunc.C h) =
      HahnSeries.C h := by
    rw [← RatFunc.algebraMap_C,
      ← IsScalarTower.algebraMap_apply (Polynomial E) (RatFunc E) (LaurentSeries E)]
    simp [Polynomial.algebraMap_hahnSeries_apply, PowerSeries.coe_C]
  dsimp only [E] at mapC
  simp only [map_mul, map_zpow₀, map_add, RatFunc.coe_X]
  simp_rw [mapC]
  rw [← map_zpow₀ (HahnSeries.C : E →+* LaurentSeries E),
    ← map_mul (HahnSeries.C : E →+* LaurentSeries E)]
  rw [show ∀ (h : E) (p k q : ℤ),
      HahnSeries.C h * (HahnSeries.single 1 1 + HahnSeries.C v) ^ p *
          (HahnSeries.single 1 1 : LaurentSeries E) ^ k *
          (HahnSeries.single 1 1 + HahnSeries.C (v - z)) ^ q =
        HahnSeries.single k h * ((HahnSeries.single 1 1 + HahnSeries.C v) ^ p *
          (HahnSeries.single 1 1 + HahnSeries.C (v - z)) ^ q) by
    intro h p k q
    rw [← RatFunc.single_zpow, HahnSeries.C_apply]
    calc
      _ = (HahnSeries.single 0 h * HahnSeries.single k (1 : E)) *
          ((HahnSeries.single 1 1 + HahnSeries.C v) ^ p *
            (HahnSeries.single 1 1 + HahnSeries.C (v - z)) ^ q) := by ring
      _ = _ := by rw [HahnSeries.single_mul_single, zero_add, mul_one]
  ]
  exact local_laurent_pair_residue v (v - z) _ hv hvz _ _ _

/-- Evaluate the original finite Laurent numerator at the actual J/A
local pole by its full finite monomial sum. Negative exponents are retained. -/
theorem current_source_laurent_residue (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (w : ℤ) :
    OrderedCollisionCoordinates.LocalResidueCurrying.localResidue ℂ (0 : Fin 3)
      ⟨1, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
        ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) P /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))) =
      ∑ e ∈ P.coeff.support, currentSourceMonomialValue D a b K e (P.coeff e) w := by
  classical
  let residue := OrderedCollisionResidues.CollisionResidueMaps.localResidueHom
    ℂ 0 1 (0 : Fin 3) ⟨1, by decide⟩
  have splitP : (∑ e ∈ P.coeff.support,
      AddMonoidAlgebra.single e (P.coeff e)) = P := by
    exact AddMonoidAlgebra.sum_coeff_single P
  have splitR :
      LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
          ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) P /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) =
      ∑ e ∈ P.coeff.support,
        LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
          ⟨1, by decide⟩ ^ w *
        (algebraMap _ (CommonRational ℂ 3) (AddMonoidAlgebra.single e (P.coeff e)) /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) := by
    rw [← Finset.mul_sum, ← Finset.sum_div, ← map_sum, splitP]
  change residue _ = _
  rw [splitR, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact current_source_monomial_residue D a b K e (P.coeff e) w

theorem finite_rectangle_cut (A B : ℕ) (f : ℕ → ℂ) :
    (∑ u ∈ Finset.range (A + 1), if u ≤ B then f u else 0) =
      ∑ u ∈ Finset.range (B + 1), if u ≤ A then f u else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Finite Vandermonde contraction in the associated Taylor coordinates.
The two bounds N and t are independent. -/
theorem finite_associated_contraction (M : ℤ) (N t : ℕ) (F : ℕ → ℂ) :
    (∑ u ∈ Finset.range (N + 1),
      ∑ j ∈ Finset.range (N - u + 1),
        if u ≤ t then ((u + j).choose u : ℂ) * F (u + j) *
          ((Ring.choose M (t - u) : ℤ) : ℂ) else 0) =
      ∑ w ∈ Finset.range (N + 1), F w *
        ((Ring.choose ((w : ℤ) + M) t : ℤ) : ℂ) := by
  classical
  have triangle :
      (∑ u ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N - u + 1),
          if u ≤ t then ((u + j).choose u : ℂ) * F (u + j) *
            ((Ring.choose M (t - u) : ℤ) : ℂ) else 0) =
      ∑ w ∈ Finset.range (N + 1),
        ∑ u ∈ Finset.range (w + 1), if u ≤ t then
          (w.choose u : ℂ) * F w * ((Ring.choose M (t - u) : ℤ) : ℂ) else 0 := by
    have flip := Finset.sum_range_diag_flip (N + 1) (fun u j =>
      if u ≤ t then ((u + j).choose u : ℂ) * F (u + j) *
        ((Ring.choose M (t - u) : ℤ) : ℂ) else 0)
    symm
    convert flip using 1
    · apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro u hu
      have bound : u ≤ w := by simpa using Finset.mem_range.mp hu
      rw [Nat.add_sub_of_le bound]
    · apply Finset.sum_congr rfl
      intro u hu
      have bound : u ≤ N := by simpa using Finset.mem_range.mp hu
      rw [show N + 1 - u = N - u + 1 by omega]
  rw [triangle]
  apply Finset.sum_congr rfl
  intro w hw
  calc
    _ = ∑ u ∈ Finset.range (t + 1), if u ≤ w then
        (w.choose u : ℂ) * F w * ((Ring.choose M (t - u) : ℤ) : ℂ) else 0 :=
      finite_rectangle_cut w t _
    _ = F w * ∑ u ∈ Finset.range (t + 1),
        Ring.choose (w : ℂ) u * Ring.choose (M : ℂ) (t - u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have castChoose : ((Ring.choose M (t - u) : ℤ) : ℂ) =
          Ring.choose (M : ℂ) (t - u) := Ring.map_choose (Int.castRingHom ℂ) M (t - u)
      rw [Ring.choose_natCast, ← castChoose]
      by_cases bound : u ≤ w
      · rw [if_pos bound]
        ring
      · rw [if_neg bound, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        ring
    _ = _ := by
      have vandermonde := Ring.add_choose_eq (R := ℂ)
        (r := (w : ℂ)) (s := (M : ℂ)) t (Commute.all _ _)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
      rw [← vandermonde]
      have castChoose : ((Ring.choose ((w : ℤ) + M) t : ℤ) : ℂ) =
          Ring.choose (((w : ℤ) + M : ℤ) : ℂ) t :=
        Ring.map_choose (Int.castRingHom ℂ) ((w : ℤ) + M) t
      rw [castChoose]
      push_cast
      rfl

set_option maxHeartbeats 1000000 in
/-- The associated-coordinate finite convolution equals the original fused
Taylor sum. No sign or nonnegativity condition is imposed on total degree. -/
theorem finite_left_outer_taylor (P : LabelledPolynomial ℂ 3)
    (gamma degree : ℤ) (M t : ℕ) :
    (∑ u ∈ Finset.range (t + 1),
      (if (u : ℤ) ≤ degree then associatedTaylor P gamma u (degree - u).toNat else 0) *
        ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ)) =
      ∑ w ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma w (degree - w).toNat *
          fusedResidueWeight ((w : ℤ) - M) (-(t : ℤ) - 1) := by
  classical
  by_cases negative : degree < 0
  · have empty : (degree + 1).toNat = 0 := by omega
    simp only [empty, Finset.range_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro u member
    rw [if_neg (by omega), zero_mul]
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ degree by omega)
    have cutoff : ((N : ℤ) + 1).toNat = N + 1 := by omega
    rw [cutoff]
    have first :
        (∑ u ∈ Finset.range (t + 1),
          (if (u : ℤ) ≤ (N : ℤ) then associatedTaylor P gamma u ((N : ℤ) - u).toNat else 0) *
            ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ)) =
        ∑ u ∈ Finset.range (N + 1), if u ≤ t then
          associatedTaylor P gamma u (N - u) *
            ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ) else 0 := by
      calc
        _ = ∑ u ∈ Finset.range (t + 1), if u ≤ N then
            associatedTaylor P gamma u (N - u) *
              ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          split_ifs with h h'
          · congr 2
            omega
          · omega
          · omega
          · simp
        _ = _ := finite_rectangle_cut t N _
    rw [first]
    calc
      _ = ∑ u ∈ Finset.range (N + 1),
          ∑ j ∈ Finset.range (N - u + 1), if u ≤ t then
            ((u + j).choose u : ℂ) * collisionTaylor P gamma (u + j) (N - (u + j)) *
              ((Ring.choose (-(M : ℤ)) (t - u) : ℤ) : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [associatedTaylor_cocycle]
        by_cases bound : u ≤ t
        · rw [if_pos bound, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_pos bound, Nat.sub_sub]
        · simp [bound]
      _ = ∑ w ∈ Finset.range (N + 1), collisionTaylor P gamma w (N - w) *
          ((Ring.choose ((w : ℤ) + -(M : ℤ)) t : ℤ) : ℂ) :=
        finite_associated_contraction (-(M : ℤ)) N t
          (fun w => collisionTaylor P gamma w (N - w))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w hw
        have index : ((N : ℤ) - w).toNat = N - w := by omega
        rw [index]
        unfold fusedResidueWeight
        rw [if_pos (show -(t : ℤ) - 1 < 0 by omega),
          show (-(-(t : ℤ) - 1) - 1).toNat = t by omega]
        rw [sub_eq_add_neg]

end
end D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation
