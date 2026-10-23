/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complete binary Taylor evaluation at independent outer locality orders. -/

import D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge

/-! The binary Laurent numerator belongs to the original complete G.
The actual inner cutoff K and the independent complete-field locality
orders H(j) are preserved. Its graded fractional Taylor coefficients give
the full original same-P weighted middle equality. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockABLocalResidue LatticeHalfFockABActualReadout BinaryLaurentEvaluation
open LatticeHalfFockClearedTaylorReadout UniformGradedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open scoped BigOperators VertexOperator
noncomputable section

/- proof_shape: actual_ab_binary_taylor: content
   admission_basis: escape-witness
   escape_witness: Genuine complete-field locality pads the actual outer
   readout to max(H(j),B(j)); the generic signed Laurent evaluation then
   contracts the complete fractional sum. The original inner K is unchanged.
   consumer: forward_weighted_identity_of_negative_degree -/
set_option maxHeartbeats 1600000 in
-- Preserve the complete actual coefficient telescope during outer completion.
/-- The actual middle family is evaluated using a finite Laurent numerator
of its own complete binary G. Every independent H(j) is preserved through
complete-field support, without locality on a monomial or an ordered half. -/
theorem actual_ab_binary_taylor
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta))) = 0) :
    let B := fun j : ℕ => vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
      ((K : ℤ) - (r + j) - 1).toNat
    ∃ Q : ℕ → BinaryPolynomial, ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      binaryRational (Q j) (-(B j : ℤ)) =
        completeAB gamma (r + j) K (originalRational D a b K P) ∧
      phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
        (qField gamma (r + j) K (targetSlice D hu a gamma)
          (targetSlice D hu b delta)))[[n]]) x) =
        binaryTaylor (Q j) (B j) 1 (d - j) n := by
  classical
  dsimp only
  let B := fun j : ℕ => vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
    ((K : ℤ) - (r + j) - 1).toNat
  choose Q hQ using (fun j : ℕ => ab_complete_pole_bound D a b K K P gamma (r + j))
  refine ⟨Q, ?_⟩
  intro j hj
  have representation : binaryRational (Q j) (-(B j : ℤ)) =
      completeAB gamma (r + j) K (originalRational D a b K P) := by
    rw [hQ j]
    simp only [binaryRational, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rfl
  refine ⟨representation, ?_⟩
  let G := completeAB gamma (r + j) K (originalRational D a b K P)
  have forward :
      (fun k l => lastSourceLocalQ 1 true gamma (r + j) K l k
        (originalRational D a b K P)) = binaryModes false G := by
    funext k l
    exact (ab_complete_remaining_orders D a b K K P gamma (r + j) l k).2.2.1
  have backward :
      (fun k l => lastSourceLocalQ 1 false gamma (r + j) K k l
        (originalRational D a b K P)) = binaryModes true G := by
    funext k l
    exact (ab_complete_remaining_orders D a b K K P gamma (r + j) k l).2.2.2
  have completion := (actual_ab_joint_outer_support D hu i a b K gamma delta d r n
    x phi P coefficients H locality).1 j hj
  change OuterQCompletion 1 (d - j) n (H j)
    (fun k l => lastSourceLocalQ 1 true gamma (r + j) K l k
      (originalRational D a b K P))
    (fun k l => lastSourceLocalQ 1 false gamma (r + j) K k l
      (originalRational D a b K P)) at completion
  rw [forward, backward] at completion
  have actual := (actual_ab_nested_readout D hu i a b K K (H j)
    gamma delta d r n j x phi P coefficients).2.2
  change phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
      (qField gamma (r + j) K (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
    supportedQReadout 1 (d - j) (H j) n (binaryModes false G) (binaryModes true G) at actual
  have pad := (completion.2 (H j) le_rfl).trans
    (completion.2 (max (B j) (H j)) (Nat.le_max_right _ _)).symm
  rw [actual, pad]
  change binaryRational (Q j) (-(B j : ℤ)) = G at representation
  rw [← representation]
  exact binary_fractional_taylor (Q j) (B j) (max (B j) (H j)) 1 (d - j) n
    (Nat.le_max_left _ _)

/- proof_shape: forward_weighted_identity_of_negative_degree: content
   admission_basis: escape-witness
   escape_witness: On j<N the signed binary Taylor order B(j)-(d-j)-1
   equals the original degree L+M+K-d-r-2. Negative degree annihilates
   each complete actual nested coefficient and the original Taylor sum. -/
set_option maxHeartbeats 1600000 in
-- Preserve the complete actual coefficient telescope during the degree comparison.
/-- The original middle equality on every negative Taylor degree, retaining
its full actual homogeneous numerator and independent outer-locality family. -/
theorem forward_weighted_identity_of_negative_degree
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta))) = 0)
    (negative : (vectorFrequencyBound D a + 1 : ℕ) +
      (vectorFrequencyBound D b + 1 : ℕ) + (K : ℤ) - d - r - 2 < 0) :
    let degree : ℤ := (vectorFrequencyBound D a + 1 : ℕ) +
      (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2
    (∑ j ∈ Finset.range ((K : ℤ) - r).toNat,
      BinomialKernelDelta.chooseSign d j *
        phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta)))[[n]]) x)) =
      ∑ u ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma u (degree - u).toNat *
          orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
            (degree - u + r - K) := by
  classical
  dsimp only
  rw [show (((vectorFrequencyBound D a + 1 : ℕ) : ℤ) +
      (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2 + 1).toNat = 0 by omega]
  simp only [Finset.range_zero, Finset.sum_empty]
  obtain ⟨Q, evaluation⟩ := actual_ab_binary_taylor D hu i a b K gamma delta d r n
    x phi P coefficients H locality
  apply Finset.sum_eq_zero
  intro j hj
  rw [(evaluation j hj).2]
  have inside := Finset.mem_range.mp hj
  have low : 0 ≤ (K : ℤ) - (r + j) - 1 := by omega
  have high : ¬ d - (j : ℤ) <
      (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
        ((K : ℤ) - (r + j) - 1).toNat : ℕ) := by omega
  rw [binaryTaylor, ite_eq_right high, mul_zero]


private abbrev yLabel : LabelledRationalClearing.GlobalRationalCurry.Remaining (1 : Fin 3) :=
  ⟨0, by decide⟩
private abbrev zLabel : LabelledRationalClearing.GlobalRationalCurry.Remaining (1 : Fin 3) :=
  ⟨2, by decide⟩

private def diagonalPolynomial : BinaryPolynomial :=
  AddMonoidAlgebra.single (Pi.single yLabel 1) 1 -
    AddMonoidAlgebra.single (Pi.single zLabel 1) 1

private def gradedMoment (W : ℤ) (k : ℕ) : BinaryPolynomial →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ (fun e : BinaryExponent =>
    if e yLabel + e zLabel = W then
      Ring.choose ((e yLabel : ℂ) - 1 / 2) k else 0)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem gradedMoment_single (W : ℤ) (k : ℕ) (e : BinaryExponent) (c : ℂ) :
    gradedMoment W k (AddMonoidAlgebra.single e c) =
      if e yLabel + e zLabel = W then
        c * Ring.choose ((e yLabel : ℂ) - 1 / 2) k else 0 := by
  classical
  simp only [gradedMoment, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single, smul_eq_mul]
  split_ifs <;> simp

private theorem gradedMoment_diagonal (W : ℤ) (k : ℕ) (Q : BinaryPolynomial) :
    gradedMoment W k (diagonalPolynomial * Q) =
      match k with
      | 0 => 0
      | k + 1 => gradedMoment (W - 1) k Q := by
  classical
  induction Q using AddMonoidAlgebra.induction_linear with
  | zero => cases k <;> simp
  | add Q R hQ hR =>
    cases k <;> simp only [mul_add, map_add] at hQ hR ⊢ <;> rw [hQ, hR] <;> simp
  | single e c =>
    rw [diagonalPolynomial, sub_mul, AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.single_mul_single, map_sub,
      gradedMoment_single, gradedMoment_single]
    have hy : (Pi.single yLabel (1 : ℤ) + e : BinaryExponent) yLabel = 1 + e yLabel := by simp
    have hz : (Pi.single yLabel (1 : ℤ) + e : BinaryExponent) zLabel = e zLabel := by simp
    have zy : (Pi.single zLabel (1 : ℤ) + e : BinaryExponent) yLabel = e yLabel := by simp
    have zz : (Pi.single zLabel (1 : ℤ) + e : BinaryExponent) zLabel = 1 + e zLabel := by simp
    rw [hy, hz, zy, zz]
    have eq1 : 1 + e yLabel + e zLabel = W ↔ e yLabel + e zLabel = W - 1 := by omega
    have eq2 : e yLabel + (1 + e zLabel) = W ↔ e yLabel + e zLabel = W - 1 := by omega
    simp only [eq1, eq2]
    cases k with
    | zero => split_ifs <;> simp
    | succ k =>
      dsimp only
      rw [gradedMoment_single]
      split_ifs with h
      · rw [show (((1 + e yLabel : ℤ) : ℂ) - 1 / 2) =
            ((e yLabel : ℂ) - 1 / 2) + 1 by push_cast; ring,
          Ring.choose_succ_succ]
        ring
      · simp

private theorem gradedMoment_diagonal_pow (W : ℤ) (k v : ℕ)
    (e : BinaryExponent) (c : ℂ) :
    gradedMoment W k (diagonalPolynomial ^ v * AddMonoidAlgebra.single e c) =
      if e yLabel + e zLabel + v = W then
        if v ≤ k then c * Ring.choose ((e yLabel : ℂ) - 1 / 2) (k - v) else 0
      else 0 := by
  induction v generalizing W k with
  | zero => simp [gradedMoment_single]
  | succ v ih =>
    rw [pow_succ', mul_assoc, gradedMoment_diagonal]
    cases k with
    | zero => simp
    | succ k =>
      dsimp only
      rw [ih]
      have eqn : e yLabel + e zLabel + (v : ℤ) = W - 1 ↔
          e yLabel + e zLabel + (v + 1 : ℕ) = W := by push_cast; omega
      simp only [eqn, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

private def shiftedMonomial (e : Exponent 3) (c : ℂ) (v : ℕ) : BinaryPolynomial :=
  AddMonoidAlgebra.single
    ((fun j : LabelledRationalClearing.GlobalRationalCurry.Remaining (1 : Fin 3) => e j.val) +
      Pi.single zLabel (e 1 - v)) c

private def residueNumerator (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (L t : ℕ) :
    BinaryPolynomial :=
  ∑ ell ∈ Finset.range (t + 1), ∑ e ∈ P.coeff.support,
    ∑ u ∈ Finset.range (t - ell + 1),
      (Ring.choose (-(gamma : ℂ) / 2) ell * Ring.choose (e 1 : ℂ) u *
        BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - ell - u)) •
          (diagonalPolynomial ^ (ell + u) * shiftedMonomial e (P.coeff e) (ell + u))

private theorem z_ne_zero : LatticeHalfFockABLocalResidue.z ≠ 0 := by
  change algebraMap (LabelledRationalClearing.GlobalRationalCurry.CoefficientPolynomial ℂ
    (1 : Fin 3)) ABField (AddMonoidAlgebra.single (Pi.single zLabel (1 : ℤ)) (1 : ℂ)) ≠ 0
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (by simp)

theorem yz_ne_zero : y - LatticeHalfFockABLocalResidue.z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have labels := LabelledRationalClearing.PairDifferenceLocalization.remainingVariable_injective
    ℂ (1 : Fin 3) h
  have impossible := congrArg Subtype.val labels
  exact (by decide : (0 : Fin 3) ≠ 2) impossible

private theorem map_z_monomial (p : ℤ) :
    algebraMap BinaryPolynomial ABField
      (AddMonoidAlgebra.single (Pi.single zLabel p) 1) =
        LatticeHalfFockABLocalResidue.z ^ p := by
  let m : Multiplicative BinaryExponent →* ABField :=
    (algebraMap BinaryPolynomial ABField).toMonoidHom.comp
      (AddMonoidAlgebra.of ℂ BinaryExponent)
  have h := m.map_zpow (Multiplicative.ofAdd (Pi.single zLabel (1 : ℤ))) p
  change algebraMap BinaryPolynomial ABField
    (AddMonoidAlgebra.single (p • (Pi.single zLabel (1 : ℤ) : BinaryExponent)) 1) =
      LatticeHalfFockABLocalResidue.z ^ p at h
  have index : p • (Pi.single zLabel (1 : ℤ) : BinaryExponent) = Pi.single zLabel p := by
    ext j
    by_cases hj : j = zLabel <;> simp [Pi.single_apply, hj]
  simpa only [index] using h

private theorem map_shiftedMonomial (e : Exponent 3) (c : ℂ) (v : ℕ) :
    algebraMap BinaryPolynomial ABField (shiftedMonomial e c v) =
      monomialConstant e c * LatticeHalfFockABLocalResidue.z ^ (e 1 - v) := by
  rw [← map_z_monomial]
  unfold shiftedMonomial monomialConstant
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]

private theorem map_diagonal :
    algebraMap BinaryPolynomial ABField diagonalPolynomial =
      y - LatticeHalfFockABLocalResidue.z := by
  simp only [diagonalPolynomial, map_sub]
  rfl

private theorem map_zShift (ell : ℕ) :
    zShift ell = LatticeHalfFockABLocalResidue.z ^ (-(ell : ℤ)) :=
  map_z_monomial _

private theorem gradedMoment_shifted (W : ℤ) (k v : ℕ) (e : Exponent 3) (c : ℂ) :
    gradedMoment W k (diagonalPolynomial ^ v * shiftedMonomial e c v) =
      if totalExponent e = W then
        if v ≤ k then c * Ring.choose ((e 0 : ℂ) - 1 / 2) (k - v) else 0
      else 0 := by
  rw [shiftedMonomial, gradedMoment_diagonal_pow]
  have hy : ((fun j : LabelledRationalClearing.GlobalRationalCurry.Remaining (1 : Fin 3) =>
      e j.val) + Pi.single zLabel (e 1 - v) : BinaryExponent) yLabel = e 0 := by simp
  have hz : ((fun j : LabelledRationalClearing.GlobalRationalCurry.Remaining (1 : Fin 3) =>
      e j.val) + Pi.single zLabel (e 1 - v) : BinaryExponent) zLabel = e 2 + (e 1 - v) := by simp
  rw [hy, hz]
  have total : e 0 + (e 2 + (e 1 - v)) + v = totalExponent e := by
    simp only [totalExponent, Fin.sum_univ_three]
    omega
  rw [total]

theorem triangle_vandermonde (a b : ℂ) (t : ℕ) (F : ℕ → ℂ) :
    (∑ ell ∈ Finset.range (t + 1), ∑ u ∈ Finset.range (t - ell + 1),
      Ring.choose a ell * Ring.choose b u * F (ell + u)) =
    ∑ v ∈ Finset.range (t + 1), Ring.choose (a + b) v * F v := by
  have flip := Finset.sum_range_diag_flip (t + 1)
    (fun ell u => Ring.choose a ell * Ring.choose b u * F (ell + u))
  have reindex :
      (∑ ell ∈ Finset.range (t + 1), ∑ u ∈ Finset.range (t - ell + 1),
        Ring.choose a ell * Ring.choose b u * F (ell + u)) =
      ∑ v ∈ Finset.range (t + 1), ∑ ell ∈ Finset.range (v + 1),
        Ring.choose a ell * Ring.choose b (v - ell) * F v := by
    symm
    convert flip using 1
    · apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro ell hell
      have le : ell ≤ v := by simpa using Finset.mem_range.mp hell
      rw [Nat.add_sub_of_le le]
    · apply Finset.sum_congr rfl
      intro ell hell
      have le : ell ≤ t := by simpa using Finset.mem_range.mp hell
      rw [show t + 1 - ell = t - ell + 1 by omega]
  rw [reindex]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_mul]
  have h := Ring.add_choose_eq (R := ℂ) (r := a) (s := b) v (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [h]

private theorem binaryTaylor_gradedMoment (Q : BinaryPolynomial) (B : ℕ) (r n : ℤ)
    (low : r < B) :
    binaryTaylor Q B 1 r n = gradedMoment ((B : ℤ) - r - n - 2)
      ((B : ℤ) - r - 1).toNat Q := by
  classical
  simp only [binaryTaylor, if_pos low, gradedMoment, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, Int.cast_one]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp

private theorem gradedMoment_residueNumerator (P : LabelledPolynomial ℂ 3)
    (gamma W : ℤ) (L t k : ℕ)
    (homogeneous : ∀ e ∈ P.coeff.support, totalExponent e = W) :
    gradedMoment W k (residueNumerator P gamma L t) =
      ∑ v ∈ Finset.range (t + 1),
        (if v ≤ k then collisionTaylor P gamma (k - v) v else 0) *
          BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - v) := by
  classical
  unfold residueNumerator
  simp only [map_sum, map_smul, smul_eq_mul, gradedMoment_shifted]
  rw [Finset.sum_comm]
  have perMonomial (e : Exponent 3) (he : e ∈ P.coeff.support) :
      (∑ ell ∈ Finset.range (t + 1), ∑ u ∈ Finset.range (t - ell + 1),
        (Ring.choose (-(gamma : ℂ) / 2) ell * Ring.choose (e 1 : ℂ) u *
          BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - ell - u)) *
          (if totalExponent e = W then
            if ell + u ≤ k then P.coeff e *
              Ring.choose ((e 0 : ℂ) - 1 / 2) (k - (ell + u)) else 0 else 0)) =
      ∑ v ∈ Finset.range (t + 1),
        (if v ≤ k then P.coeff e * Ring.choose ((e 0 : ℂ) - 1 / 2) (k - v) else 0) *
          Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2) v *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - v) := by
    simp only [if_pos (homogeneous e he)]
    have h := triangle_vandermonde (-(gamma : ℂ) / 2) (e 1 : ℂ) t
      (fun v => (if v ≤ k then P.coeff e *
        Ring.choose ((e 0 : ℂ) - 1 / 2) (k - v) else 0) *
          BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - v))
    rw [show -(gamma : ℂ) / 2 + (e 1 : ℂ) =
      (e 1 : ℂ) - (gamma : ℂ) / 2 by ring] at h
    calc
      _ = ∑ ell ∈ Finset.range (t + 1), ∑ u ∈ Finset.range (t - ell + 1),
          Ring.choose (-(gamma : ℂ) / 2) ell * Ring.choose (e 1 : ℂ) u *
            ((if ell + u ≤ k then P.coeff e *
              Ring.choose ((e 0 : ℂ) - 1 / 2) (k - (ell + u)) else 0) *
                BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - (ell + u))) := by
        apply Finset.sum_congr rfl
        intro ell hell
        apply Finset.sum_congr rfl
        intro u hu
        rw [Nat.sub_sub]
        ring
      _ = _ := h
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
  rw [Finset.sum_congr rfl perMonomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases inside : v ≤ k
  · simp only [if_pos inside, collisionTaylor, Finsupp.linearCombination_apply,
      Finsupp.sum, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    ring
  · simp [inside]

theorem map_complex_smul (c : ℂ) (Q : BinaryPolynomial) :
    algebraMap BinaryPolynomial ABField (c • Q) =
      algebraMap ℂ ABField c * algebraMap BinaryPolynomial ABField Q := by
  rw [Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply ℂ BinaryPolynomial ABField]

set_option maxHeartbeats 1600000 in
-- Keep the original signed exponents while normalizing the cleared local residue.
private theorem cleared_ab_monomial (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (w : ℤ) (t ell : ℕ) (ht : (K : ℤ) - w - 1 = t) (hell : ell ≤ t)
    (e : Exponent 3) (c : ℂ) :
    (y - LatticeHalfFockABLocalResidue.z) ^
        (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t) *
      zShift ell * abMonomialValue D a b K e c (w + ell) =
    algebraMap BinaryPolynomial ABField
      (∑ u ∈ Finset.range (t - ell + 1),
        (Ring.choose (e 1 : ℂ) u *
          BinomialKernelDelta.chooseSign (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ))
            (t - ell - u)) •
          (diagonalPolynomial ^ (ell + u) * shiftedMonomial e c (ell + u))) := by
  classical
  let L : ℤ := vectorFrequencyBound D a + 1
  let M : ℤ := vectorFrequencyBound D b + 1
  let A : ABField := y - LatticeHalfFockABLocalResidue.z
  let Z : ABField := LatticeHalfFockABLocalResidue.z
  have low : w + (ell : ℤ) - K < 0 := by omega
  have index : (-(w + (ell : ℤ) - K) - 1).toNat = t - ell := by omega
  rw [abMonomialValue, if_pos low, index, map_zShift, map_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u ≤ t - ell := by simpa using Finset.mem_range.mp hu
  let m := t - ell - u
  have exponent : ((vectorFrequencyBound D a + 1 +
      (vectorFrequencyBound D b + 1) + t : ℕ) : ℤ) - M - L - m = ell + u := by
    dsimp [L, M, m]
    omega
  have orient (p : ℤ) : (Z - y) ^ p = (-1 : ABField) ^ p * A ^ p := by
    rw [← mul_zpow]
    congr 1
    dsimp [A, Z]
    ring
  have sign : (-1 : ABField) ^ (-L) * (Z - y) ^ (-L) = A ^ (-L) := by
    rw [← mul_zpow]
    congr 1
    dsimp [A, Z]
    ring
  have normalize :
      A ^ (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t) *
        Z ^ (-(ell : ℤ)) *
        ((monomialConstant e c * A ^ (-M) * (-1 : ABField) ^ (-L)) *
          (Z ^ e 1 * (Z - y) ^ (-L)) *
          (Z⁻¹ ^ u * ((Ring.choose (e 1) u : ℤ) : ABField) *
            ((Z - y)⁻¹ ^ m * ((Ring.choose (-L) m : ℤ) : ABField)))) =
      ((Ring.choose (e 1) u : ℤ) : ABField) *
        ((Ring.choose (-L) m : ℤ) : ABField) * (-1 : ABField) ^ m *
        (A ^ (ell + u) * (monomialConstant e c * Z ^ (e 1 - (ell + u)))) := by
    have orient' : (Z - y)⁻¹ ^ m =
        (-1 : ABField) ^ (-(m : ℤ)) * A ^ (-(m : ℤ)) := by
      simpa only [zpow_neg, zpow_natCast, inv_pow] using orient (-(m : ℤ))
    rw [orient']
    have signs : (-1 : ABField) ^ (-(m : ℤ)) = (-1 : ABField) ^ m := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
    rw [signs]
    calc
      _ = ((Ring.choose (e 1) u : ℤ) : ABField) *
          ((Ring.choose (-L) m : ℤ) : ABField) * (-1 : ABField) ^ m *
          (monomialConstant e c * (Z ^ e 1 * Z ^ (-(ell : ℤ)) * Z ^ (-(u : ℤ)))) *
            (A ^ (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t) *
              A ^ (-M) * ((-1 : ABField) ^ (-L) * (Z - y) ^ (-L)) * A ^ (-(m : ℤ))) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
        ring
      _ = _ := by
        rw [sign]
        have za : Z ^ e 1 * Z ^ (-(ell : ℤ)) * Z ^ (-(u : ℤ)) =
            Z ^ (e 1 - (ell + u)) := by
          rw [← zpow_add₀ z_ne_zero, ← zpow_add₀ z_ne_zero]
          congr 1
          push_cast
          omega
        have aa : A ^ (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t) *
            A ^ (-M) * A ^ (-L) * A ^ (-(m : ℤ)) = A ^ (ell + u) := by
          rw [← zpow_natCast A, ← zpow_add₀ yz_ne_zero, ← zpow_add₀ yz_ne_zero,
            ← zpow_add₀ yz_ne_zero]
          rw [show ((vectorFrequencyBound D a + 1 +
            (vectorFrequencyBound D b + 1) + t : ℕ) : ℤ) + -M + -L + -(m : ℤ) =
              ((ell + u : ℕ) : ℤ) by omega, zpow_natCast]
        rw [za, aa]
        ring
  change A ^ _ * Z ^ (-(ell : ℤ)) *
    ((monomialConstant e c * A ^ (-M) * (-1 : ABField) ^ (-L)) *
      (Z ^ e 1 * (Z - y) ^ (-L)) *
      (Z⁻¹ ^ u * ((Ring.choose (e 1) u : ℤ) : ABField) *
        ((Z - y)⁻¹ ^ m * ((Ring.choose (-L) m : ℤ) : ABField)))) = _
  rw [normalize, map_complex_smul]
  simp only [map_mul, map_pow, map_diagonal, map_shiftedMonomial]
  have castChoose : algebraMap ℂ ABField (Ring.choose (e 1 : ℂ) u) =
      ((Ring.choose (e 1) u : ℤ) : ABField) := by
    have h : ((Ring.choose (e 1) u : ℤ) : ℂ) = Ring.choose (e 1 : ℂ) u :=
      Ring.map_choose (Int.castRingHom ℂ) (e 1) u
    rw [← h, map_intCast]
  have lcast : -((vectorFrequencyBound D a + 1 : ℕ) : ℤ) = -L := by simp [L]
  rw [castChoose, lcast]
  simp only [BinomialKernelDelta.chooseSign, map_mul, map_pow, map_neg, map_one,
    map_intCast, Nat.cast_add]
  dsimp only [A, Z, m]
  ring

set_option maxHeartbeats 1600000 in
-- Clear the complete finite residue before comparing Laurent numerators.
private theorem residueNumerator_representation (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (gamma w : ℤ) (t : ℕ)
    (ht : (K : ℤ) - w - 1 = t) :
    binaryRational (residueNumerator P gamma (vectorFrequencyBound D a + 1) t)
      (-((vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t : ℕ) : ℤ)) =
      completeAB gamma w K (originalRational D a b K P) := by
  classical
  let B := vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t
  have count : ((K : ℤ) - w).toNat = t + 1 := by omega
  have cleared :
      (y - LatticeHalfFockABLocalResidue.z) ^ B *
        completeAB gamma w K (originalRational D a b K P) =
      algebraMap BinaryPolynomial ABField
        (residueNumerator P gamma (vectorFrequencyBound D a + 1) t) := by
    unfold completeAB
    rw [count, Finset.mul_sum]
    calc
      _ = ∑ ell ∈ Finset.range (t + 1),
          algebraMap ℂ ABField (Ring.choose (-(gamma : ℂ) / 2) ell) *
            ∑ e ∈ P.coeff.support,
              (y - LatticeHalfFockABLocalResidue.z) ^ B * zShift ell *
                abMonomialValue D a b K e (P.coeff e) (w + ell) := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [(ab_complete_remaining_orders D a b K K P gamma (w + ell) 0 0).1]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ ell ∈ Finset.range (t + 1),
          algebraMap ℂ ABField (Ring.choose (-(gamma : ℂ) / 2) ell) *
            ∑ e ∈ P.coeff.support,
              algebraMap BinaryPolynomial ABField
                (∑ u ∈ Finset.range (t - ell + 1),
                  (Ring.choose (e 1 : ℂ) u *
                    BinomialKernelDelta.chooseSign
                      (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ)) (t - ell - u)) •
                    (diagonalPolynomial ^ (ell + u) *
                      shiftedMonomial e (P.coeff e) (ell + u))) := by
        apply Finset.sum_congr rfl
        intro ell hell
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        exact cleared_ab_monomial D a b K w t ell ht
          (by simpa using Finset.mem_range.mp hell) e (P.coeff e)
      _ = _ := by
        simp only [residueNumerator, map_sum, map_complex_smul, map_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell hell
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro u hu
        ring
  change algebraMap BinaryPolynomial ABField
    (residueNumerator P gamma (vectorFrequencyBound D a + 1) t) *
      (y - LatticeHalfFockABLocalResidue.z) ^ (-(B : ℤ)) = _
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  apply (div_eq_iff (pow_ne_zero B yz_ne_zero)).mpr
  rw [← cleared, mul_comm]

private theorem same_numerator_taylor (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (gamma w outer n : ℤ) (t k : ℕ)
    (ht : (K : ℤ) - w - 1 = t)
    (order : ((vectorFrequencyBound D a + 1 +
      (vectorFrequencyBound D b + 1) + t : ℕ) : ℤ) - outer - 1 = k)
    (homogeneous : ∀ e ∈ P.coeff.support, totalExponent e = (k : ℤ) - n - 1)
    (Q : BinaryPolynomial)
    (representation : binaryRational Q
      (-((vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t : ℕ) : ℤ)) =
      completeAB gamma w K (originalRational D a b K P)) :
    binaryTaylor Q (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + t)
      1 outer n =
    ∑ v ∈ Finset.range (t + 1),
      (if v ≤ k then collisionTaylor P gamma (k - v) v else 0) *
        BinomialKernelDelta.chooseSign (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ)) (t - v) := by
  have eqn := representation.trans
    (residueNumerator_representation D a b K P gamma w t ht).symm
  have same : Q = residueNumerator P gamma (vectorFrequencyBound D a + 1) t := by
    apply IsFractionRing.injective BinaryPolynomial ABField
    dsimp only [binaryRational] at eqn
    exact (mul_left_inj' (zpow_ne_zero _ yz_ne_zero)).mp eqn
  rw [same, binaryTaylor_gradedMoment _ _ _ _ (by omega)]
  rw [show ((vectorFrequencyBound D a + 1 +
    (vectorFrequencyBound D b + 1) + t : ℕ) : ℤ) - outer - n - 2 = (k : ℤ) - n - 1 by omega,
    order, Int.toNat_natCast]
  exact gradedMoment_residueNumerator P gamma _ _ t k homogeneous

/- proof_shape: forward_weighted_identity: content
   admission_basis: escape-witness
   escape_witness: The complete A/B residue determines the actual binary
   numerator by injectivity. Clearing its pole gives signed Laurent monomials
   times powers of the original diagonal. Their graded fractional Taylor
   moments shift exactly; Vandermonde contracts the inner fractional sum.
   The resulting same-P convolution feeds finite_forward_outer_taylor. -/
set_option maxHeartbeats 1600000 in
-- Preserve the complete actual coefficient telescope through the same-numerator calculation.
/-- The full original weighted middle equality, at every supplied cutoff and
signed Taylor degree, with independent genuine whole-field locality orders. -/
theorem forward_weighted_identity
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta))) = 0) :
    let degree : ℤ := (vectorFrequencyBound D a + 1 : ℕ) +
      (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2
    (∑ j ∈ Finset.range ((K : ℤ) - r).toNat,
      BinomialKernelDelta.chooseSign d j *
        phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta)))[[n]]) x)) =
      ∑ u ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma u (degree - u).toNat *
          orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
            (degree - u + r - K) := by
  classical
  dsimp only
  by_cases empty : (K : ℤ) ≤ r
  · exact LatticeHalfFockNestedQForwardEdge.forward_weighted_identity_of_cutoff_le_lift
      D hu i a b K gamma delta d r n x phi P H empty
  let degree : ℤ := (vectorFrequencyBound D a + 1 : ℕ) +
    (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2
  by_cases negative : degree < 0
  · exact forward_weighted_identity_of_negative_degree D hu i a b K gamma delta d r n
      x phi P coefficients H locality negative
  have nonnegative : 0 ≤ degree := by omega
  let t := ((K : ℤ) - r - 1).toNat
  have tcast : (t : ℤ) = K - r - 1 := by dsimp [t]; omega
  have count : ((K : ℤ) - r).toNat = t + 1 := by omega
  have orders : (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) =
      (vectorFrequencyBound D a + 1 : ℕ) + (vectorFrequencyBound D b + 1 : ℕ) + (K : ℤ) := by
    have pairs : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
    simp [pairs, threeOrders, add_assoc]
  have homogeneous : ∀ e ∈ P.coeff.support, totalExponent e = degree - n - 1 := by
    intro e he
    have nz := Finsupp.mem_support_iff.mp he
    have eqn := coefficients e
    split_ifs at eqn with total
    · rw [orders] at total
      dsimp [degree]
      omega
    · exact (nz eqn).elim
  obtain ⟨Q, evaluation⟩ := actual_ab_binary_taylor D hu i a b K gamma delta d r n
    x phi P coefficients H locality
  have sameP (j : ℕ) (hj : j ∈ Finset.range (t + 1)) :
      binaryTaylor (Q j)
        (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
          ((K : ℤ) - (r + j) - 1).toNat) 1 (d - j) n =
      ∑ v ∈ Finset.range (t - j + 1),
        (if (v : ℤ) ≤ degree then collisionTaylor P gamma (degree - v).toNat v else 0) *
          BinomialKernelDelta.chooseSign
            (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ)) (t - j - v) := by
    have jle : j ≤ t := by simpa using Finset.mem_range.mp hj
    have jrange : j ∈ Finset.range ((K : ℤ) - r).toNat := by rwa [count]
    have localIndex : ((K : ℤ) - (r + j) - 1).toNat = t - j := by omega
    have representation := (evaluation j jrange).1
    dsimp only at representation
    rw [localIndex] at representation ⊢
    have law := same_numerator_taylor D a b K P gamma (r + j) (d - j) n
      (t - j) degree.toNat (by omega) (by dsimp [degree]; omega)
      (by simpa only [Int.toNat_of_nonneg nonnegative] using homogeneous)
      (Q j) representation
    rw [law]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [show (v : ℤ) ≤ degree ↔ v ≤ degree.toNat by omega,
      show (degree - (v : ℤ)).toNat = degree.toNat - v by omega]
  change (∑ j ∈ Finset.range ((K : ℤ) - r).toNat, _) =
    ∑ u ∈ Finset.range (degree + 1).toNat, _
  rw [count]
  calc
    _ = ∑ j ∈ Finset.range (t + 1), BinomialKernelDelta.chooseSign d j *
        ∑ v ∈ Finset.range (t - j + 1),
          (if (v : ℤ) ≤ degree then collisionTaylor P gamma (degree - v).toNat v else 0) *
            BinomialKernelDelta.chooseSign
              (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ)) (t - j - v) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(evaluation j (by rwa [count])).2, sameP j hj]
    _ = ∑ u ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma u (degree - u).toNat *
          orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
            (degree - u - t - 1) :=
      LatticeHalfFockOuterTaylorEvaluation.finite_forward_outer_taylor
        P gamma d degree (vectorFrequencyBound D a + 1) t
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [show degree - (u : ℤ) - t - 1 = degree - u + r - K by omega]

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
