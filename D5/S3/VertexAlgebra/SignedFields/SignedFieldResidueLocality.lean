/- GID: D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality
   mirror-E: none(waiver:algebraic-signed-field-calculus)
   anchors: []
   utility: none
   digest: All-integer signed Dong locality and translation of vectorwise finite residues. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The finite-support constructor and telescope adapt StateFieldResidueReconstruction
and its attributed ScottCarnahan/vertexAlg source. Signed calculations adapt
BcGhostStateFieldIterate to arbitrary fields. The existing PairSpace cancellation
and FieldDeltaBinomial.delta_binomial are reused. No novelty claim is made.
proof_shape: residue_locality, residue_translation: content
admission_basis: escape-witness
escape_witness: Nonnegative residues are boundaries of shifted signed triple
pairs; negative residues are signed normal products of divided derivatives.
Vectorwise support bounds and a binomial telescope establish covariance.
-/

import D5.S3.VertexAlgebra.SignedFields.SignedFieldNormalProductLocality
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
import D5.S3.VertexAlgebra.BinomialKernelDelta

/-! Vectorwise residues, all-integer signed locality and covariance. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators VertexOperator
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open private signedTriple signedTriple_coefficients signedPair_low signedPair_high from
  D5.S3.VertexAlgebra.SignedFields.SignedFieldNormalProductLocality
open private shiftsCommute discrepancyXY residueXY residueYZ intertwiningPowers
  cancellationBound from D5.S3.VertexAlgebra.FieldNormalProductLocality

noncomputable section
namespace D5.S3.VertexAlgebra.SignedFieldResidueLocality
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

def residueLeft (r n : ℤ) (A B : VertexOperator ℂ V) (vector : V) : V :=
  ∑ᶠ offset : ℕ, (((-1 : ℂ) ^ offset) * integerBinomial r offset) • (A [[r - offset]]) ((B [[n + offset]])
    vector)

def residueRight (r n : ℤ) (A B : VertexOperator ℂ V) (vector : V) : V :=
  ∑ᶠ offset : ℕ, (((-1 : ℂ) ^ offset) * integerBinomial r offset) • (B [[r + n - offset]]) ((A [[offset]])
    vector)

def residueCoefficient (s : ℂ) (r n : ℤ) (A B : VertexOperator ℂ V) (vector : V) : V :=
  residueLeft r n A B vector - (epsilon r * s) • residueRight r n A B vector

structure ResidueField (s : ℂ) (r : ℤ) (A B : VertexOperator ℂ V) where
  operator : VertexOperator ℂ V
  coefficient : ∀ n vector, (operator [[n]]) vector = residueCoefficient s r n A B vector
  left_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • (A [[r - offset]]) ((B [[n + offset]]) vector))
  right_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • (B [[r + n - offset]]) ((A [[offset]]) vector))

def residueField (s : ℂ) (r : ℤ) (A B : VertexOperator ℂ V) : ResidueField s r A B := by
  classical
  have leftKernel (m n : ℤ) (A B : VertexOperator ℂ V) (vector : V) : (Function.support fun offset : ℕ => (Int.negOnePow offset) • Ring.choose n offset • (A [[n - offset]])
    ((B [[-m - 1 + offset]]) vector)).Finite := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm (B vector)).order + m).toNat, ?_⟩; intro offset member
    contrapose! member
    suffices (B [[-m - 1 + offset]]) vector = 0 by simp [this]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
  have rightKernel (m n : ℤ) (A B : VertexOperator ℂ V) (vector : V) : (Function.support fun offset : ℕ => (Int.negOnePow offset) • Ring.choose n offset • (B [[n + (-m - 1) -
    offset]]) ((A [[offset]]) vector)).Finite := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm (A vector)).order - 1).toNat, ?_⟩; intro offset member
    contrapose! member
    suffices (A [[offset]]) vector = 0 by simp [this]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
  have leftFinite (n : ℤ) (vector : V) : Function.HasFiniteSupport (fun offset : ℕ =>
      (((-1 : ℂ) ^ offset) * integerBinomial r offset) • (A [[r - offset]]) ((B [[n + offset]]) vector)) := by
    have finite := leftKernel (-n - 1) r A B vector
    simpa only [Function.HasFiniteSupport, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_smul, integerBinomial, show -(-n - 1) - 1 = n by omega]
      using finite
  have rightFinite (n : ℤ) (vector : V) : Function.HasFiniteSupport (fun offset : ℕ =>
      (((-1 : ℂ) ^ offset) * integerBinomial r offset) • (B [[r + n - offset]]) ((A [[offset]]) vector)) := by
    have finite := rightKernel (-n - 1) r A B vector
    simpa only [Function.HasFiniteSupport, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_smul, integerBinomial, show -(-n - 1) - 1 = n by omega]
      using finite
  let coefficient (n : ℤ) : Module.End ℂ V := {
    toFun := residueCoefficient s r n A B
    map_add' first second := by
      dsimp [residueCoefficient, residueLeft, residueRight]; simp only [map_add, smul_add]
      rw [finsum_add_distrib (leftFinite n first) (leftFinite n second), finsum_add_distrib (rightFinite n first) (rightFinite n second)]
      module
    map_smul' scalar vector := by
      dsimp [residueCoefficient, residueLeft, residueRight]; simp only [map_smul, RingHom.id_apply]; simp_rw [smul_comm _ scalar]
      rw [← smul_finsum' scalar (leftFinite n vector), ← smul_finsum' scalar (rightFinite n vector)]
      rw [smul_comm (epsilon r * s) scalar, ← smul_sub] }
  have bounded (vector : V) : BddBelow (Function.support (fun power : ℤ => coefficient (-power - 1) vector)) := by
    let cutoff : ℕ := (-((HahnModule.of ℂ).symm (A vector)).order - 1).toNat
    let orders : Finset ℤ := (Finset.range (cutoff + 1)).image (fun offset : ℕ =>
      ((HahnModule.of ℂ).symm (B ((A [[offset]]) vector))).order + r - offset)
    let lower : ℤ := min ((HahnModule.of ℂ).symm (B vector)).order (orders.min' (by
        apply Finset.image_nonempty.mpr; exact ⟨0, Finset.mem_range.mpr (by omega)⟩))
    refine ⟨lower, ?_⟩; intro power member; by_contra notLower
    have small : power < lower := lt_of_not_ge notLower
    have firstZero (offset : ℕ) : (A [[r - offset]]) ((B [[-power - 1 + offset]]) vector) = 0 := by
      have vanish : (B [[-power - 1 + offset]]) vector = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; dsimp [lower] at small; omega
      simp [vanish]
    have secondZero (offset : ℕ) : (B [[r + (-power - 1) - offset]]) ((A [[offset]]) vector) = 0 := by
      by_cases within : offset ≤ cutoff
      · have inOrders : ((HahnModule.of ℂ).symm (B ((A [[offset]]) vector))).order + r - offset ∈ orders := Finset.mem_image.mpr ⟨offset, Finset.mem_range.mpr (by omega),
        rfl⟩
        have bound := Finset.min'_le orders _ inOrders
        apply VertexOperator.ncoeff_eq_zero_of_lt_order; dsimp [lower] at small; omega
      · have vanish : (A [[offset]]) vector = 0 := by
          apply VertexOperator.ncoeff_eq_zero_of_lt_order; dsimp [cutoff] at within; omega
        simp [vanish]
    exact member (by simp [coefficient, residueCoefficient, residueLeft, residueRight, firstZero, secondZero])
  refine ⟨VertexOperator.of_coeff (fun power => coefficient (-power - 1)) bounded, ?_, leftFinite, rightFinite⟩; intro n vector
  rw [VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]; rfl

private theorem positiveModes (s : ℂ) (A B : VertexOperator ℂ V) (r : ℕ) (n : ℤ) (vector : V) : (((residueField s r A B).operator) [[n]]) vector = ((deltaEnd ^ r) (signedComm s A B)) 0 n vector :=
    by
    have chooseNat (offset : ℕ) : integerBinomial r offset = (r.choose offset : ℂ) := by simp [integerBinomial, Ring.choose_natCast]
    have leftSum : residueLeft r n A B vector = ∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • (A [[(r : ℤ) - offset]]) ((B [[n +
      offset]]) vector) := by
      unfold residueLeft; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
      by_contra outside
      have zeroChoose : r.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
      exact member (by simp [zeroChoose])
    have rightSum : residueRight r n A B vector = ∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • (B [[(r : ℤ) + n - offset]]) ((A
      [[offset]]) vector) := by
      unfold residueRight; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
      by_contra outside
      have zeroChoose : r.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
      exact member (by simp [zeroChoose])
    rw [(residueField s r A B).coefficient, residueCoefficient, leftSum, rightSum, FieldDeltaBinomial.delta_binomial, LinearMap.sum_apply]
    simp only [zero_add, LinearMap.smul_apply, signedComm, Module.End.mul_apply, LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib, smul_smul]
    apply congrArg ((∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • (A [[(r : ℤ) - offset]]) ((B [[n + offset]]) vector)) - ·)
    rw [Finset.smul_sum, ← Finset.sum_range_reflect]; apply Finset.sum_congr rfl; intro offset member
    have within : offset ≤ r := by simpa using Finset.mem_range.mp member
    simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, epsilon, zpow_natCast]
    have signs : (-1 : ℂ) ^ r * ((-1 : ℂ) ^ (r - offset) * (r.choose offset : ℂ)) = (-1 : ℂ) ^ offset * (r.choose offset : ℂ) := by
      have split : (-1 : ℂ) ^ r = (-1 : ℂ) ^ offset * (-1 : ℂ) ^ (r - offset) := by rw [← pow_add, Nat.add_sub_of_le within]
      rw [split]
      have squared : ((-1 : ℂ) ^ (r - offset)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      calc
        _ = (-1 : ℂ) ^ offset * (((-1 : ℂ) ^ (r - offset)) ^ 2) * (r.choose offset : ℂ) := by ring
        _ = _ := by rw [squared]; ring
    have signedWeight : ((-1 : ℂ) ^ r * s) *
        ((-1 : ℂ) ^ (r - offset) * (r.choose offset : ℂ)) =
          ((-1 : ℂ) ^ offset * (r.choose offset : ℂ)) * s := by
      calc
        _ = ((-1 : ℂ) ^ r *
          ((-1 : ℂ) ^ (r - offset) * (r.choose offset : ℂ))) * s := by ring
        _ = _ := by rw [signs]
    rw [signedWeight]; push_cast [Int.natCast_sub within]; rw [show (r : ℤ) + n - ((r : ℤ) - offset) = n + offset by omega]

theorem negativeResidue (s : ℂ) (A B : VertexOperator ℂ V) (degree : ℕ) : (residueField s (-(degree : ℤ) - 1) A B).operator = (signedNormalMinusOne s (dividedDerivative degree A) B).1 := by
  have derivativeModes (index : ℤ) (vector : V) : ((dividedDerivative degree A) [[index]]) vector = ((Ring.choose (-index - 1 + degree) degree : ℤ) : ℂ) • (A
    [[index - degree]]) vector := by
    change Ring.choose (-index - 1 + degree) degree • HVertexOperator.coeff A (-index - 1 + degree) vector = _
    rw [VertexOperator.coeff_eq_ncoeff, show -(-index - 1 + degree) - 1 = index - degree by omega, ← Int.cast_smul_eq_zsmul ℂ]
  have square (offset : ℕ) : (-1 : ℂ) ^ offset * (-1 : ℂ) ^ offset = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have negativeChoose (offset : ℕ) : (((Ring.choose (-(degree : ℤ) - 1) offset : ℤ) : ℂ)) = (-1 : ℂ) ^ offset * ((degree + offset).choose degree : ℂ) := by
    rw [show -(degree : ℤ) - 1 = -((degree : ℤ) + 1) by omega, Ring.choose_neg, show (degree : ℤ) + 1 + offset - 1 = ((degree + offset : ℕ) : ℤ) by omega,
      Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast, Int.cast_natCast]; rw [← Nat.choose_symm_add]
  have weight (offset : ℕ) : (-1 : ℂ) ^ offset * integerBinomial (-(degree : ℤ) - 1) offset = ((degree + offset).choose degree : ℂ) := by
    rw [integerBinomial, negativeChoose, ← mul_assoc, square, one_mul]
  have sign : -epsilon (-(degree : ℤ) - 1) = (-1 : ℂ) ^ degree := by
    rw [epsilon, show -(degree : ℤ) - 1 = -((degree + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow]; norm_num [pow_succ]
  apply HVertexOperator.coeff_inj; funext power; apply LinearMap.ext; intro vector
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, (residueField s (-(degree : ℤ) - 1) A B).coefficient, (signedNormalMinusOne s (dividedDerivative degree A) B).2]
  let index : ℤ := -power - 1
  have firstEquality : residueLeft (-(degree : ℤ) - 1) index A B vector = ∑ᶠ offset : ℕ, ((dividedDerivative degree A) [[-(offset : ℤ) - 1]]) ((B [[index + offset]])
    vector) := by
    unfold residueLeft; apply finsum_congr; intro offset; rw [weight, derivativeModes]
    have parameter : -(-(offset : ℤ) - 1) - 1 + degree = ((degree + offset : ℕ) : ℤ) := by omega
    rw [parameter, Ring.choose_natCast]; rw [show -(degree : ℤ) - 1 - offset = -(offset : ℤ) - 1 - degree by omega]
    simp only [Int.cast_natCast]
  let term (offset : ℕ) : V := (B [[index - offset - 1]]) (((dividedDerivative degree A) [[offset]]) vector)
  have initialZero (offset : Fin degree) : term offset = 0 := by
    have parameter : -(offset : ℤ) - 1 + degree = ((degree - offset - 1 : ℕ) : ℤ) := by omega
    have zeroChoose : Ring.choose (-(offset : ℤ) - 1 + degree) degree = 0 := by rw [parameter, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]; rfl
    simp [term, derivativeModes, zeroChoose]
  have split : (∑ᶠ offset : ℕ, term offset) = ∑ᶠ offset : ℕ, term (degree + offset) := by
    have subset : Function.support term ⊆ Set.range (fun offset : ℕ => degree + offset) := by
      intro offset member
      have bound : degree ≤ offset := by by_contra smaller; exact member (initialZero ⟨offset, by omega⟩)
      exact ⟨offset - degree, by change degree + (offset - degree) = offset; omega⟩
    have sets : Set.range (fun offset : ℕ => degree + offset) ∩ Function.support term = Set.univ ∩ Function.support term := by rw [Set.inter_eq_right.mpr subset, Set.univ_inter]
    rw [← finsum_mem_range (f := term) (g := fun offset : ℕ => degree + offset) (fun first second equality => Nat.add_left_cancel equality), finsum_mem_inter_support_eq term
      _ _ sets, finsum_mem_univ]
  have secondEquality : (∑ᶠ offset : ℕ, term offset) = (-1 : ℂ) ^ degree • residueRight (-(degree : ℤ) - 1) index A B vector := by
    rw [split, residueRight, smul_finsum' _ ((residueField s (-(degree : ℤ) - 1) A B).right_finite index vector)]; apply finsum_congr
    intro offset; dsimp [term]; rw [derivativeModes, map_smul, weight]
    rw [show -((degree : ℤ) + offset) - 1 + degree = -(offset : ℤ) - 1 by omega, show -(offset : ℤ) - 1 = -((offset : ℤ) + 1) by omega, Ring.choose_neg, show (offset : ℤ) + 1
      + degree - 1 = ((degree + offset : ℕ) : ℤ) by omega, Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast, Int.cast_natCast, smul_smul]
    rw [show (degree : ℤ) + offset - degree = offset by omega, show index - ((degree : ℤ) + offset) - 1 = -(degree : ℤ) - 1 + index - offset by omega]
  change residueCoefficient s (-(degree : ℤ) - 1) index A B vector = _
  rw [residueCoefficient, firstEquality]
  change _ - (epsilon (-(degree : ℤ) - 1) * s) • residueRight (-(degree : ℤ) - 1) index A B vector = _ + s • (∑ᶠ offset : ℕ, term offset)
  rw [secondEquality, sub_eq_add_neg, ← neg_smul, ← neg_mul, sign, mul_smul,
      smul_comm ((-1 : ℂ) ^ degree) s]

private theorem positiveLocality (x y z : ℂ) (A B C : VertexOperator ℂ V) (r Na Nb Nc : ℕ)
    (hAC : delta^[Na] (signedComm y A C) = 0)
    (hBC : delta^[Nb] (signedComm z B C) = 0)
    (hAB : delta^[Nc] (signedComm x A B) = 0) :
    delta^[Na + Nb + Nc]
      (signedComm (y * z) (residueField x r A B).operator C) = 0 := by
  funext l k
  apply LinearMap.ext
  intro v
  let pair := signedTriple x y z A B C v
  let shifted := ((deltaXY ^ (r + 1) : Module.End ℂ (PairSpace V))) pair
  have commute : Commute (deltaXY (V := V))
      ((deltaXY + deltaYZ) ^ Na * deltaYZ ^ Nb) :=
    (((Commute.refl deltaXY).add_right shiftsCommute).pow_right Na).mul_right
      (shiftsCommute.pow_right Nb)
  have low : (((deltaXY + deltaYZ) ^ Na * deltaYZ ^ Nb : Module.End ℂ (PairSpace V)))
      shifted = 0 := by
    dsimp only [shifted, pair]
    rw [← Module.End.mul_apply, (commute.pow_left (r + 1)).symm.eq,
      Module.End.mul_apply, signedPair_low x y z A B C v Na Nb hAC hBC,
      map_zero]
  have high : discrepancy ((deltaXY ^ Nc) shifted) = 0 := by
    dsimp only [shifted, pair]
    rw [← Module.End.mul_apply, (Commute.refl deltaXY).pow_pow Nc (r + 1) |>.eq,
      Module.End.mul_apply, intertwiningPowers (deltaXY (V := V)) (plainXY (V := V))
        (discrepancy (V := V)) discrepancyXY (r + 1),
      signedPair_high x y z A B C v Nc hAB, map_zero]
  have cancelled := cancellationBound shifted Na Nb Nc low high
  let lifting := liftAB C v true - (y * z) • liftAB C v false
  have difference : discrepancy pair = lifting (signedComm x A B) := by
    funext i j k
    change (signedTriple x y z A B C v).val.1 i j k -
      (signedTriple x y z A B C v).val.2 i j k = _
    rw [(signedTriple_coefficients x y z A B C v i j k).1,
      (signedTriple_coefficients x y z A B C v i j k).2]
    simp only [lifting, liftAB, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, ite_true, Bool.false_eq_true, ite_false,
      signedComm, Module.End.mul_apply, map_sub, map_smul, smul_smul,
      Pi.sub_apply, Pi.smul_apply]
    module
  have liftingLaw (D : ℤ → ℤ → Module.End ℂ V) :
      lifting (deltaEnd D) = plainXY (lifting D) := by
    funext i j k
    dsimp [lifting, liftAB, deltaEnd, delta, plainXY, shiftXY]
    simp only [map_sub]
    module
  have connection : res shifted = evaluate v
      (signedComm (y * z) (residueField x r A B).operator C) := by
    funext j k
    dsimp only [shifted]
    rw [pow_succ', Module.End.mul_apply]
    change residue (shiftXY ((deltaXY ^ r) pair).val.1)
      (shiftXY ((deltaXY ^ r) pair).val.2) j k = _
    rw [residueXY _ _ ((deltaXY ^ r) pair).property.1 ((deltaXY ^ r) pair).property.2]
    change discrepancy ((deltaXY ^ r) pair) 0 j k = _
    rw [intertwiningPowers (deltaXY (V := V)) (plainXY (V := V))
        (discrepancy (V := V)) discrepancyXY r pair, difference,
      ← intertwiningPowers (deltaEnd (V := V)) (plainXY (V := V))
        lifting liftingLaw r (signedComm x A B)]
    dsimp only [lifting, liftAB, evaluate, signedComm]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, ite_true, Bool.false_eq_true, ite_false, Pi.sub_apply,
      Pi.smul_apply, Module.End.mul_apply]
    rw [← positiveModes x A B r j ((C [[k]]) v), ← positiveModes x A B r j v]
    simp only [signedComm, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.mul_apply]
  change delta^[Na + Nb + Nc] (res shifted) = 0 at cancelled
  rw [connection] at cancelled
  have evaluationLaw (D : ℤ → ℤ → Module.End ℂ V) :
      evaluate v (deltaEnd D) = plainDelta (evaluate v D) := rfl
  have transport := intertwiningPowers deltaEnd plainDelta (evaluate v) evaluationLaw
    (Na + Nb + Nc) (signedComm (y * z) (residueField x r A B).operator C)
  rw [Module.End.pow_apply, Module.End.pow_apply] at transport
  change evaluate v (delta^[Na + Nb + Nc]
    (signedComm (y * z) (residueField x r A B).operator C)) =
      delta^[Na + Nb + Nc] (evaluate v
        (signedComm (y * z) (residueField x r A B).operator C)) at transport
  rw [cancelled] at transport
  exact congrFun (congrFun transport l) k

/-- Signed Dong locality for every integer residue and three independent signs.
All sums defining the residue have finite support only after vector evaluation. -/
theorem residue_locality (x y z : ℂ) (A B C : VertexOperator ℂ V)
    (hAC : ∃ N : ℕ, delta^[N] (signedComm y A C) = 0)
    (hBC : ∃ N : ℕ, delta^[N] (signedComm z B C) = 0)
    (hAB : ∃ N : ℕ, delta^[N] (signedComm x A B) = 0) (r : ℤ) :
    ∃ N : ℕ, delta^[N] (signedComm (y * z) (residueField x r A B).operator C) = 0 := by
  obtain ⟨Na, hAC⟩ := hAC
  obtain ⟨Nb, hBC⟩ := hBC
  obtain ⟨Nc, hAB⟩ := hAB
  by_cases nonnegative : 0 ≤ r
  · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
    exact ⟨Na + Nb + Nc, positiveLocality x y z A B C degree Na Nb Nc hAC hBC hAB⟩
  · let degree := (-r - 1).toNat
    have hr : r = -(degree : ℤ) - 1 := by dsimp [degree]; omega
    rw [hr, negativeResidue]
    exact ⟨Na + degree + Nb + (Nc + degree),
      signedNormal_locality x y z _ B C (Na + degree) Nb (Nc + degree)
        (signedDerivative_locality y A C Na degree hAC) hBC
        (signedDerivative_locality x A B Nc degree hAB)⟩

theorem residue_translation (s : ℂ) (r : ℤ) (A B : VertexOperator ℂ V)
    (T : Module.End ℂ V)
    (hA : ∀ m : ℤ, T * (A [[m]]) - (A [[m]]) * T = -(m : ℂ) • (A [[m - 1]]))
    (hB : ∀ m : ℤ, T * (B [[m]]) - (B [[m]]) * T = -(m : ℂ) • (B [[m - 1]]))
    (index : ℤ) : T * (((residueField s r A B).operator) [[index]]) - (((residueField s r A B).operator) [[index]]) * T = -(index : ℂ) • (((residueField s r A
    B).operator) [[index - 1]]) := by
    let translationOp := T
    let weight (offset : ℕ) : ℂ := (-1 : ℂ) ^ offset * integerBinomial r offset
    have relation (offset : ℕ) : weight (offset + 1) * ((offset : ℂ) + 1) = -(weight offset * ((r : ℂ) - offset)) := by
      have raw := Ring.choose_smul_choose r (n := offset + 1) (k := offset) (Nat.le_succ offset)
      simp only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right, nsmul_eq_mul] at raw
      have complex : ((offset : ℂ) + 1) * integerBinomial r (offset + 1) = integerBinomial r offset * ((r : ℂ) - offset) := by
        dsimp [integerBinomial]
        exact_mod_cast raw
      dsimp [weight]; rw [pow_succ]
      calc
        _ = -((-1 : ℂ) ^ offset * (((offset : ℂ) + 1) * integerBinomial r (offset + 1))) := by ring
        _ = _ := by rw [complex]; ring
    have forwardFinite (outer inner : VertexOperator ℂ V) (start finish : ℤ) (vector : V) : Function.HasFiniteSupport (fun offset : ℕ =>
          (outer [[start - offset]]) ((inner [[finish + offset]]) vector)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm (inner vector)).order - finish).toNat, ?_⟩
      intro offset member
      contrapose! member
      have vanish : (inner [[finish + offset]]) vector = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      simp [vanish]
    let zeroSucc : Option ℕ ≃ ℕ := {
      toFun value := match value with | none => 0 | some offset => offset + 1
      invFun value := match value with | 0 => none | offset + 1 => some offset
      left_inv value := by cases value <;> rfl
      right_inv value := by cases value <;> rfl }
    have shiftSum (term : ℕ → V) (finite : Function.HasFiniteSupport term) (atZero : term 0 = 0) : ∑ᶠ offset : ℕ, term offset = ∑ᶠ offset : ℕ, term (offset + 1) := by
      rw [← finsum_comp_equiv zeroSucc, finsum_option]
      · simp [zeroSucc, atZero]
      · change Function.HasFiniteSupport (fun offset : ℕ => term (offset + 1))
        exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have telescope (sequence : ℤ → V) (finite : Function.HasFiniteSupport (fun offset : ℕ => sequence offset)) (shiftedFinite : Function.HasFiniteSupport (fun offset : ℕ =>
      sequence ((offset : ℤ) - 1))) : Function.HasFiniteSupport (fun offset : ℕ => weight offset • (((r : ℂ) - offset) • sequence offset + (offset : ℂ) • sequence ((offset : ℤ) -
      1))) ∧ (∑ᶠ offset : ℕ, weight offset • (((r : ℂ) - offset) • sequence offset + (offset : ℂ) • sequence ((offset : ℤ) - 1))) = 0 := by
      have firstFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          (weight offset * ((r : ℂ) - offset)) • sequence offset) :=
        finite.smul_right (fun offset => weight offset * ((r : ℂ) - offset))
      have secondFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          (weight offset * (offset : ℂ)) • sequence ((offset : ℤ) - 1)) :=
        shiftedFinite.smul_right (fun offset => weight offset * (offset : ℂ))
      constructor
      · simpa only [Pi.add_def, smul_add, smul_smul] using firstFinite.add secondFinite
      · simp only [smul_add, smul_smul]
        rw [finsum_add_distrib firstFinite secondFinite, shiftSum _ secondFinite (by simp)]
        have shifted (offset : ℕ) : (weight (offset + 1) * ((offset + 1 : ℕ) : ℂ)) • sequence (((offset + 1 : ℕ) : ℤ) - 1) = -((weight offset * ((r : ℂ) - offset)) • sequence
          offset) := by rw [Nat.cast_add, Nat.cast_one, relation, show ((offset + 1 : ℕ) : ℤ) - 1 = offset by omega, neg_smul]
        simp_rw [shifted]; rw [finsum_neg_distrib]; abel
    let weightedSum (outer inner : VertexOperator ℂ V) (start finish : ℤ) (vector : V) : V := ∑ᶠ offset : ℕ, weight offset • (outer [[start - offset]]) ((inner [[finish +
      offset]]) vector)
    have branchLaw (outer inner : VertexOperator ℂ V) (outerLaw : ∀ mode : ℤ, translationOp * (outer [[mode]]) - (outer [[mode]]) * translationOp = -(mode : ℂ) • (outer [[mode -
      1]])) (innerLaw : ∀ mode : ℤ, translationOp * (inner [[mode]]) - (inner [[mode]]) * translationOp = -(mode : ℂ) • (inner [[mode - 1]])) (start finish : ℤ) (vector : V) :
      translationOp (weightedSum outer inner start finish vector) - weightedSum outer inner start finish (translationOp vector) = -((start : ℂ) - r) • weightedSum outer inner (start -
      1) finish vector - (finish : ℂ) • weightedSum outer inner start (finish - 1) vector := by
      let sequence (mode : ℤ) : V := (outer [[start - mode - 1]]) ((inner [[finish + mode]]) vector)
      have sequenceFinite : Function.HasFiniteSupport (fun offset : ℕ => sequence offset) := by simpa only [sequence, sub_right_comm] using forwardFinite outer inner (start - 1) finish vector
      have sequenceShifted : Function.HasFiniteSupport (fun offset : ℕ => sequence ((offset : ℤ) - 1)) := by
        have arithmetic (offset : ℕ) : start - ((offset : ℤ) - 1) - 1 = start - offset := by omega
        simpa only [sequence, arithmetic, add_sub_assoc, sub_add_eq_add_sub] using forwardFinite outer inner start (finish - 1) vector
      have cancellation := telescope sequence sequenceFinite sequenceShifted
      let terms (offset : ℕ) : Module.End ℂ V := weight offset • ((outer [[start - offset]]) * (inner [[finish + offset]]))
      have finiteTerms (input : V) : Function.HasFiniteSupport (fun offset => terms offset input) := (forwardFinite outer inner start finish input).smul_right weight
      have commuteSum : translationOp (∑ᶠ offset : ℕ, terms offset vector) - ∑ᶠ offset : ℕ, terms offset (translationOp vector) = ∑ᶠ offset : ℕ, (translationOp * terms offset - terms
        offset * translationOp) vector := by
        rw [map_finsum translationOp (finiteTerms vector), ← finsum_sub_distrib ((finiteTerms vector).fun_comp (map_zero translationOp)) (finiteTerms (translationOp vector))]
        rfl
      have productLaw (first second : ℤ) : translationOp * ((outer [[first]]) * (inner [[second]])) - ((outer [[first]]) * (inner [[second]])) * translationOp = -(first : ℂ) • ((outer
        [[first - 1]]) * (inner [[second]])) + -(second : ℂ) • ((outer [[first]]) * (inner [[second - 1]])) := by
        calc
          _ = (translationOp * (outer [[first]]) - (outer [[first]]) * translationOp) * (inner [[second]]) + (outer [[first]]) * (translationOp * (inner [[second]]) - (inner [[second]])
            * translationOp) := by simp only [mul_sub, sub_mul, mul_assoc]; abel
          _ = _ := by rw [outerLaw, innerLaw]; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      have pointwise (offset : ℕ) : (translationOp * terms offset - terms offset * translationOp) vector = (-((start : ℂ) - r) • (weight offset • sequence offset) - (finish : ℂ) •
        (weight offset • sequence ((offset : ℤ) - 1))) - weight offset • (((r : ℂ) - offset) • sequence offset + (offset : ℂ) • sequence ((offset : ℤ) - 1)) := by
        dsimp only [terms]; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub, productLaw]
        simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply]; dsimp only [sequence]
        rw [show start - ((offset : ℤ) - 1) - 1 = start - offset by omega, show finish + ((offset : ℤ) - 1) = finish + offset - 1 by omega]
        push_cast; module
      change translationOp (∑ᶠ offset : ℕ, terms offset vector) - ∑ᶠ offset : ℕ, terms offset (translationOp vector) = _; rw [commuteSum]
      simp_rw [pointwise]
      have firstFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          -((start : ℂ) - r) • (weight offset • sequence offset)) :=
        (sequenceFinite.smul_right weight).smul_right (fun _ => -((start : ℂ) - r))
      have secondFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          (finish : ℂ) • (weight offset • sequence ((offset : ℤ) - 1))) :=
        (sequenceShifted.smul_right weight).smul_right (fun _ => (finish : ℂ))
      have mainFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          -((start : ℂ) - r) • (weight offset • sequence offset) - (finish : ℂ) • (weight offset • sequence ((offset : ℤ) - 1))) :=
        firstFinite.sub secondFinite
      have sequenceWeighted : Function.HasFiniteSupport (fun offset : ℕ => weight offset • sequence offset) := sequenceFinite.smul_right weight
      have shiftedWeighted : Function.HasFiniteSupport (fun offset : ℕ =>
          weight offset • sequence ((offset : ℤ) - 1)) := sequenceShifted.smul_right weight
      rw [finsum_sub_distrib mainFinite cancellation.1, cancellation.2, sub_zero, finsum_sub_distrib firstFinite secondFinite, ← smul_finsum' _ sequenceWeighted, ← smul_finsum' _
        shiftedWeighted]
      congr 1
      · dsimp [weightedSum, sequence]
        apply congrArg (fun value : V => -((start : ℂ) - r) • value); apply finsum_congr; intro offset
        rw [show start - (offset : ℤ) - 1 = start - 1 - offset by omega]
      · dsimp [weightedSum, sequence]
        apply congrArg (fun value : V => (finish : ℂ) • value); apply finsum_congr; intro offset
        rw [show start - ((offset : ℤ) - 1) - 1 = start - offset by omega, show finish + ((offset : ℤ) - 1) = finish - 1 + offset by omega]
    have firstMatch (mode : ℤ) (input : V) : residueLeft r mode A B input = weightedSum A B r mode input := by rfl
    have secondMatch (mode : ℤ) (input : V) : residueRight r mode A B input = weightedSum B A (r + mode) 0 input := by dsimp only [residueRight, weightedSum]; simp only [zero_add, weight]
    apply LinearMap.ext; intro vector
    change translationOp ((((residueField s r A B).operator) [[index]]) vector) - (((residueField s r A B).operator) [[index]]) (translationOp vector) = -(index : ℂ) • ((((residueField s r A
      B).operator) [[index - 1]]) vector)
    rw [(residueField s r A B).coefficient, (residueField s r A B).coefficient, (residueField s r A B).coefficient]
    have firstLaw := branchLaw A B hA hB r index vector
    have secondLaw := branchLaw B A hB hA (r + index) 0 vector
    simp only [sub_self, Int.cast_add, add_sub_cancel_left] at firstLaw secondLaw; simp only [residueCoefficient, firstMatch, secondMatch]
    rw [map_sub, map_smul]
    have arithmetic : r + index - 1 = r + (index - 1) := by omega
    rw [arithmetic] at secondLaw
    calc
      _ = (translationOp (weightedSum A B r index vector) - weightedSum A B r index (translationOp vector)) - (epsilon r * s) • (translationOp (weightedSum B A (r +
        index) 0 vector) - weightedSum B A (r + index) 0 (translationOp vector)) := by module
      _ = _ := by rw [firstLaw, secondLaw]; module


end D5.S3.VertexAlgebra.SignedFieldResidueLocality
