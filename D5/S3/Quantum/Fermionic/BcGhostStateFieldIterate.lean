/- GID: D5/S3/Quantum/Fermionic/BcGhostStateFieldIterate
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostStateFieldIterate
   mirror-E: none(waiver:algebraic-ghost-signed-iterate)
   anchors: []
   utility: none
   digest: Signed integer residue closure on the original ghost occupation carrier. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The finite-support residue constructor and translation telescope adapt
D5.S3.VertexAlgebra.StateFieldResidueReconstruction, itself attributed to
ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea.
The reverse residue has its actual homogeneous super sign throughout.
-/

/-
proof_shape: stateField_iterate: content
escape_witness: Signed positive-residue locality and signed negative normal products
combine with original translation and creative occupation-basis uniqueness. This
identifies the actual residue with the field of the actual all-integer mode product.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostStateField
open D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open private signedNormalMinusOne derivative_modes forward_finite reverse_finite from
  D5.S3.Quantum.Fermionic.BcGhostStateField
open private signedComm signedTriple signedTriple_coefficients signedPair_low
  signedPair_high signedNormal_locality signedDerivative_locality from
  D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
open private shiftsCommute discrepancyXY residueXY residueYZ intertwiningPowers
  cancellationBound from D5.S3.VertexAlgebra.FieldNormalProductLocality
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate

private def residueLeft (r n : ℤ) (a b vector : Fock) : Fock :=
  ∑ᶠ offset : ℕ, (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y a) [[r - offset]]) (((Y b) [[n + offset]])
    vector)

private def residueRight (r n : ℤ) (a b vector : Fock) : Fock :=
  ∑ᶠ offset : ℕ, (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y b) [[r + n - offset]]) (((Y a) [[offset]])
    vector)

private def residueCoefficient (s : ℂ) (r n : ℤ) (a b vector : Fock) : Fock :=
  residueLeft r n a b vector - (epsilon r * s) • residueRight r n a b vector

private structure ResidueField (s : ℂ) (r : ℤ) (a b : Fock) where
  operator : VertexOperator ℂ Fock
  coefficient : ∀ n vector, (operator [[n]]) vector = residueCoefficient s r n a b vector
  left_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y a) [[r - offset]]) (((Y b) [[n + offset]]) vector))
  right_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y b) [[r + n - offset]]) (((Y a) [[offset]]) vector))

private def residueField (s : ℂ) (r : ℤ) (a b : Fock) : ResidueField s r a b := by
  classical
  have leftKernel (m n : ℤ) (A B : VertexOperator ℂ Fock) (vector : Fock) : (Function.support fun offset : ℕ => (Int.negOnePow offset) • Ring.choose n offset • (A [[n - offset]])
    ((B [[-m - 1 + offset]]) vector)).Finite := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm (B vector)).order + m).toNat, ?_⟩; intro offset member
    contrapose! member
    suffices (B [[-m - 1 + offset]]) vector = 0 by simp [this]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
  have rightKernel (m n : ℤ) (A B : VertexOperator ℂ Fock) (vector : Fock) : (Function.support fun offset : ℕ => (Int.negOnePow offset) • Ring.choose n offset • (B [[n + (-m - 1) -
    offset]]) ((A [[offset]]) vector)).Finite := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm (A vector)).order - 1).toNat, ?_⟩; intro offset member
    contrapose! member
    suffices (A [[offset]]) vector = 0 by simp [this]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
  have leftFinite (n : ℤ) (vector : Fock) : Function.HasFiniteSupport (fun offset : ℕ =>
      (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y a) [[r - offset]]) (((Y b) [[n + offset]]) vector)) := by
    have finite := leftKernel (-n - 1) r (Y a) (Y b) vector
    simpa only [Function.HasFiniteSupport, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_smul, integerBinomial, show -(-n - 1) - 1 = n by omega]
      using finite
  have rightFinite (n : ℤ) (vector : Fock) : Function.HasFiniteSupport (fun offset : ℕ =>
      (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y b) [[r + n - offset]]) (((Y a) [[offset]]) vector)) := by
    have finite := rightKernel (-n - 1) r (Y a) (Y b) vector
    simpa only [Function.HasFiniteSupport, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_smul, integerBinomial, show -(-n - 1) - 1 = n by omega]
      using finite
  let coefficient (n : ℤ) : Module.End ℂ Fock := {
    toFun := residueCoefficient s r n a b
    map_add' first second := by
      dsimp [residueCoefficient, residueLeft, residueRight]; simp only [map_add, smul_add]
      rw [finsum_add_distrib (leftFinite n first) (leftFinite n second), finsum_add_distrib (rightFinite n first) (rightFinite n second)]
      module
    map_smul' scalar vector := by
      dsimp [residueCoefficient, residueLeft, residueRight]; simp only [map_smul, RingHom.id_apply]; simp_rw [smul_comm _ scalar]
      rw [← smul_finsum' scalar (leftFinite n vector), ← smul_finsum' scalar (rightFinite n vector)]
      rw [smul_comm (epsilon r * s) scalar, ← smul_sub] }
  have bounded (vector : Fock) : BddBelow (Function.support (fun power : ℤ => coefficient (-power - 1) vector)) := by
    let cutoff : ℕ := (-((HahnModule.of ℂ).symm ((Y a) vector)).order - 1).toNat
    let orders : Finset ℤ := (Finset.range (cutoff + 1)).image (fun offset : ℕ =>
      ((HahnModule.of ℂ).symm ((Y b) (((Y a) [[offset]]) vector))).order + r - offset)
    let lower : ℤ := min ((HahnModule.of ℂ).symm ((Y b) vector)).order (orders.min' (by
        apply Finset.image_nonempty.mpr; exact ⟨0, Finset.mem_range.mpr (by omega)⟩))
    refine ⟨lower, ?_⟩; intro power member; by_contra notLower
    have small : power < lower := lt_of_not_ge notLower
    have firstZero (offset : ℕ) : ((Y a) [[r - offset]]) (((Y b) [[-power - 1 + offset]]) vector) = 0 := by
      have vanish : ((Y b) [[-power - 1 + offset]]) vector = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; dsimp [lower] at small; omega
      simp [vanish]
    have secondZero (offset : ℕ) : ((Y b) [[r + (-power - 1) - offset]]) (((Y a) [[offset]]) vector) = 0 := by
      by_cases within : offset ≤ cutoff
      · have inOrders : ((HahnModule.of ℂ).symm ((Y b) (((Y a) [[offset]]) vector))).order + r - offset ∈ orders := Finset.mem_image.mpr ⟨offset, Finset.mem_range.mpr (by omega),
        rfl⟩
        have bound := Finset.min'_le orders _ inOrders
        apply VertexOperator.ncoeff_eq_zero_of_lt_order; dsimp [lower] at small; omega
      · have vanish : ((Y a) [[offset]]) vector = 0 := by
          apply VertexOperator.ncoeff_eq_zero_of_lt_order; dsimp [cutoff] at within; omega
        simp [vanish]
    exact member (by simp [coefficient, residueCoefficient, residueLeft, residueRight, firstZero, secondZero])
  refine ⟨VertexOperator.of_coeff (fun power => coefficient (-power - 1)) bounded, ?_, leftFinite, rightFinite⟩; intro n vector
  rw [VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]; rfl

private theorem binomial (value : ℤ → ℤ → Module.End ℂ Fock) (order : ℕ) (first second : ℤ) : ((deltaEnd ^ order) value) first second = ∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^
    offset) * (order.choose offset : ℂ)) • value (first + (order : ℤ) - offset) (second + offset) := by
  let shiftLeft : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock) := {
    toFun value := fun first second => value (first + 1) second
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock) := {
    toFun value := fun first second => value first (second + 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have commute : Commute (-shiftRight) shiftLeft := by apply LinearMap.ext; intro distribution; funext left right; simp [shiftLeft, shiftRight]
  have leftPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ Fock) : (shiftLeft ^ degree) distribution = fun left right => distribution (left + degree) right := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
      change distribution (left + 1 + degree) right = distribution (left + (degree + 1 : ℕ)) right; congr 1; push_cast; omega
  have rightPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ Fock) : ((-shiftRight) ^ degree) distribution = fun left right => ((-1 : ℂ) ^ degree) • distribution left
    (right + degree) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
      change -(((-1 : ℂ) ^ degree) • distribution left (right + 1 + degree)) = ((-1 : ℂ) ^ (degree + 1)) • distribution left (right + (degree + 1 : ℕ))
      rw [pow_succ', mul_smul, neg_one_smul]
      have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by push_cast; omega
      rw [indices]
  have equation : (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock)) = -shiftRight + shiftLeft := by
    apply LinearMap.ext; intro distribution; funext left right; simp [deltaEnd, delta, shiftLeft, shiftRight]
    abel
  rw [equation, commute.add_pow, LinearMap.sum_apply]; simp only [Finset.sum_apply]; apply Finset.sum_congr rfl; intro offset member
  have within : offset ≤ order := by simpa using Finset.mem_range.mp member
  simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, rightPower, leftPower, Pi.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]; congr 2; push_cast [Int.natCast_sub within]; omega

private theorem positiveModes (s : ℂ) (a b : Fock) (r : ℕ) (n : ℤ) (vector : Fock) : (((residueField s r a b).operator) [[n]]) vector = ((deltaEnd ^ r) (signedComm s (Y a) (Y b))) 0 n vector :=
    by
    have chooseNat (offset : ℕ) : integerBinomial r offset = (r.choose offset : ℂ) := by simp [integerBinomial, Ring.choose_natCast]
    have leftSum : residueLeft r n a b vector = ∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • ((Y a) [[(r : ℤ) - offset]]) (((Y b) [[n +
      offset]]) vector) := by
      unfold residueLeft; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
      by_contra outside
      have zeroChoose : r.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
      exact member (by simp [zeroChoose])
    have rightSum : residueRight r n a b vector = ∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • ((Y b) [[(r : ℤ) + n - offset]]) (((Y a)
      [[offset]]) vector) := by
      unfold residueRight; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
      by_contra outside
      have zeroChoose : r.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
      exact member (by simp [zeroChoose])
    rw [(residueField s r a b).coefficient, residueCoefficient, leftSum, rightSum, binomial, LinearMap.sum_apply]
    simp only [zero_add, LinearMap.smul_apply, signedComm, Module.End.mul_apply, LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib, smul_smul]
    apply congrArg ((∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • ((Y a) [[(r : ℤ) - offset]]) (((Y b) [[n + offset]]) vector)) - ·)
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

private theorem residue_translation (s : ℂ) (r : ℤ) (a b : Fock) (index : ℤ) : BcGhostVirasoro.L (-1) * (((residueField s r a b).operator) [[index]]) - (((residueField s r a b).operator) [[index]]) * BcGhostVirasoro.L (-1) = -(index : ℂ) • (((residueField s r a
    b).operator) [[index - 1]]) := by
    let translationOp := BcGhostVirasoro.L (-1)
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
    have forwardFinite (outer inner : VertexOperator ℂ Fock) (start finish : ℤ) (vector : Fock) : Function.HasFiniteSupport (fun offset : ℕ =>
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
    have shiftSum (term : ℕ → Fock) (finite : Function.HasFiniteSupport term) (atZero : term 0 = 0) : ∑ᶠ offset : ℕ, term offset = ∑ᶠ offset : ℕ, term (offset + 1) := by
      rw [← finsum_comp_equiv zeroSucc, finsum_option]
      · simp [zeroSucc, atZero]
      · change Function.HasFiniteSupport (fun offset : ℕ => term (offset + 1))
        exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have telescope (sequence : ℤ → Fock) (finite : Function.HasFiniteSupport (fun offset : ℕ => sequence offset)) (shiftedFinite : Function.HasFiniteSupport (fun offset : ℕ =>
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
    let weightedSum (outer inner : VertexOperator ℂ Fock) (start finish : ℤ) (vector : Fock) : Fock := ∑ᶠ offset : ℕ, weight offset • (outer [[start - offset]]) ((inner [[finish +
      offset]]) vector)
    have branchLaw (outer inner : VertexOperator ℂ Fock) (outerLaw : ∀ mode : ℤ, translationOp * (outer [[mode]]) - (outer [[mode]]) * translationOp = -(mode : ℂ) • (outer [[mode -
      1]])) (innerLaw : ∀ mode : ℤ, translationOp * (inner [[mode]]) - (inner [[mode]]) * translationOp = -(mode : ℂ) • (inner [[mode - 1]])) (start finish : ℤ) (vector : Fock) :
      translationOp (weightedSum outer inner start finish vector) - weightedSum outer inner start finish (translationOp vector) = -((start : ℂ) - r) • weightedSum outer inner (start -
      1) finish vector - (finish : ℂ) • weightedSum outer inner start (finish - 1) vector := by
      let sequence (mode : ℤ) : Fock := (outer [[start - mode - 1]]) ((inner [[finish + mode]]) vector)
      have sequenceFinite : Function.HasFiniteSupport (fun offset : ℕ => sequence offset) := by simpa only [sequence, sub_right_comm] using forwardFinite outer inner (start - 1) finish vector
      have sequenceShifted : Function.HasFiniteSupport (fun offset : ℕ => sequence ((offset : ℤ) - 1)) := by
        have arithmetic (offset : ℕ) : start - ((offset : ℤ) - 1) - 1 = start - offset := by omega
        simpa only [sequence, arithmetic, add_sub_assoc, sub_add_eq_add_sub] using forwardFinite outer inner start (finish - 1) vector
      have cancellation := telescope sequence sequenceFinite sequenceShifted
      let terms (offset : ℕ) : Module.End ℂ Fock := weight offset • ((outer [[start - offset]]) * (inner [[finish + offset]]))
      have finiteTerms (input : Fock) : Function.HasFiniteSupport (fun offset => terms offset input) := (forwardFinite outer inner start finish input).smul_right weight
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
        apply congrArg (fun value : Fock => -((start : ℂ) - r) • value); apply finsum_congr; intro offset
        rw [show start - (offset : ℤ) - 1 = start - 1 - offset by omega]
      · dsimp [weightedSum, sequence]
        apply congrArg (fun value : Fock => (finish : ℂ) • value); apply finsum_congr; intro offset
        rw [show start - ((offset : ℤ) - 1) - 1 = start - offset by omega, show finish + ((offset : ℤ) - 1) = finish - 1 + offset by omega]
    have firstMatch (mode : ℤ) (input : Fock) : residueLeft r mode a b input = weightedSum (Y a) (Y b) r mode input := by rfl
    have secondMatch (mode : ℤ) (input : Fock) : residueRight r mode a b input = weightedSum (Y b) (Y a) (r + mode) 0 input := by dsimp only [residueRight, weightedSum]; simp only [zero_add, weight]
    apply LinearMap.ext; intro vector
    change translationOp ((((residueField s r a b).operator) [[index]]) vector) - (((residueField s r a b).operator) [[index]]) (translationOp vector) = -(index : ℂ) • ((((residueField s r a
      b).operator) [[index - 1]]) vector)
    rw [(residueField s r a b).coefficient, (residueField s r a b).coefficient, (residueField s r a b).coefficient]
    have firstLaw := branchLaw (Y a) (Y b) (fun mode => stateField_translation.2 a mode) (fun mode => stateField_translation.2 b mode) r index vector
    have secondLaw := branchLaw (Y b) (Y a) (fun mode => stateField_translation.2 b mode) (fun mode => stateField_translation.2 a mode) (r + index) 0 vector
    simp only [sub_self, Int.cast_add, add_sub_cancel_left] at firstLaw secondLaw; simp only [residueCoefficient, firstMatch, secondMatch]
    rw [map_sub, map_smul]
    have arithmetic : r + index - 1 = r + (index - 1) := by omega
    rw [arithmetic] at secondLaw
    calc
      _ = (translationOp (weightedSum (Y a) (Y b) r index vector) - weightedSum (Y a) (Y b) r index (translationOp vector)) - (epsilon r * s) • (translationOp (weightedSum (Y b) (Y a) (r +
        index) 0 vector) - weightedSum (Y b) (Y a) (r + index) 0 (translationOp vector)) := by module
      _ = _ := by rw [firstLaw, secondLaw]; module

private theorem residue_creation (s : ℂ) (r : ℤ) (a b : Fock) : (((residueField s r a b).operator) [[-1]]) vacuum = ((Y a) [[r]]) b ∧ ∀ index : ℤ, 0 ≤ index → (((residueField s r a b).operator) [[index]]) vacuum = 0 := by

    have rightZero (index : ℤ) : residueRight r index a b vacuum = 0 := by
      unfold residueRight; apply finsum_eq_zero_of_forall_eq_zero; intro offset; rw [stateField_creation.2.2.1 a offset (by omega)]
      simp
    constructor
    · rw [(residueField s r a b).coefficient, residueCoefficient, rightZero, smul_zero, sub_zero]
      unfold residueLeft; rw [finsum_eq_single _ 0]
      · simp [integerBinomial, stateField_creation.2.1 b]
      · intro offset distinct
        rw [stateField_creation.2.2.1 b (-1 + (offset : ℤ)) (by omega)]; simp
    · intro index nonnegative
      rw [(residueField s r a b).coefficient, residueCoefficient, rightZero, smul_zero, sub_zero]; unfold residueLeft
      apply finsum_eq_zero_of_forall_eq_zero; intro offset; rw [stateField_creation.2.2.1 b (index + (offset : ℤ)) (by omega)]; simp


private theorem signed_uniqueness (operator : VertexOperator ℂ Fock)
    (sign : Finset ℕ → ℂ)
    (creativeOperator : ∀ index : ℤ, 0 ≤ index → (operator [[index]]) vacuum = 0)
    (initial : (operator [[-1]]) vacuum = 0)
    (covariant : ∀ index : ℤ,
      BcGhostVirasoro.L (-1) * (operator [[index]]) -
        (operator [[index]]) * BcGhostVirasoro.L (-1) =
          -(index : ℂ) • (operator [[index - 1]]))
    (locality : ∀ S : Finset ℕ, ∃ order : ℕ,
      delta^[order] (signedComm (sign S) operator (Y (ket S))) = 0) :
    operator = 0 := by
  classical
  have vacuumNegative (degree : ℕ) : (operator [[-(degree : ℤ) - 1]]) vacuum = 0 := by
    induction degree with
    | zero => simpa using initial
    | succ degree inductionHypothesis =>
      have law := congrArg (fun endomorphism : Module.End ℂ Fock => endomorphism vacuum) (covariant (-(degree : ℤ) - 1))
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, inductionHypothesis, stateField_translation.1, map_zero, sub_self] at law
      rw [show -(degree : ℤ) - 1 - 1 = -((degree + 1 : ℕ) : ℤ) - 1 by omega] at law
      have scalar : -((-(degree : ℤ) - 1 : ℤ) : ℂ) = (degree : ℂ) + 1 := by push_cast; ring
      rw [scalar] at law
      have nonzero : (degree : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
      exact (smul_eq_zero.mp law.symm).resolve_left nonzero
  have vacuumZero (index : ℤ) : (operator [[index]]) vacuum = 0 := by
    by_cases nonnegative : 0 ≤ index
    · exact creativeOperator index nonnegative
    · let degree := (-index - 1).toNat
      rw [show index = -(degree : ℤ) - 1 by dsimp [degree]; omega]
      exact vacuumNegative degree
  have allModes (index : ℤ) (state : Finset ℕ) : (operator [[index]]) (ket state) = 0 := by
    obtain ⟨order, killed⟩ := locality state
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] (signedComm (sign state) operator (Y (ket state))) = 0 at killed
    rw [← Module.End.pow_apply] at killed
    have coefficient := congrArg (fun distribution : ℤ → ℤ → Module.End ℂ Fock =>
        distribution (index - order) (-1) vacuum) killed
    rw [binomial, LinearMap.sum_apply] at coefficient; simp only [LinearMap.smul_apply] at coefficient
    have simplify : (∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) • signedComm (sign state) operator (Y (ket state)) (index -
      order + (order : ℤ) - offset) (-1 + offset) vacuum) = (operator [[index]]) (ket state) := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul, Nat.cast_zero, sub_zero, add_zero, show index - (order : ℤ) + order = index by omega,
        signedComm, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, vacuumZero, map_zero, smul_zero, sub_zero, stateField_creation.2.1 (ket state)]
      · intro offset member distinct
        have vanish : ((Y (ket state)) [[-1 + (offset : ℤ)]]) vacuum = 0 := stateField_creation.2.2.1 (ket state) _ (by omega)
        simp only [signedComm, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, vanish, vacuumZero, map_zero, smul_zero, sub_self]
      · simp
    rw [simplify] at coefficient; exact coefficient
  have endZero (index : ℤ) : (operator [[index]]) = 0 := by
    apply Finsupp.lhom_ext
    intro S z
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    rw [hs, map_smul, allModes, smul_zero]
    rfl
  apply HVertexOperator.coeff_inj
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, endZero]
  simp

private theorem negativeResidue (s : ℂ) (a b : Fock) (degree : ℕ) : (residueField s (-(degree : ℤ) - 1) a b).operator = (signedNormalMinusOne s (dividedDerivative degree (Y a)) (Y b)).1 := by
  have derivativeModes (index : ℤ) (vector : Fock) : ((dividedDerivative degree (Y a)) [[index]]) vector = ((Ring.choose (-index - 1 + degree) degree : ℤ) : ℂ) • ((Y a)
    [[index - degree]]) vector := by
    change Ring.choose (-index - 1 + degree) degree • HVertexOperator.coeff (Y a) (-index - 1 + degree) vector = _
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
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, (residueField s (-(degree : ℤ) - 1) a b).coefficient, (signedNormalMinusOne s (dividedDerivative degree (Y a)) (Y
    b)).2]
  let index : ℤ := -power - 1
  have firstEquality : residueLeft (-(degree : ℤ) - 1) index a b vector = ∑ᶠ offset : ℕ, ((dividedDerivative degree (Y a)) [[-(offset : ℤ) - 1]]) (((Y b) [[index + offset]])
    vector) := by
    unfold residueLeft; apply finsum_congr; intro offset; rw [weight, derivativeModes]
    have parameter : -(-(offset : ℤ) - 1) - 1 + degree = ((degree + offset : ℕ) : ℤ) := by omega
    rw [parameter, Ring.choose_natCast]; rw [show -(degree : ℤ) - 1 - offset = -(offset : ℤ) - 1 - degree by omega]
    simp only [Int.cast_natCast]
  let term (offset : ℕ) : Fock := ((Y b) [[index - offset - 1]]) (((dividedDerivative degree (Y a)) [[offset]]) vector)
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
  have secondEquality : (∑ᶠ offset : ℕ, term offset) = (-1 : ℂ) ^ degree • residueRight (-(degree : ℤ) - 1) index a b vector := by
    rw [split, residueRight, smul_finsum' _ ((residueField s (-(degree : ℤ) - 1) a b).right_finite index vector)]; apply finsum_congr
    intro offset; dsimp [term]; rw [derivativeModes, map_smul, weight]
    rw [show -((degree : ℤ) + offset) - 1 + degree = -(offset : ℤ) - 1 by omega, show -(offset : ℤ) - 1 = -((offset : ℤ) + 1) by omega, Ring.choose_neg, show (offset : ℤ) + 1
      + degree - 1 = ((degree + offset : ℕ) : ℤ) by omega, Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast, Int.cast_natCast, smul_smul]
    rw [show (degree : ℤ) + offset - degree = offset by omega, show index - ((degree : ℤ) + offset) - 1 = -(degree : ℤ) - 1 + index - offset by omega]
  change residueCoefficient s (-(degree : ℤ) - 1) index a b vector = _
  rw [residueCoefficient, firstEquality]
  change _ - (epsilon (-(degree : ℤ) - 1) * s) • residueRight (-(degree : ℤ) - 1) index a b vector = _ + s • (∑ᶠ offset : ℕ, term offset)
  rw [secondEquality, sub_eq_add_neg, ← neg_smul, ← neg_mul, sign, mul_smul,
      smul_comm ((-1 : ℂ) ^ degree) s]

private theorem positiveLocality (x y z : ℂ) (a b c : Fock) (r Na Nb Nc : ℕ)
    (hAC : delta^[Na] (signedComm y (Y a) (Y c)) = 0)
    (hBC : delta^[Nb] (signedComm z (Y b) (Y c)) = 0)
    (hAB : delta^[Nc] (signedComm x (Y a) (Y b)) = 0) :
    delta^[Na + Nb + Nc]
      (signedComm (y * z) (residueField x r a b).operator (Y c)) = 0 := by
  funext l k
  apply LinearMap.ext
  intro v
  let pair := signedTriple x y z (Y a) (Y b) (Y c) v
  let shifted := ((deltaXY ^ (r + 1) : Module.End ℂ (PairSpace Fock))) pair
  have commute : Commute (deltaXY (V := Fock))
      ((deltaXY + deltaYZ) ^ Na * deltaYZ ^ Nb) :=
    (((Commute.refl deltaXY).add_right shiftsCommute).pow_right Na).mul_right
      (shiftsCommute.pow_right Nb)
  have low : (((deltaXY + deltaYZ) ^ Na * deltaYZ ^ Nb : Module.End ℂ (PairSpace Fock)))
      shifted = 0 := by
    dsimp only [shifted, pair]
    rw [← Module.End.mul_apply, (commute.pow_left (r + 1)).symm.eq,
      Module.End.mul_apply, signedPair_low x y z (Y a) (Y b) (Y c) v Na Nb hAC hBC,
      map_zero]
  have high : discrepancy ((deltaXY ^ Nc) shifted) = 0 := by
    dsimp only [shifted, pair]
    rw [← Module.End.mul_apply, (Commute.refl deltaXY).pow_pow Nc (r + 1) |>.eq,
      Module.End.mul_apply, intertwiningPowers (deltaXY (V := Fock)) (plainXY (V := Fock))
        (discrepancy (V := Fock)) discrepancyXY (r + 1),
      signedPair_high x y z (Y a) (Y b) (Y c) v Nc hAB, map_zero]
  have cancelled := cancellationBound shifted Na Nb Nc low high
  let lifting := liftAB (Y c) v true - (y * z) • liftAB (Y c) v false
  have difference : discrepancy pair = lifting (signedComm x (Y a) (Y b)) := by
    funext i j k
    change (signedTriple x y z (Y a) (Y b) (Y c) v).val.1 i j k -
      (signedTriple x y z (Y a) (Y b) (Y c) v).val.2 i j k = _
    rw [(signedTriple_coefficients x y z (Y a) (Y b) (Y c) v i j k).1,
      (signedTriple_coefficients x y z (Y a) (Y b) (Y c) v i j k).2]
    simp only [lifting, liftAB, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, if_true, Bool.false_eq_true, if_false,
      signedComm, Module.End.mul_apply, map_sub, map_smul, smul_smul,
      Pi.sub_apply, Pi.smul_apply]
    module
  have liftingLaw (D : ℤ → ℤ → Module.End ℂ Fock) :
      lifting (deltaEnd D) = plainXY (lifting D) := by
    funext i j k
    dsimp [lifting, liftAB, deltaEnd, delta, plainXY, shiftXY]
    simp only [map_sub]
    module
  have connection : res shifted = evaluate v
      (signedComm (y * z) (residueField x r a b).operator (Y c)) := by
    funext j k
    dsimp only [shifted]
    rw [pow_succ', Module.End.mul_apply]
    change residue (shiftXY ((deltaXY ^ r) pair).val.1)
      (shiftXY ((deltaXY ^ r) pair).val.2) j k = _
    rw [residueXY _ _ ((deltaXY ^ r) pair).property.1 ((deltaXY ^ r) pair).property.2]
    change discrepancy ((deltaXY ^ r) pair) 0 j k = _
    rw [intertwiningPowers (deltaXY (V := Fock)) (plainXY (V := Fock))
        (discrepancy (V := Fock)) discrepancyXY r pair, difference,
      ← intertwiningPowers (deltaEnd (V := Fock)) (plainXY (V := Fock))
        lifting liftingLaw r (signedComm x (Y a) (Y b))]
    dsimp only [lifting, liftAB, evaluate, signedComm]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, if_true, Bool.false_eq_true, if_false, Pi.sub_apply,
      Pi.smul_apply, Module.End.mul_apply]
    rw [← positiveModes x a b r j (((Y c) [[k]]) v), ← positiveModes x a b r j v]
    simp only [signedComm, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.mul_apply]
  change delta^[Na + Nb + Nc] (res shifted) = 0 at cancelled
  rw [connection] at cancelled
  have evaluationLaw (D : ℤ → ℤ → Module.End ℂ Fock) :
      evaluate v (deltaEnd D) = plainDelta (evaluate v D) := rfl
  have transport := intertwiningPowers deltaEnd plainDelta (evaluate v) evaluationLaw
    (Na + Nb + Nc) (signedComm (y * z) (residueField x r a b).operator (Y c))
  rw [Module.End.pow_apply, Module.End.pow_apply] at transport
  change evaluate v (delta^[Na + Nb + Nc]
    (signedComm (y * z) (residueField x r a b).operator (Y c))) =
      delta^[Na + Nb + Nc] (evaluate v
        (signedComm (y * z) (residueField x r a b).operator (Y c))) at transport
  rw [cancelled] at transport
  exact congrFun (congrFun transport l) k

private theorem residueLocality (a b c : Fock) (p q t : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hb : parity b = (-1 : ℂ) ^ q • b)
    (hc : parity c = (-1 : ℂ) ^ t • c) (r : ℤ) :
    ∃ N, delta^[N] (signedComm ((-1 : ℂ) ^ ((p + q) * t))
      (residueField ((-1 : ℂ) ^ (p * q)) r a b).operator (Y c)) = 0 := by
  obtain ⟨Na, hAC⟩ := stateField_locality a c p t ha hc
  obtain ⟨Nb, hBC⟩ := stateField_locality b c q t hb hc
  obtain ⟨Nc, hAB⟩ := stateField_locality a b p q ha hb
  change delta^[Na] (signedComm ((-1 : ℂ) ^ (p * t)) (Y a) (Y c)) = 0 at hAC
  change delta^[Nb] (signedComm ((-1 : ℂ) ^ (q * t)) (Y b) (Y c)) = 0 at hBC
  change delta^[Nc] (signedComm ((-1 : ℂ) ^ (p * q)) (Y a) (Y b)) = 0 at hAB
  have sign : ((-1 : ℂ) ^ (p * t)) * ((-1 : ℂ) ^ (q * t)) =
      (-1 : ℂ) ^ ((p + q) * t) := by rw [← pow_add, Nat.add_mul]
  by_cases nonnegative : 0 ≤ r
  · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
    refine ⟨Na + Nb + Nc, ?_⟩
    rw [← sign]
    exact positiveLocality _ _ _ a b c degree Na Nb Nc hAC hBC hAB
  · let degree := (-r - 1).toNat
    have hr : r = -(degree : ℤ) - 1 := by dsimp [degree]; omega
    rw [hr, negativeResidue]
    refine ⟨Na + degree + Nb + (Nc + degree), ?_⟩
    rw [← sign]
    exact signedNormal_locality _ _ _ _ _ _ (Na + degree) Nb (Nc + degree)
      (signedDerivative_locality _ (Y a) (Y c) Na degree hAC) hBC
      (signedDerivative_locality _ (Y a) (Y b) Nc degree hAB)
private theorem residueClosure (a b : Fock) (p q : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hb : parity b = (-1 : ℂ) ^ q • b) (r : ℤ) :
    Y (((Y a) [[r]]) b) = (residueField ((-1 : ℂ) ^ (p * q)) r a b).operator := by
  classical
  let field := (residueField ((-1 : ℂ) ^ (p * q)) r a b).operator
  let product := ((Y a) [[r]]) b
  let difference := field - Y product
  have productParity : parity product = (-1 : ℂ) ^ (p + q) • product := by
    have law := LinearMap.congr_fun (stateField_parity a r) b
    simp only [Module.End.mul_apply] at law
    rw [ha, hb, map_smul, map_smul] at law
    simp only [Pi.smul_apply, LinearMap.smul_apply, map_smul, smul_smul] at law
    simpa only [product, pow_add, mul_comm] using law
  have creativeDifference : ∀ index : ℤ, 0 ≤ index → (difference [[index]]) vacuum = 0 := by
    intro index nonnegative
    simp only [difference, field, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      (residue_creation _ r a b).2 index nonnegative,
      stateField_creation.2.2.1 product index nonnegative, sub_self]
  have initial : (difference [[-1]]) vacuum = 0 := by
    simp only [difference, field, product, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      (residue_creation _ r a b).1, stateField_creation.2.1, sub_self]
  have covariance (index : ℤ) :
      BcGhostVirasoro.L (-1) * (difference [[index]]) -
        (difference [[index]]) * BcGhostVirasoro.L (-1) =
          -(index : ℂ) • (difference [[index - 1]]) := by
    simp only [difference, map_sub, Pi.sub_apply]
    calc
      _ = (BcGhostVirasoro.L (-1) * (field [[index]]) -
          (field [[index]]) * BcGhostVirasoro.L (-1)) -
        (BcGhostVirasoro.L (-1) * ((Y product) [[index]]) -
          ((Y product) [[index]]) * BcGhostVirasoro.L (-1)) := by
          simp only [mul_sub, sub_mul]
          abel
      _ = _ := by rw [residue_translation, stateField_translation.2]; module
  have crossLocality (S : Finset ℕ) : ∃ N, delta^[N]
      (signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) difference (Y (ket S))) = 0 := by
    obtain ⟨M, hM⟩ := residueLocality a b (ket S) p q S.card ha hb (parity_ket S) r
    obtain ⟨N, hN⟩ := stateField_locality product (ket S) (p + q) S.card
      productParity (parity_ket S)
    let degree := max M N
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[M]
      (signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) field (Y (ket S))) = 0 at hM
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[N]
      (signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) (Y product) (Y (ket S))) = 0 at hN
    rw [← Module.End.pow_apply] at hM hN
    have firstHigh := Module.End.pow_map_zero_of_le (le_max_left M N) hM
    have secondHigh := Module.End.pow_map_zero_of_le (le_max_right M N) hN
    have split : signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) difference (Y (ket S)) =
        signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) field (Y (ket S)) -
          signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) (Y product) (Y (ket S)) := by
      funext i j
      simp only [signedComm, difference, map_sub, Pi.sub_apply, mul_sub, sub_mul,
        smul_sub]
      abel
    refine ⟨degree, ?_⟩
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[degree] _ = 0
    rw [← Module.End.pow_apply, split, map_sub, firstHigh, secondHigh, sub_self]
  have vanished := signed_uniqueness difference (fun S => (-1 : ℂ) ^ ((p + q) * S.card))
    creativeDifference initial covariance crossLocality
  exact (sub_eq_zero.mp vanished).symm

/-- The full signed all-integer iterate identity on the original ghost carrier,
including genuine finite support for both coefficient sums. -/
theorem stateField_iterate (a b c : Fock) (p q : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hb : parity b = (-1 : ℂ) ^ q • b) (r n : ℤ) :
    let left : ℕ → Fock := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y a) [[r - (i : ℤ)]]) (((Y b) [[n + (i : ℤ)]]) c))
    let right : ℕ → Fock := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y b) [[r + n - (i : ℤ)]]) (((Y a) [[(i : ℤ)]]) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right ∧
      (((Y (((Y a) [[r]]) b)) [[n]]) c) =
        (∑ᶠ i : ℕ, left i) -
          (((-1 : ℂ) ^ r) * ((-1 : ℂ) ^ (p * q))) • (∑ᶠ i : ℕ, right i) := by
  dsimp
  let field := residueField ((-1 : ℂ) ^ (p * q)) r a b
  refine ⟨field.left_finite n c, field.right_finite n c, ?_⟩
  rw [residueClosure a b p q ha hb r, field.coefficient]
  rfl

end D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
