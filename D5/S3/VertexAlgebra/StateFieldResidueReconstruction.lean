/- GID: D5/S3/VertexAlgebra/StateFieldResidueReconstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/StateFieldResidueReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer residue closure and the finite iterate identity for unrestricted state fields. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Scott Carnahan
Modified source: the two finite-support kernels from
ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea,
VertexAlg/VertexBasic/VertexOperator.lean, are used inside the residue constructor.
The coefficient representation and finite-intermediate-state truncation use the
existing pinned VertexOperator interface, without the upstream lexicographic backend.
proof_shape: residue_nonnegative_locality, relative_vacuum_uniqueness,
residue_closure, stateField_iterate_of_creation_translation_locality: content
escape_witness: The double commutator is annihilated by the first pair's
locality polynomial and by the product of the other two locality polynomials.
Expansion in the commuting coefficient shifts kills every finite summand,
giving a vector-independent locality order for the actual nonnegative residue.
Vacuum covariance and coefficient extraction prove relative uniqueness, without
an image-of-Y premise. Creative vacuum uniqueness identifies all-integer residue closure,
and direct coefficient extraction gives the finite Ring.choose iterate identity.
admission_basis: escape-witness
-/

import D5.S3.VertexAlgebra.FieldNormalProductLocality

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.StateFieldResidueReconstruction

open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open scoped VertexOperator

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {Y : V →ₗ[ℂ] VertexOperator ℂ V}

noncomputable def mu (a : V) (index : ℤ) (b : V) : V := ((Y a) [[index]]) b

noncomputable def integerBinomial (index : ℤ) (offset : ℕ) : ℂ := ((Ring.choose index offset : ℤ) : ℂ)

noncomputable def epsilon (index : ℤ) : ℂ := (-1 : ℂ) ^ index

noncomputable def residueLeft (r n : ℤ) (a b vector : V) : V :=
  ∑ᶠ offset : ℕ, (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y a) [[r - offset]]) (((Y b) [[n + offset]])
    vector)

noncomputable def residueRight (r n : ℤ) (a b vector : V) : V :=
  ∑ᶠ offset : ℕ, (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y b) [[r + n - offset]]) (((Y a) [[offset]])
    vector)

noncomputable def residueCoefficient (r n : ℤ) (a b vector : V) : V :=
  residueLeft (Y := Y) r n a b vector - epsilon r • residueRight (Y := Y) r n a b vector

structure ResidueField (r : ℤ) (a b : V) where
  operator : VertexOperator ℂ V
  coefficient : ∀ n vector, (operator [[n]]) vector = residueCoefficient (Y := Y) r n a b vector
  left_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y a) [[r - offset]]) (((Y b) [[n + offset]]) vector))
  right_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y b) [[r + n - offset]]) (((Y a) [[offset]]) vector))

theorem deltaEnd_iterate_apply (value : ℤ → ℤ → Module.End ℂ V) (order : ℕ)
    (first second : ℤ) :
    ((deltaEnd ^ order) value) first second = (delta^[order] value) first second := by
  induction order generalizing first second with
  | zero => rfl
  | succ order ih =>
      rw [pow_succ', Module.End.mul_apply]
      change ((deltaEnd ^ order) value) (first + 1) second -
        ((deltaEnd ^ order) value) first (second + 1) = _
      rw [ih, ih]
      change delta (delta^[order] value) first second = delta^[order + 1] value first second
      rw [← Function.iterate_succ_apply' delta order value, Function.iterate_succ_apply]

noncomputable def residueField (r : ℤ) (a b : V) : ResidueField (Y := Y) r a b := by
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
      (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y a) [[r - offset]]) (((Y b) [[n + offset]]) vector)) := by
    have finite := leftKernel (-n - 1) r (Y a) (Y b) vector
    simpa only [Function.HasFiniteSupport, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_smul, integerBinomial, show -(-n - 1) - 1 = n by omega]
      using finite
  have rightFinite (n : ℤ) (vector : V) : Function.HasFiniteSupport (fun offset : ℕ =>
      (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y b) [[r + n - offset]]) (((Y a) [[offset]]) vector)) := by
    have finite := rightKernel (-n - 1) r (Y a) (Y b) vector
    simpa only [Function.HasFiniteSupport, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_smul, integerBinomial, show -(-n - 1) - 1 = n by omega]
      using finite
  let coefficient (n : ℤ) : Module.End ℂ V := {
    toFun := residueCoefficient (Y := Y) r n a b
    map_add' first second := by
      dsimp [residueCoefficient, residueLeft, residueRight]; simp only [map_add, smul_add]
      rw [finsum_add_distrib (leftFinite n first) (leftFinite n second), finsum_add_distrib (rightFinite n first) (rightFinite n second)]
      module
    map_smul' scalar vector := by
      dsimp [residueCoefficient, residueLeft, residueRight]; simp only [map_smul]; simp_rw [smul_comm _ scalar]
      rw [← smul_finsum' scalar (leftFinite n vector), ← smul_finsum' scalar (rightFinite n vector)]
      rw [smul_comm (epsilon r) scalar, ← smul_sub] }
  have bounded (vector : V) : BddBelow (Function.support (fun power : ℤ => coefficient (-power - 1) vector)) := by
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

theorem residue_nonnegative_locality
    (localityHyp : ∀ a b : V, ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator (Y a) (Y b)) = 0)
    (a b c : V) (r : ℕ) : ∃ order : ℕ, delta^[order] (FieldNormalProductLocality.commutator (residueField (Y := Y) r a b).operator (Y c)) = 0 := by
  classical
  let shiftLeft : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun first second => value (first + 1) second
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun first second => value first (second + 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have binomial (value : ℤ → ℤ → Module.End ℂ V) (order : ℕ) (first second : ℤ) : ((deltaEnd ^ order) value) first second = ∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^
    offset) * (order.choose offset : ℂ)) • value (first + (order : ℤ) - offset) (second + offset) := by
    have commute : Commute (-shiftRight) shiftLeft := by apply LinearMap.ext; intro distribution; funext left right; simp [shiftLeft, shiftRight]
    have leftPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : (shiftLeft ^ degree) distribution = fun left right => distribution (left + degree) right := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
        change distribution (left + 1 + degree) right = distribution (left + (degree + 1 : ℕ)) right; congr 1; push_cast; omega
    have rightPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : ((-shiftRight) ^ degree) distribution = fun left right => ((-1 : ℂ) ^ degree) • distribution left
      (right + degree) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
        change -(((-1 : ℂ) ^ degree) • distribution left (right + 1 + degree)) = ((-1 : ℂ) ^ (degree + 1)) • distribution left (right + (degree + 1 : ℕ))
        rw [pow_succ', mul_smul, neg_one_smul]
        have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by push_cast; omega
        rw [indices]
    have equation : (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V)) = -shiftRight + shiftLeft := by
      apply LinearMap.ext; intro distribution; funext left right; simp [deltaEnd, delta, shiftLeft, shiftRight]
      abel
    rw [equation, commute.add_pow, LinearMap.sum_apply]; simp only [Finset.sum_apply]; apply Finset.sum_congr rfl; intro offset member
    have within : offset ≤ order := by simpa using Finset.mem_range.mp member
    simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, rightPower, leftPower, Pi.smul_apply]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]; congr 2; push_cast [Int.natCast_sub within]; omega
  have positiveModes (n : ℤ) (vector : V) : (((residueField (Y := Y) r a b).operator) [[n]]) vector = ((deltaEnd ^ r) (FieldNormalProductLocality.commutator (Y a) (Y b))) 0 n vector :=
    by
    have chooseNat (offset : ℕ) : integerBinomial r offset = (r.choose offset : ℂ) := by simp [integerBinomial, Ring.choose_natCast]
    have leftSum : residueLeft (Y := Y) r n a b vector = ∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • ((Y a) [[(r : ℤ) - offset]]) (((Y b) [[n +
      offset]]) vector) := by
      unfold residueLeft; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
      by_contra outside
      have zeroChoose : r.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
      exact member (by simp [zeroChoose])
    have rightSum : residueRight (Y := Y) r n a b vector = ∑ offset ∈ Finset.range (r + 1), (((-1 : ℂ) ^ offset) * (r.choose offset : ℂ)) • ((Y b) [[(r : ℤ) + n - offset]]) (((Y a)
      [[offset]]) vector) := by
      unfold residueRight; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
      by_contra outside
      have zeroChoose : r.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
      exact member (by simp [zeroChoose])
    rw [(residueField (Y := Y) r a b).coefficient, residueCoefficient, leftSum, rightSum, binomial, LinearMap.sum_apply]
    simp only [zero_add, LinearMap.smul_apply, FieldNormalProductLocality.commutator, Module.End.mul_apply, LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib]
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
    rw [signs]; push_cast [Int.natCast_sub within]; rw [show (r : ℤ) + n - ((r : ℤ) - offset) = n + offset by omega]
  have locality (first second : V) : ∃ order : ℕ, (deltaEnd ^ order) (FieldNormalProductLocality.commutator (Y first) (Y second)) = 0 := by
    obtain ⟨order, law⟩ := localityHyp first second
    have law' : (deltaEnd ^ order) (FieldNormalProductLocality.commutator (Y first) (Y second)) = 0 := by
      funext left right
      rw [deltaEnd_iterate_apply]
      exact congrFun (congrFun law left) right
    refine ⟨order, ?_⟩
    funext left right
    rw [binomial]
    have lawPoint := congrFun (congrFun law' left) right
    rw [binomial] at lawPoint
    exact lawPoint
  obtain ⟨firstOrder, firstKilled⟩ := locality a c; obtain ⟨secondOrder, secondKilled⟩ := locality b c
  obtain ⟨thirdOrder, thirdKilled⟩ := locality a b
  let order := if thirdOrder ≤ r then 0 else firstOrder + thirdOrder - r - 1 + secondOrder
  have cancellation (vector : V) : ((plainYZ ^ order * plainXY ^ r : Module.End ℂ (Triple V)) (fun left middle right =>
          FieldNormalProductLocality.commutator (Y a) (Y b) left middle (((Y c) [[right]]) vector) - ((Y c) [[right]]) (FieldNormalProductLocality.commutator (Y a) (Y b) left
            middle vector))) = 0 := by
    dsimp only [order]
    let first : Module.End ℂ (Triple V) := plainXY
    let second : Module.End ℂ (Triple V) := plainYZ
    let combined := first + second
    have commuting : Commute first second := by
      apply LinearMap.ext; intro distribution; funext left middle right; dsimp [first, second, plainXY, plainYZ, shiftXY, shiftYZ]
      abel
    have combinedFirst : Commute combined first := (Commute.refl first).add_left commuting.symm
    have combinedSecond : Commute combined second := commuting.add_left (Commute.refl second)
    have intertwiningPowersOT
        (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))
        (target : Module.End ℂ (Triple V))
        (linear : (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] Triple V)
        (law : ∀ value, linear (source value) = target (linear value))
        (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ V) :
        linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        simp only [pow_succ', Module.End.mul_apply]
        rw [law, inductionHypothesis]
    have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : liftAB (Y c) vector side (deltaEnd distribution) = first (liftAB (Y c) vector side distribution) := by
      funext left middle right; dsimp [liftAB, deltaEnd, delta, first, plainXY, shiftXY]
      cases side <;> simp [map_sub]
    have lawAC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : liftAC (Y b) vector side (deltaEnd distribution) = combined (liftAC (Y b) vector side distribution) := by
      funext left middle right; dsimp [liftAC, deltaEnd, delta, combined, first, second, plainXY, plainYZ, shiftXY, shiftYZ]
      cases side <;> simp [map_sub]
    have lawBC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : liftBC (Y a) vector side (deltaEnd distribution) = second (liftBC (Y a) vector side distribution) := by
      funext left middle right; dsimp [liftBC, deltaEnd, delta, second, plainYZ, shiftYZ]
      cases side <;> simp [map_sub]
    let discrepancy := liftAB (Y c) vector true (FieldNormalProductLocality.commutator (Y a) (Y b)) - liftAB (Y c) vector false (FieldNormalProductLocality.commutator (Y a) (Y b))
    let firstPart := liftAC (Y b) vector true (FieldNormalProductLocality.commutator (Y a) (Y c)) - liftAC (Y b) vector false (FieldNormalProductLocality.commutator (Y a) (Y c))
    let secondPart := liftBC (Y a) vector true (FieldNormalProductLocality.commutator (Y b) (Y c)) - liftBC (Y a) vector false (FieldNormalProductLocality.commutator (Y b) (Y c))
    have jacobi : discrepancy = firstPart + secondPart := by
      funext left middle right; dsimp [discrepancy, firstPart, secondPart, liftAB, liftAC, liftBC, FieldNormalProductLocality.commutator]
      simp only [map_sub]; abel
    have discrepancyKilled : (first ^ thirdOrder) discrepancy = 0 := by
      dsimp [discrepancy]
      rw [map_sub, ← intertwiningPowersOT deltaEnd first (liftAB (Y c) vector true) (lawAB true), ← intertwiningPowersOT deltaEnd first (liftAB (Y c) vector false) (lawAB false), thirdKilled]
      simp
    have firstPartKilled : (combined ^ firstOrder) firstPart = 0 := by
      dsimp [firstPart]
      rw [map_sub, ← intertwiningPowersOT deltaEnd combined (liftAC (Y b) vector true) (lawAC true), ← intertwiningPowersOT deltaEnd combined (liftAC (Y b) vector false) (lawAC false), firstKilled]
      simp
    have secondPartKilled : (second ^ secondOrder) secondPart = 0 := by
      dsimp [secondPart]
      rw [map_sub, ← intertwiningPowersOT deltaEnd second (liftBC (Y a) vector true) (lawBC true), ← intertwiningPowersOT deltaEnd second (liftBC (Y a) vector false) (lawBC false), secondKilled]
      simp
    have annihilated : (combined ^ firstOrder * second ^ secondOrder) discrepancy = 0 := by
      rw [jacobi, map_add]
      have firstVanish : (combined ^ firstOrder * second ^ secondOrder) firstPart = 0 := by rw [(combinedSecond.pow_pow _ _).eq, Module.End.mul_apply, firstPartKilled, map_zero]
      have secondVanish : (combined ^ firstOrder * second ^ secondOrder) secondPart = 0 := by rw [Module.End.mul_apply, secondPartKilled, map_zero]
      rw [firstVanish, secondVanish, add_zero]
    have high (power : ℕ) (large : thirdOrder ≤ power) : (first ^ power) discrepancy = 0 := by
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le large
      rw [pow_add, (Commute.refl first).pow_pow _ _ |>.eq, Module.End.mul_apply, discrepancyKilled, map_zero]
    by_cases large : thirdOrder ≤ r
    · simp only [if_pos large]
      change (second ^ 0 * first ^ r) discrepancy = 0; simp [high r large]
    · let exponent := firstOrder + thirdOrder - r - 1
      simp only [if_neg large]; change (second ^ (exponent + secondOrder) * first ^ r) discrepancy = 0
      have low (degree : ℕ) (largeDegree : firstOrder ≤ degree) : (combined ^ degree * second ^ secondOrder) discrepancy = 0 := by
        obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le largeDegree
        rw [pow_add, (Commute.refl combined).pow_pow _ _ |>.eq, mul_assoc, Module.End.mul_apply, annihilated, map_zero]
      have minusCommute : Commute combined (-first) := by
        apply LinearMap.ext; intro value
        have law := congrArg (fun operator : Module.End ℂ (Triple V) => operator value) combinedFirst.eq
        simpa only [Module.End.mul_apply, LinearMap.neg_apply, map_neg] using congrArg Neg.neg law
      have expansion := minusCommute.add_pow exponent
      have sumEquality : second ^ exponent = ∑ degree ∈ Finset.range (exponent + 1), combined ^ degree * (-first) ^ (exponent - degree) * exponent.choose degree := by
        have difference : combined + -first = second := by dsimp [combined]; abel
        rw [difference] at expansion; exact expansion
      rw [pow_add, sumEquality, Finset.sum_mul, Finset.sum_mul, LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro degree member
      have sign (power : ℕ) : (-first) ^ power = ((-1 : ℂ) ^ power) • first ^ power := by
        induction power with
        | zero => simp
        | succ power inductionHypothesis =>
          rw [pow_succ', inductionHypothesis, pow_succ']; apply LinearMap.ext; intro value
          simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply, mul_smul, neg_one_smul, map_smul, pow_succ', smul_neg]
      rw [sign, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, LinearMap.smul_apply]
      simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
      by_cases largeDegree : firstOrder ≤ degree
      · have vanish : (combined ^ degree) ((first ^ (exponent - degree)) ((second ^ secondOrder) ((first ^ r) discrepancy))) = 0 := by
          change (combined ^ degree * first ^ (exponent - degree) * second ^ secondOrder * first ^ r) discrepancy = 0
          rw [(combinedFirst.pow_pow degree (exponent - degree)).eq]
          have move := (combinedFirst.pow_pow degree r).mul_left (commuting.symm.pow_pow secondOrder r)
          have reorder : first ^ (exponent - degree) * combined ^ degree * second ^ secondOrder * first ^ r = first ^ (exponent - degree) * first ^ r * (combined ^ degree * second
            ^ secondOrder) := by
            calc
              _ = first ^ (exponent - degree) * ((combined ^ degree * second ^ secondOrder) * first ^ r) := by simp only [mul_assoc]
              _ = _ := by rw [move.eq]; simp only [mul_assoc]
          rw [reorder, Module.End.mul_apply, low degree largeDegree, map_zero]
        simp [vanish]
      · have bound : thirdOrder ≤ exponent - degree + r := by
          have within : degree ≤ exponent := by simpa using Finset.mem_range.mp member
          dsimp [exponent]; omega
        have vanish : (first ^ (exponent - degree)) ((second ^ secondOrder) ((first ^ r) discrepancy)) = 0 := by
          change (first ^ (exponent - degree) * second ^ secondOrder * first ^ r) discrepancy = 0
          rw [(commuting.pow_pow _ _).eq, mul_assoc, ← pow_add, Module.End.mul_apply, high _ bound, map_zero]
        simp [vanish]
  refine ⟨order, ?_⟩; funext left right; apply LinearMap.ext; intro vector
  let extract : Triple V →ₗ[ℂ] (ℤ → ℤ → V) := {
    toFun distribution := distribution 0
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have intertwiningPowersTV
      (source : Module.End ℂ (Triple V))
      (target : Module.End ℂ (ℤ → ℤ → V))
      (linear : Triple V →ₗ[ℂ] (ℤ → ℤ → V))
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : Triple V) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  have intertwiningPowersEV
      (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))
      (target : Module.End ℂ (ℤ → ℤ → V))
      (linear : (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] (ℤ → ℤ → V))
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ V) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  have extractLaw (distribution : Triple V) : extract (plainYZ distribution) = plainDelta (extract distribution) := by rfl
  have evaluateLaw (distribution : ℤ → ℤ → Module.End ℂ V) : evaluate vector (deltaEnd distribution) = plainDelta (evaluate vector distribution) := by rfl
  have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : liftAB (Y c) vector side (deltaEnd distribution) = plainXY (liftAB (Y c) vector side distribution) := by
    funext first middle third; dsimp [liftAB, deltaEnd, delta, plainXY, shiftXY]
    cases side <;> simp [map_sub]
  have intertwiningPowersOT
      (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))
      (target : Module.End ℂ (Triple V))
      (linear : (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] Triple V)
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ V) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  let discrepancy := liftAB (Y c) vector true (FieldNormalProductLocality.commutator (Y a) (Y b)) - liftAB (Y c) vector false (FieldNormalProductLocality.commutator (Y a) (Y b))
  have connection : extract ((plainXY ^ r) discrepancy) = evaluate vector (FieldNormalProductLocality.commutator (residueField (Y := Y) r a b).operator (Y c)) := by
    dsimp only [discrepancy]
    rw [map_sub, map_sub, ← intertwiningPowersOT deltaEnd plainXY (liftAB (Y c) vector true) (lawAB true), ← intertwiningPowersOT deltaEnd plainXY (liftAB (Y c) vector false) (lawAB
      false)]
    funext first second; dsimp [extract, liftAB, evaluate, FieldNormalProductLocality.commutator]
    rw [← positiveModes first (((Y c) [[second]]) vector), ← positiveModes first vector]
  have killed := congrArg (fun distribution : Triple V => extract distribution) (cancellation vector)
  change extract ((plainYZ ^ order) ((plainXY ^ r) discrepancy)) = extract 0 at killed
  rw [intertwiningPowersTV plainYZ plainDelta extract extractLaw, connection, ← intertwiningPowersEV deltaEnd plainDelta (evaluate vector) evaluateLaw, map_zero] at killed
  have coefficient := congrFun (congrFun killed left) right
  change ((deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] (FieldNormalProductLocality.commutator (residueField (Y := Y) r a b).operator (Y c))) left right vector = 0
  rw [← Module.End.pow_apply]; exact coefficient

theorem relative_vacuum_uniqueness
    (vacuum : V) (T : Module.End ℂ V) (translation_vacuum : T vacuum = 0)
    (creation : ∀ state : V, ((Y state) [[-1]]) vacuum = state)
    (creativeField : ∀ (state : V) (index : ℤ), 0 ≤ index → ((Y state) [[index]]) vacuum = 0)
    (operator : VertexOperator ℂ V)
    (creativeOperator : ∀ index : ℤ, 0 ≤ index → (operator [[index]]) vacuum = 0)
    (initial : (operator [[-1]]) vacuum = 0)
    (covariant : ∀ index : ℤ, T * (operator [[index]]) - (operator [[index]]) * T =
      -(index : ℂ) • (operator [[index - 1]]))
    (locality : ∀ state : V, ∃ order : ℕ,
      delta^[order] (FieldNormalProductLocality.commutator operator (Y state)) = 0) :
    operator = 0 := by
  classical
  let shiftLeft : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun first second => value (first + 1) second
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun first second => value first (second + 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have binomial (value : ℤ → ℤ → Module.End ℂ V) (order : ℕ) (first second : ℤ) : ((deltaEnd ^ order) value) first second = ∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^
    offset) * (order.choose offset : ℂ)) • value (first + (order : ℤ) - offset) (second + offset) := by
    have commute : Commute (-shiftRight) shiftLeft := by apply LinearMap.ext; intro distribution; funext left right; simp [shiftLeft, shiftRight]
    have leftPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : (shiftLeft ^ degree) distribution = fun left right => distribution (left + degree) right := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
        change distribution (left + 1 + degree) right = distribution (left + (degree + 1 : ℕ)) right; congr 1; push_cast; omega
    have rightPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : ((-shiftRight) ^ degree) distribution = fun left right => ((-1 : ℂ) ^ degree) • distribution left
      (right + degree) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
        change -(((-1 : ℂ) ^ degree) • distribution left (right + 1 + degree)) = ((-1 : ℂ) ^ (degree + 1)) • distribution left (right + (degree + 1 : ℕ))
        rw [pow_succ', mul_smul, neg_one_smul]
        have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by push_cast; omega
        rw [indices]
    have equation : (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V)) = -shiftRight + shiftLeft := by
      apply LinearMap.ext; intro distribution; funext left right; simp [deltaEnd, delta, shiftLeft, shiftRight]
      abel
    rw [equation, commute.add_pow, LinearMap.sum_apply]; simp only [Finset.sum_apply]; apply Finset.sum_congr rfl; intro offset member
    have within : offset ≤ order := by simpa using Finset.mem_range.mp member
    simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, rightPower, leftPower, Pi.smul_apply]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]; congr 2; push_cast [Int.natCast_sub within]; omega
  have vacuumNegative (degree : ℕ) : (operator [[-(degree : ℤ) - 1]]) vacuum = 0 := by
    induction degree with
    | zero => simpa using initial
    | succ degree inductionHypothesis =>
      have law := congrArg (fun endomorphism : Module.End ℂ V => endomorphism vacuum) (covariant (-(degree : ℤ) - 1))
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, inductionHypothesis, translation_vacuum, map_zero, sub_self] at law
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
  have allModes (index : ℤ) (state : V) : (operator [[index]]) state = 0 := by
    obtain ⟨order, killed⟩ := locality state
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] (FieldNormalProductLocality.commutator operator (Y state)) = 0 at killed
    rw [← Module.End.pow_apply] at killed
    have coefficient := congrArg (fun distribution : ℤ → ℤ → Module.End ℂ V =>
        distribution (index - order) (-1) vacuum) killed
    rw [binomial, LinearMap.sum_apply] at coefficient; simp only [LinearMap.smul_apply] at coefficient
    have simplify : (∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) • FieldNormalProductLocality.commutator operator (Y state) (index -
      order + (order : ℤ) - offset) (-1 + offset) vacuum) = (operator [[index]]) state := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul, Nat.cast_zero, sub_zero, add_zero, show index - (order : ℤ) + order = index by omega,
        FieldNormalProductLocality.commutator, LinearMap.sub_apply, Module.End.mul_apply, vacuumZero, map_zero, sub_zero, creation state]
      · intro offset member distinct
        have vanish : ((Y state) [[-1 + (offset : ℤ)]]) vacuum = 0 := creativeField state _ (by omega)
        simp only [FieldNormalProductLocality.commutator, LinearMap.sub_apply, Module.End.mul_apply, vanish, vacuumZero, map_zero, sub_self, smul_zero]
      · simp
    rw [simplify] at coefficient; exact coefficient
  apply HVertexOperator.coeff_inj; funext power; apply LinearMap.ext; intro vector
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply] using allModes (-power - 1) vector

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
theorem residue_closure
    (vacuum : V) (T : Module.End ℂ V) (translation_vacuum : T vacuum = 0)
    (creationHyp : ∀ a : V, ((Y a) [[-1]]) vacuum = a)
    (creative : ∀ (a : V) (n : ℤ), 0 ≤ n → ((Y a) [[n]]) vacuum = 0)
    (translation : ∀ (a : V) (n : ℤ),
      T * ((Y a) [[n]]) - ((Y a) [[n]]) * T =
        -(n : ℂ) • ((Y a) [[n - 1]]))
    (localityHyp : ∀ a b : V, ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator (Y a) (Y b)) = 0)
    (a b : V) (r : ℤ) :
    Y (mu (Y := Y) a r b) = (residueField (Y := Y) r a b).operator := by
  classical
  have locality (c : V) : ∃ order : ℕ, delta^[order] (FieldNormalProductLocality.commutator (residueField (Y := Y) r a b).operator (Y c)) = 0 := by
    classical
    by_cases nonnegative : 0 ≤ r
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
      exact residue_nonnegative_locality (Y := Y) localityHyp a b c degree
    · let degree := (-r - 1).toNat
      have index : r = -(degree : ℤ) - 1 := by dsimp [degree]; omega
      rw [index]
      have identification : (residueField (Y := Y) (-(degree : ℤ) - 1) a b).operator = (normalMinusOne (dividedDerivative degree (Y a)) (Y b)).val := by
        have derivativeModes (index : ℤ) (vector : V) : ((dividedDerivative degree (Y a)) [[index]]) vector = ((Ring.choose (-index - 1 + degree) degree : ℤ) : ℂ) • ((Y a)
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
        rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, (residueField (Y := Y) (-(degree : ℤ) - 1) a b).coefficient, (normalMinusOne (dividedDerivative degree (Y a)) (Y
          b)).property]
        let index : ℤ := -power - 1
        have firstEquality : residueLeft (Y := Y) (-(degree : ℤ) - 1) index a b vector = ∑ᶠ offset : ℕ, ((dividedDerivative degree (Y a)) [[-(offset : ℤ) - 1]]) (((Y b) [[index + offset]])
          vector) := by
          unfold residueLeft; apply finsum_congr; intro offset; rw [weight, derivativeModes]
          have parameter : -(-(offset : ℤ) - 1) - 1 + degree = ((degree + offset : ℕ) : ℤ) := by omega
          rw [parameter, Ring.choose_natCast]; rw [show -(degree : ℤ) - 1 - offset = -(offset : ℤ) - 1 - degree by omega]
          simp only [Int.cast_natCast]
        let term (offset : ℕ) : V := ((Y b) [[index - offset - 1]]) (((dividedDerivative degree (Y a)) [[offset]]) vector)
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
        have secondEquality : (∑ᶠ offset : ℕ, term offset) = (-1 : ℂ) ^ degree • residueRight (Y := Y) (-(degree : ℤ) - 1) index a b vector := by
          rw [split, residueRight, smul_finsum' _ ((residueField (Y := Y) (-(degree : ℤ) - 1) a b).right_finite index vector)]; apply finsum_congr
          intro offset; dsimp [term]; rw [derivativeModes, map_smul, weight]
          rw [show -((degree : ℤ) + offset) - 1 + degree = -(offset : ℤ) - 1 by omega, show -(offset : ℤ) - 1 = -((offset : ℤ) + 1) by omega, Ring.choose_neg, show (offset : ℤ) + 1
            + degree - 1 = ((degree + offset : ℕ) : ℤ) by omega, Ring.choose_natCast]
          simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast, Int.cast_natCast, smul_smul]
          rw [show (degree : ℤ) + offset - degree = offset by omega, show index - ((degree : ℤ) + offset) - 1 = -(degree : ℤ) - 1 + index - offset by omega]
        change residueCoefficient (Y := Y) (-(degree : ℤ) - 1) index a b vector = _; rw [residueCoefficient, firstEquality]
        change _ - epsilon (-(degree : ℤ) - 1) • residueRight (Y := Y) (-(degree : ℤ) - 1) index a b vector = _ + ∑ᶠ offset : ℕ, term offset
        rw [secondEquality, sub_eq_add_neg, ← neg_smul, sign]
      let shiftLeft : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
        toFun value := fun first second => value (first + 1) second
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
      let shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
        toFun value := fun first second => value first (second + 1)
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
      have binomial (value : ℤ → ℤ → Module.End ℂ V) (order : ℕ) (first second : ℤ) : ((deltaEnd ^ order) value) first second = ∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^
        offset) * (order.choose offset : ℂ)) • value (first + (order : ℤ) - offset) (second + offset) := by
        have commute : Commute (-shiftRight) shiftLeft := by apply LinearMap.ext; intro distribution; funext left right; simp [shiftLeft, shiftRight]
        have leftPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : (shiftLeft ^ degree) distribution = fun left right => distribution (left + degree) right := by
          induction degree with
          | zero => simp
          | succ degree inductionHypothesis =>
            rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
            change distribution (left + 1 + degree) right = distribution (left + (degree + 1 : ℕ)) right; congr 1; push_cast; omega
        have rightPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : ((-shiftRight) ^ degree) distribution = fun left right => ((-1 : ℂ) ^ degree) • distribution left
          (right + degree) := by
          induction degree with
          | zero => simp
          | succ degree inductionHypothesis =>
            rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
            change -(((-1 : ℂ) ^ degree) • distribution left (right + 1 + degree)) = ((-1 : ℂ) ^ (degree + 1)) • distribution left (right + (degree + 1 : ℕ))
            rw [pow_succ', mul_smul, neg_one_smul]
            have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by push_cast; omega
            rw [indices]
        have equation : (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V)) = -shiftRight + shiftLeft := by
          apply LinearMap.ext; intro distribution; funext left right; simp [deltaEnd, delta, shiftLeft, shiftRight]
          abel
        rw [equation, commute.add_pow, LinearMap.sum_apply]; simp only [Finset.sum_apply]; apply Finset.sum_congr rfl; intro offset member
        have within : offset ≤ order := by simpa using Finset.mem_range.mp member
        simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, rightPower, leftPower, Pi.smul_apply]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]; congr 2; push_cast [Int.natCast_sub within]; omega
      rw [identification]
      have locality (first second : V) : ∃ order : ℕ, delta^[order] (FieldNormalProductLocality.commutator (Y first) (Y second)) = 0 := by
        obtain ⟨order, law⟩ := localityHyp first second
        refine ⟨order, ?_⟩
        change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] (FieldNormalProductLocality.commutator (Y first) (Y second)) = 0
        have law' : (deltaEnd ^ order) (FieldNormalProductLocality.commutator (Y first) (Y second)) = 0 := by
          funext left right
          rw [deltaEnd_iterate_apply]
          exact congrFun (congrFun law left) right
        rw [← Module.End.pow_apply]
        funext left right
        rw [binomial]
        have lawPoint := congrFun (congrFun law' left) right
        rw [binomial] at lawPoint
        exact lawPoint
      obtain ⟨firstOrder, firstKilled⟩ := locality a c; obtain ⟨secondOrder, secondKilled⟩ := locality b c
      obtain ⟨thirdOrder, thirdKilled⟩ := locality a b; refine ⟨(firstOrder + degree) + secondOrder + (thirdOrder + degree), ?_⟩
      exact normalMinusOne_locality (dividedDerivative degree (Y a)) (Y b) (Y c) (firstOrder + degree) secondOrder (thirdOrder + degree) (dividedDerivative_locality (Y a) (Y c)
        firstOrder degree firstKilled) secondKilled (dividedDerivative_locality (Y a) (Y b) thirdOrder degree thirdKilled)
  have covariance (index : ℤ) : T * (((residueField (Y := Y) r a b).operator) [[index]]) - (((residueField (Y := Y) r a b).operator) [[index]]) * T = -(index : ℂ) • (((residueField (Y := Y) r a
    b).operator) [[index - 1]]) := by
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
    have firstMatch (mode : ℤ) (input : V) : residueLeft (Y := Y) r mode a b input = weightedSum (Y a) (Y b) r mode input := by rfl
    have secondMatch (mode : ℤ) (input : V) : residueRight (Y := Y) r mode a b input = weightedSum (Y b) (Y a) (r + mode) 0 input := by dsimp only [residueRight, weightedSum]; simp only [zero_add, weight]
    apply LinearMap.ext; intro vector
    change translationOp ((((residueField (Y := Y) r a b).operator) [[index]]) vector) - (((residueField (Y := Y) r a b).operator) [[index]]) (translationOp vector) = -(index : ℂ) • ((((residueField (Y := Y) r a
      b).operator) [[index - 1]]) vector)
    rw [(residueField (Y := Y) r a b).coefficient, (residueField (Y := Y) r a b).coefficient, (residueField (Y := Y) r a b).coefficient]
    have firstLaw := branchLaw (Y a) (Y b) (fun mode => translation a mode) (fun mode => translation b mode) r index vector
    have secondLaw := branchLaw (Y b) (Y a) (fun mode => translation b mode) (fun mode => translation a mode) (r + index) 0 vector
    simp only [sub_self, Int.cast_add, add_sub_cancel_left] at firstLaw secondLaw; simp only [residueCoefficient, firstMatch, secondMatch]
    rw [map_sub, map_smul]
    have arithmetic : r + index - 1 = r + (index - 1) := by omega
    rw [arithmetic] at secondLaw
    calc
      _ = (translationOp (weightedSum (Y a) (Y b) r index vector) - weightedSum (Y a) (Y b) r index (translationOp vector)) - epsilon r • (translationOp (weightedSum (Y b) (Y a) (r +
        index) 0 vector) - weightedSum (Y b) (Y a) (r + index) 0 (translationOp vector)) := by module
      _ = _ := by rw [firstLaw, secondLaw]; module
  have creation : (((residueField (Y := Y) r a b).operator) [[-1]]) vacuum = mu (Y := Y) a r b ∧ ∀ index : ℤ, 0 ≤ index → (((residueField (Y := Y) r a b).operator) [[index]]) vacuum = 0 := by

    have rightZero (index : ℤ) : residueRight (Y := Y) r index a b vacuum = 0 := by
      unfold residueRight; apply finsum_eq_zero_of_forall_eq_zero; intro offset; rw [creative a offset (by omega)]
      simp
    constructor
    · rw [(residueField (Y := Y) r a b).coefficient, residueCoefficient, rightZero, smul_zero, sub_zero]
      unfold residueLeft; rw [finsum_eq_single _ 0]
      · simp [integerBinomial, creationHyp b, mu]
      · intro offset distinct
        rw [creative b (-1 + (offset : ℤ)) (by omega)]; simp
    · intro index nonnegative
      rw [(residueField r a b).coefficient, residueCoefficient, rightZero, smul_zero, sub_zero]; unfold residueLeft
      apply finsum_eq_zero_of_forall_eq_zero; intro offset; rw [creative b (index + (offset : ℤ)) (by omega)]; simp

  let difference := (residueField (Y := Y) r a b).operator - Y (mu (Y := Y) a r b)
  have differenceCreative : ∀ index : ℤ, 0 ≤ index → (difference [[index]]) vacuum = 0 := by
    intro index nonnegative
    simp only [difference, map_sub, Pi.sub_apply, LinearMap.sub_apply, creation.2 index nonnegative, creative (mu (Y := Y) a r b) index nonnegative, sub_self]
  have initial : (difference [[-1]]) vacuum = 0 := by simp only [difference, map_sub, Pi.sub_apply, LinearMap.sub_apply, creation.1, creationHyp (mu (Y := Y) a r b), sub_self]
  have covariant : ∀ index : ℤ, T * (difference [[index]]) - (difference [[index]]) * T = -(index : ℂ) • (difference [[index - 1]]) := by
    intro index; simp only [difference, map_sub, Pi.sub_apply]
    calc
      _ = (T * (((residueField (Y := Y) r a b).operator) [[index]]) - (((residueField (Y := Y) r a b).operator) [[index]]) * T) - (T * ((Y (mu (Y := Y) a r b)) [[index]]) - ((Y (mu (Y := Y) a r b))
        [[index]]) * T) := by simp only [mul_sub, sub_mul]; abel
      _ = _ := by rw [covariance, translation]; module
  have crossLocality : ∀ state : V, ∃ order : ℕ, delta^[order] (FieldNormalProductLocality.commutator difference (Y state)) = 0 := by
    intro state; obtain ⟨firstOrder, firstKilled⟩ := locality state; obtain ⟨secondOrder, law⟩ := localityHyp (mu (Y := Y) a r b) state
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[firstOrder] (FieldNormalProductLocality.commutator (residueField (Y := Y) r a b).operator (Y state)) = 0 at firstKilled
    rw [← Module.End.pow_apply] at firstKilled
    have secondKilled : (deltaEnd ^ secondOrder) (FieldNormalProductLocality.commutator (Y (mu (Y := Y) a r b)) (Y state)) = 0 := by
      have law' : (deltaEnd ^ secondOrder) (FieldNormalProductLocality.commutator (Y (mu (Y := Y) a r b)) (Y state)) = 0 := by
        funext left right
        rw [deltaEnd_iterate_apply]
        exact congrFun (congrFun law left) right
      exact law'
    have firstHigh : (deltaEnd ^ (firstOrder + secondOrder)) (FieldNormalProductLocality.commutator (residueField (Y := Y) r a b).operator (Y state)) = 0 := by
      rw [pow_add, (Commute.refl deltaEnd).pow_pow firstOrder secondOrder |>.eq, Module.End.mul_apply, firstKilled, map_zero]
    have secondHigh : (deltaEnd ^ (firstOrder + secondOrder)) (FieldNormalProductLocality.commutator (Y (mu (Y := Y) a r b)) (Y state)) = 0 := by rw [pow_add, Module.End.mul_apply, secondKilled, map_zero]
    have split : FieldNormalProductLocality.commutator difference (Y state) = FieldNormalProductLocality.commutator (residueField (Y := Y) r a b).operator (Y state) -
      FieldNormalProductLocality.commutator (Y (mu (Y := Y) a r b)) (Y state) := by
      funext left right; dsimp only [FieldNormalProductLocality.commutator, difference]; simp only [map_sub, Pi.sub_apply, mul_sub, sub_mul]
      dsimp only [FieldNormalProductLocality.commutator]; abel
    refine ⟨firstOrder + secondOrder, ?_⟩
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[firstOrder + secondOrder] (FieldNormalProductLocality.commutator difference (Y state)) = 0
    rw [← Module.End.pow_apply, split, map_sub, firstHigh, secondHigh, sub_self]
  have vanished := relative_vacuum_uniqueness (Y := Y) vacuum T translation_vacuum creationHyp creative difference
    (fun index nonnegative => differenceCreative index nonnegative) initial covariant crossLocality
  exact (sub_eq_zero.mp vanished).symm

theorem stateField_iterate_of_creation_translation_locality
    (Y : V →ₗ[ℂ] VertexOperator ℂ V)
    (vacuum : V) (T : Module.End ℂ V)
    (translation_vacuum : T vacuum = 0)
    (creation : ∀ a : V, ((Y a) [[-1]]) vacuum = a)
    (creative : ∀ (a : V) (n : ℤ),
      0 ≤ n → ((Y a) [[n]]) vacuum = 0)
    (translation : ∀ (a : V) (n : ℤ),
      T * ((Y a) [[n]]) - ((Y a) [[n]]) * T =
        -(n : ℂ) • ((Y a) [[n - 1]]))
    (locality : ∀ a b : V, ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator (Y a) (Y b)) = 0)
    (a b c : V) (r n : ℤ) :
    let left : ℕ → V := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y a) [[r - (i : ℤ)]]) (((Y b) [[n + (i : ℤ)]]) c))
    let right : ℕ → V := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y b) [[r + n - (i : ℤ)]]) (((Y a) [[(i : ℤ)]]) c))
    Function.HasFiniteSupport left ∧
    Function.HasFiniteSupport right ∧
    (((Y (((Y a) [[r]]) b)) [[n]]) c) =
      (∑ᶠ i : ℕ, left i) - ((-1 : ℂ) ^ r) • (∑ᶠ i : ℕ, right i) := by
  dsimp
  let field := residueField (Y := Y) r a b
  have leftFinite : Function.HasFiniteSupport (fun i : ℕ =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y a) [[r - (i : ℤ)]]) (((Y b) [[n + (i : ℤ)]]) c))) := by
    simpa [field, integerBinomial] using field.left_finite n c
  have rightFinite : Function.HasFiniteSupport (fun i : ℕ =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y b) [[r + n - (i : ℤ)]]) (((Y a) [[(i : ℤ)]]) c))) := by
    simpa [field, integerBinomial] using field.right_finite n c
  refine ⟨leftFinite, rightFinite, ?_⟩
  have closure : Y (mu (Y := Y) a r b) = field.operator := residue_closure
    (Y := Y) vacuum T translation_vacuum creation creative translation locality a b r
  have closure' : Y (((Y a) [[r]]) b) = field.operator := by
    simpa [mu, field] using closure
  rw [closure', field.coefficient]
  rfl
end D5.S3.VertexAlgebra.StateFieldResidueReconstruction
