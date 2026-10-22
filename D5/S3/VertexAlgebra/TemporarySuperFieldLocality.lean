import D5.S3.VertexAlgebra.TemporarySuperFieldProducts
import D5.S3.VertexAlgebra.FieldNormalProductLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.SuperFieldLocality

open FieldNormalProduct
open FieldNormalProductLocality (Triple shiftXY shiftYZ NegativeFinite PositiveFinite
  PairSpace deltaXY deltaYZ res discrepancy plainXY plainYZ projectionFirst projectionSecond
  deltaEnd liftAC liftBC liftAB evaluate plainDelta weighted flipDistribution residue delta)
open SuperFieldProducts (superCommutator koszul SuperLocal normal)
open scoped VertexOperator

universe spaceLevel
noncomputable section
variable {Space : Type spaceLevel} [AddCommGroup Space] [Module ℂ Space]

theorem delta_iterate_eq_pow (distribution : ℤ → ℤ → Module.End ℂ Space) (order : ℕ) :
    delta^[order] distribution = ((deltaEnd (V := Space)) ^ order) distribution :=
  (Module.End.pow_apply (deltaEnd (V := Space)) order distribution).symm

private theorem residueXY (negative positive : Triple Space)
    (negativeFinite : NegativeFinite negative) (positiveFinite : PositiveFinite positive)
    (second third : ℤ) :
    residue (shiftXY negative) (shiftXY positive) second third =
      negative 0 second third - positive 0 second third := by
  classical
  let zeroSucc : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some offset => offset + 1
    invFun value := match value with | 0 => none | offset + 1 => some offset
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  have splitSum (term : ℕ → Space) (finite : Function.HasFiniteSupport term) :
      ∑ᶠ offset : ℕ, term offset = term 0 + ∑ᶠ offset : ℕ, term (offset + 1) := by
    rw [← finsum_comp_equiv zeroSucc, finsum_option]
    · rfl
    · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1)
        (fun first second equality => Nat.add_right_cancel equality)
  have negativeFirst : Function.HasFiniteSupport
      (fun offset : ℕ => negative (-(offset : ℤ)) (second + offset) third) := by
    simpa using negativeFinite 0 second third
  have negativeSecond : Function.HasFiniteSupport
      (fun offset : ℕ => negative (-(offset : ℤ) - 1) (second + offset + 1) third) := by
    simpa only [show ∀ offset : ℕ, (-1 : ℤ) - offset = -(offset : ℤ) - 1 by
      intro offset; omega, add_assoc, add_left_comm, add_comm] using negativeFinite (-1)
        (second + 1) third
  have positiveFirst : Function.HasFiniteSupport
      (fun offset : ℕ => positive ((offset : ℤ) + 1) (second - offset - 1) third) := by
    simpa only [add_comm, sub_right_comm] using positiveFinite 1 (second - 1) third
  have positiveSecond : Function.HasFiniteSupport
      (fun offset : ℕ => positive offset (second - offset) third) := by
    simpa using positiveFinite 0 second third
  unfold residue shiftXY
  simp_rw [show ∀ offset : ℕ, -(offset : ℤ) - 1 + 1 = -(offset : ℤ) by intro offset; omega,
    show ∀ offset : ℕ, second - offset - 1 + 1 = second - offset by intro offset; omega]
  rw [finsum_sub_distrib negativeFirst negativeSecond,
    finsum_sub_distrib positiveFirst positiveSecond,
    splitSum _ negativeFirst, splitSum _ positiveSecond]
  have negativeShift : (fun offset : ℕ => negative (-((offset + 1 : ℕ) : ℤ))
      (second + (offset + 1 : ℕ)) third) =
      (fun offset : ℕ => negative (-(offset : ℤ) - 1) (second + offset + 1) third) := by
    funext offset
    push_cast
    congr 1 <;> omega
  have positiveShift : (fun offset : ℕ => positive ((offset + 1 : ℕ) : ℤ)
      (second - (offset + 1 : ℕ)) third) =
      (fun offset : ℕ => positive ((offset : ℤ) + 1) (second - offset - 1) third) := by
    funext offset
    push_cast
    congr 1; omega
  rw [negativeShift, positiveShift]
  simp only [Nat.cast_zero, neg_zero, add_zero, sub_zero]
  abel
private theorem shiftsCommute : Commute (deltaXY (V := Space)) deltaYZ := by
  apply LinearMap.ext
  intro pair
  apply Subtype.ext
  ext <;> simp [deltaXY, deltaYZ, shiftXY, shiftYZ] <;> abel
private theorem residueYZ (pair : PairSpace Space) : res (deltaYZ pair) = delta (res pair) := by
  funext left right
  dsimp [res, residue, deltaYZ, shiftYZ, delta]
  have negativeFinite (left right : ℤ) : Function.HasFiniteSupport
      (fun offset : ℕ => pair.val.1 (-(offset : ℤ) - 1) (left + offset) right) := by
    simpa only [show ∀ offset : ℕ, (-1 : ℤ) - offset = -(offset : ℤ) - 1 by
      intro offset; omega] using pair.property.1 (-1) left right
  have positiveFinite (left right : ℤ) : Function.HasFiniteSupport
      (fun offset : ℕ => pair.val.2 offset (left - offset - 1) right) := by
    simpa only [zero_add, sub_right_comm] using pair.property.2 0 (left - 1) right
  have forwardIndex (offset : ℕ) : left + (offset : ℤ) + 1 = (left + 1) + offset := by omega
  have reverseIndex (offset : ℕ) :
      left - (offset : ℤ) - 1 + 1 = (left + 1) - offset - 1 := by omega
  simp_rw [forwardIndex, reverseIndex]
  rw [finsum_sub_distrib (negativeFinite (left + 1) right) (negativeFinite left (right + 1)),
    finsum_sub_distrib (positiveFinite (left + 1) right) (positiveFinite left (right + 1))]
  abel
private theorem discrepancyXY (pair : PairSpace Space) :
    discrepancy (deltaXY pair) = plainXY (discrepancy pair) := by
  funext left middle right
  dsimp [discrepancy, deltaXY, plainXY, shiftXY]
  abel
private theorem discrepancyYZ (pair : PairSpace Space) :
    discrepancy (deltaYZ pair) = plainYZ (discrepancy pair) := by
  funext left middle right
  dsimp [discrepancy, deltaYZ, plainYZ, shiftYZ]
  abel
private theorem intertwiningPowers {M Coefficient : Type spaceLevel} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup Coefficient] [Module ℂ Coefficient] (first : Module.End ℂ M) (second : Module.End ℂ Coefficient)
    (linear : M →ₗ[ℂ] Coefficient) (law : ∀ vector, linear (first vector) = second (linear vector))
    (order : ℕ) (vector : M) : linear ((first ^ order) vector) =
      (second ^ order) (linear vector) := by
  induction order with
  | zero => simp
  | succ order inductionHypothesis =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [law, inductionHypothesis]
private theorem cancellationBound (pair : PairSpace Space) (firstOrder secondOrder thirdOrder : ℕ)
    (annihilated : ((((deltaXY : Module.End ℂ (PairSpace Space)) + deltaYZ) ^ firstOrder *
      deltaYZ ^ secondOrder : Module.End ℂ (PairSpace Space))) pair = 0)
    (discrepancyKilled : discrepancy ((deltaXY ^ thirdOrder) pair) = 0) :
    delta^[firstOrder + secondOrder + thirdOrder] (res pair) = 0 := by
  let first : Module.End ℂ (PairSpace Space) := deltaXY
  let second : Module.End ℂ (PairSpace Space) := deltaYZ
  let combined := first + second
  have commuting : Commute first second := shiftsCommute
  have combinedCommute : Commute combined first := (Commute.refl first).add_left commuting.symm
  have firstCombined : Commute first combined := combinedCommute.symm
  have low (degree : ℕ) (large : firstOrder ≤ degree) :
      (combined ^ degree * second ^ secondOrder) pair = 0 := by
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le large
    rw [pow_add, (Commute.refl combined).pow_pow _ _ |>.eq]
    rw [mul_assoc, Module.End.mul_apply, annihilated, map_zero]
  have high (degree power : ℕ) (large : thirdOrder + 1 ≤ power) :
      res ((combined ^ degree * first ^ power * second ^ secondOrder) pair) = 0 := by
    obtain ⟨extra, powerEquality⟩ := Nat.exists_eq_add_of_le large
    have reorder : combined ^ degree * first ^ power * second ^ secondOrder =
        first * (combined ^ degree * first ^ extra * second ^ secondOrder) * first ^
          thirdOrder := by
      rw [powerEquality]
      rw [show thirdOrder + 1 + extra = 1 + extra + thirdOrder by omega, pow_add,
        pow_add, pow_one]
      calc
        _ = first * (combined ^ degree * first ^ extra * first ^ thirdOrder) *
            second ^ secondOrder := by
              rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
                (combinedCommute.pow_left degree).eq]
              simp only [mul_assoc]
        _ = (first * (combined ^ degree * first ^ extra)) *
            (first ^ thirdOrder * second ^ secondOrder) := by simp only [mul_assoc]
        _ = _ := by
          rw [(commuting.pow_pow thirdOrder secondOrder).eq]
          simp only [mul_assoc]
    rw [reorder]
    let value := (combined ^ degree * first ^ extra * second ^ secondOrder)
      ((first ^ thirdOrder) pair)
    change residue (shiftXY value.val.1) (shiftXY value.val.2) = _
    funext left right
    rw [residueXY]
    · have vanished : discrepancy
          ((combined ^ degree * first ^ extra * second ^ secondOrder)
            ((first ^ thirdOrder) pair)) = 0 := by
        simp only [Module.End.mul_apply]
        have combinedLaw (value : PairSpace Space) : discrepancy (combined value) =
            ((plainXY + plainYZ : Module.End ℂ (Triple Space))) (discrepancy value) := by
          change discrepancy (deltaXY value + deltaYZ value) =
            plainXY (discrepancy value) + plainYZ (discrepancy value)
          rw [map_add, discrepancyXY, discrepancyYZ]
        rw [intertwiningPowers combined (plainXY + plainYZ) discrepancy combinedLaw,
          intertwiningPowers first plainXY discrepancy discrepancyXY,
          intertwiningPowers second plainYZ discrepancy discrepancyYZ,
          discrepancyKilled, map_zero, map_zero, map_zero]
      have atCoefficient := congrFun (congrFun (congrFun vanished 0) left) right
      exact atCoefficient
    · exact ((combined ^ degree * first ^ extra * second ^ secondOrder)
        ((first ^ thirdOrder) pair)).property.1
    · exact ((combined ^ degree * first ^ extra * second ^ secondOrder)
        ((first ^ thirdOrder) pair)).property.2
  have cancellation : res ((second ^ (firstOrder + thirdOrder) * second ^ secondOrder) pair)
    = 0 := by
    have minusCommute : Commute combined (-first) := by
      apply LinearMap.ext
      intro value
      have law := congrArg (fun operator : Module.End ℂ (PairSpace Space) => operator value)
        combinedCommute.eq
      simpa only [Module.End.mul_apply, LinearMap.neg_apply, map_neg] using congrArg Neg.neg law
    have expansion := minusCommute.add_pow (firstOrder + thirdOrder)
    have sumEquality : second ^ (firstOrder + thirdOrder) =
        ∑ degree ∈ Finset.range (firstOrder + thirdOrder + 1),
          combined ^ degree * (-first) ^ (firstOrder + thirdOrder - degree) *
            (firstOrder + thirdOrder).choose degree := by
      have difference : combined + -first = second := by dsimp [combined]; abel
      rw [difference] at expansion
      exact expansion
    rw [sumEquality, Finset.sum_mul, LinearMap.sum_apply, map_sum]
    apply Finset.sum_eq_zero
    intro degree member
    have bound : degree ≤ firstOrder + thirdOrder := by simpa using Finset.mem_range.mp member
    have sign (order : ℕ) : (-first) ^ order = ((-1 : ℂ) ^ order) • first ^ order := by
      induction order with
      | zero => simp
      | succ order inductionHypothesis =>
        rw [pow_succ', inductionHypothesis, pow_succ']
        apply LinearMap.ext
        intro value
        simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply,
          mul_smul, neg_one_smul, map_smul]
        simp only [pow_succ', Module.End.mul_apply, smul_neg]
    rw [sign, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
      LinearMap.smul_apply, map_smul]
    simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
    by_cases large : firstOrder ≤ degree
    · have vanish : (combined ^ degree * first ^ (firstOrder + thirdOrder - degree) *
          second ^ secondOrder) pair = 0 := by
        rw [(combinedCommute.pow_pow _ _).eq, mul_assoc, Module.End.mul_apply]
        rw [low degree large, map_zero]
      have atCoefficient := congrArg (fun value => res value) vanish
      simp only [map_zero] at atCoefficient
      simp only [Module.End.mul_apply] at atCoefficient
      simp only [atCoefficient, smul_zero]
    · have vanish := high degree (firstOrder + thirdOrder - degree) (by omega)
      simp only [Module.End.mul_apply] at vanish
      simp only [vanish, smul_zero]
  have residuePowers (order : ℕ) (value : PairSpace Space) :
      res ((second ^ order) value) = delta^[order] (res value) := by
    induction order with
    | zero => simp
    | succ order inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, residueYZ, inductionHypothesis,
        Function.iterate_succ_apply']
  rw [← residuePowers]
  rw [show firstOrder + secondOrder + thirdOrder = firstOrder + thirdOrder + secondOrder by omega,
    pow_add]
  exact cancellation

private theorem commutatorRow_finite (exchange : ℂ) (first third : VertexOperator ℂ Space)
    (start finish : ℤ) (vector : Space) : Function.HasFiniteSupport
      (fun offset : ℕ => superCommutator exchange first third (start + offset) finish vector) := by
  have firstFinite := SuperFieldProducts.increasing_finite first start ((third[[finish]]) vector)
  have secondFinite := ((SuperFieldProducts.increasing_finite first start vector).comp
    ((third[[finish]])).map_zero).smul_right (fun _ => exchange)
  exact firstFinite.sub secondFinite

private def signedPairAC (exchangeAB exchangeAC exchangeBC : ℂ)
    (first second third : VertexOperator ℂ Space) (vector : Space) : PairSpace Space :=
  ⟨(exchangeBC • liftAC second vector true (superCommutator exchangeAC first third),
    exchangeAB • liftAC second vector false (superCommutator exchangeAC first third)), by
    constructor
    · intro left middle right
      apply Function.HasFiniteSupport.smul_right
      refine (SuperFieldProducts.increasing_finite second middle vector).subset ?_
      intro offset member vanish
      apply member
      change (second[[middle + offset]]) vector = 0 at vanish
      change superCommutator exchangeAC first third (left - offset) right
        ((second[[middle + offset]]) vector) = 0
      rw [vanish, map_zero]
    · intro left middle right
      apply Function.HasFiniteSupport.smul_right
      refine (commutatorRow_finite exchangeAC first third left right vector).subset ?_
      intro offset member vanish
      apply member
      change superCommutator exchangeAC first third (left + offset) right vector = 0 at vanish
      change (second[[middle - offset]])
        (superCommutator exchangeAC first third (left + offset) right vector) = 0
      rw [vanish, map_zero]⟩

private def signedPairBC (exchangeAB exchangeAC exchangeBC : ℂ)
    (first second third : VertexOperator ℂ Space) (vector : Space) : PairSpace Space :=
  ⟨(liftBC first vector true (superCommutator exchangeBC second third),
    (exchangeAB * exchangeAC) • liftBC first vector false
      (superCommutator exchangeBC second third)), by
    constructor
    · intro left middle right
      refine (commutatorRow_finite exchangeBC second third middle right vector).subset ?_
      intro offset member vanish
      apply member
      change superCommutator exchangeBC second third (middle + offset) right vector = 0 at vanish
      change (first[[left - offset]])
        (superCommutator exchangeBC second third (middle + offset) right vector) = 0
      rw [vanish, map_zero]
    · intro left middle right
      apply Function.HasFiniteSupport.smul_right
      refine (SuperFieldProducts.increasing_finite first left vector).subset ?_
      intro offset member vanish
      apply member
      change (first[[left + offset]]) vector = 0 at vanish
      change superCommutator exchangeBC second third (middle - offset) right
        ((first[[left + offset]]) vector) = 0
      rw [vanish, map_zero]⟩

private def signedTriplePair (exchangeAB exchangeAC exchangeBC : ℂ)
    (first second third : VertexOperator ℂ Space) (vector : Space) : PairSpace Space :=
  signedPairAC exchangeAB exchangeAC exchangeBC first second third vector +
    signedPairBC exchangeAB exchangeAC exchangeBC first second third vector

private theorem signedTripleCoefficients (exchangeAB exchangeAC exchangeBC : ℂ)
    (first second third : VertexOperator ℂ Space) (vector : Space) (left middle right : ℤ) :
    (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector).val.1
        left middle right =
      (first[[left]]) ((second[[middle]]) ((third[[right]]) vector)) -
        (exchangeAC * exchangeBC) • (third[[right]]) ((first[[left]]) ((second[[middle]]) vector)) ∧
    (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector).val.2
        left middle right =
      exchangeAB • (second[[middle]]) ((first[[left]]) ((third[[right]]) vector)) -
        (exchangeAB * (exchangeAC * exchangeBC)) •
          (third[[right]]) ((second[[middle]]) ((first[[left]]) vector)) := by
  constructor <;>
    dsimp [signedTriplePair, signedPairAC, signedPairBC, liftAC, liftBC, superCommutator] <;>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      map_sub, map_smul] <;> module

theorem normal_locality (exchangeAB exchangeAC exchangeBC : ℂ)
    (first second third : VertexOperator ℂ Space) (firstOrder secondOrder thirdOrder : ℕ)
    (firstKilled : delta^[firstOrder] (superCommutator exchangeAC first third) = 0)
    (secondKilled : delta^[secondOrder] (superCommutator exchangeBC second third) = 0)
    (thirdKilled : delta^[thirdOrder] (superCommutator exchangeAB first second) = 0) :
    delta^[firstOrder + secondOrder + thirdOrder]
      (superCommutator (exchangeAC * exchangeBC) (normal exchangeAB first second) third) = 0 := by
  funext left right
  apply LinearMap.ext
  intro vector
  let combined : Module.End ℂ (PairSpace Space) := deltaXY + deltaYZ
  let combinedPlain : Module.End ℂ (Triple Space) := plainXY + plainYZ
  have acLaw (factor : Bool) (distribution : ℤ → ℤ → Module.End ℂ Space) :
      liftAC second vector factor (deltaEnd distribution) =
        combinedPlain (liftAC second vector factor distribution) := by
    funext left middle right
    dsimp [liftAC, deltaEnd, delta, combinedPlain, plainXY, plainYZ, shiftXY, shiftYZ]
    cases factor <;> simp only [Bool.false_eq_true, if_false, if_true, map_sub] <;> abel
  have bcLaw (factor : Bool) (distribution : ℤ → ℤ → Module.End ℂ Space) :
      liftBC first vector factor (deltaEnd distribution) =
        plainYZ (liftBC first vector factor distribution) := by
    funext left middle right
    dsimp [liftBC, deltaEnd, delta, plainYZ, shiftYZ]
    cases factor <;> simp only [Bool.false_eq_true, if_false, if_true, map_sub]
  have acLiftKilled (factor : Bool) : (combinedPlain ^ firstOrder)
      (liftAC second vector factor (superCommutator exchangeAC first third)) = 0 := by
    rw [← intertwiningPowers deltaEnd combinedPlain (liftAC second vector factor) (acLaw factor),
      Module.End.pow_apply]
    change liftAC second vector factor
      (delta^[firstOrder] (superCommutator exchangeAC first third)) = 0
    rw [firstKilled, map_zero]
  have bcLiftKilled (factor : Bool) : (plainYZ ^ secondOrder)
      (liftBC first vector factor (superCommutator exchangeBC second third)) = 0 := by
    rw [← intertwiningPowers deltaEnd plainYZ (liftBC first vector factor) (bcLaw factor),
      Module.End.pow_apply]
    change liftBC first vector factor
      (delta^[secondOrder] (superCommutator exchangeBC second third)) = 0
    rw [secondKilled, map_zero]
  have acKilled : (combined ^ firstOrder)
      (signedPairAC exchangeAB exchangeAC exchangeBC first second third vector) = 0 := by
    apply Subtype.ext
    apply Prod.ext
    · change projectionFirst ((combined ^ firstOrder) _) = 0
      rw [intertwiningPowers combined combinedPlain projectionFirst (fun _ => rfl)]
      change (combinedPlain ^ firstOrder)
        (exchangeBC • liftAC second vector true (superCommutator exchangeAC first third)) = 0
      rw [map_smul, acLiftKilled, smul_zero]
    · change projectionSecond ((combined ^ firstOrder) _) = 0
      rw [intertwiningPowers combined combinedPlain projectionSecond (fun _ => rfl)]
      change (combinedPlain ^ firstOrder)
        (exchangeAB • liftAC second vector false (superCommutator exchangeAC first third)) = 0
      rw [map_smul, acLiftKilled, smul_zero]
  have bcKilled : (deltaYZ ^ secondOrder)
      (signedPairBC exchangeAB exchangeAC exchangeBC first second third vector) = 0 := by
    apply Subtype.ext
    apply Prod.ext
    · change projectionFirst ((deltaYZ ^ secondOrder) _) = 0
      rw [intertwiningPowers (deltaYZ (V := Space)) plainYZ projectionFirst (fun _ => rfl)]
      exact bcLiftKilled true
    · change projectionSecond ((deltaYZ ^ secondOrder) _) = 0
      rw [intertwiningPowers (deltaYZ (V := Space)) plainYZ projectionSecond (fun _ => rfl)]
      change (plainYZ ^ secondOrder) ((exchangeAB * exchangeAC) •
        liftBC first vector false (superCommutator exchangeBC second third)) = 0
      rw [map_smul, bcLiftKilled, smul_zero]
  have low : (combined ^ firstOrder * (deltaYZ (V := Space)) ^ secondOrder)
      (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector) = 0 := by
    rw [signedTriplePair, Module.End.mul_apply, map_add, map_add]
    have commute : Commute combined deltaYZ :=
      shiftsCommute.add_left (Commute.refl deltaYZ)
    rw [← Module.End.mul_apply, (commute.pow_pow firstOrder secondOrder).eq,
      Module.End.mul_apply, acKilled, map_zero, bcKilled, map_zero, add_zero]
  let lifting := liftAB third vector true -
    (exchangeAC * exchangeBC) • liftAB third vector false
  have difference : discrepancy
      (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector) =
      lifting (superCommutator exchangeAB first second) := by
    funext left middle right
    change (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector).val.1
        left middle right -
      (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector).val.2
        left middle right = _
    rw [(signedTripleCoefficients exchangeAB exchangeAC exchangeBC first second third vector
      left middle right).1, (signedTripleCoefficients exchangeAB exchangeAC exchangeBC
      first second third vector left middle right).2]
    dsimp [lifting, liftAB, superCommutator]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sub, map_smul]
    module
  have liftingLaw (distribution : ℤ → ℤ → Module.End ℂ Space) :
      lifting (deltaEnd distribution) = plainXY (lifting distribution) := by
    funext left middle right
    dsimp [lifting, liftAB, deltaEnd, delta, plainXY, shiftXY]
    simp only [map_sub, smul_sub]
    abel
  have high : discrepancy ((deltaXY ^ thirdOrder)
      (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector)) = 0 := by
    rw [intertwiningPowers (deltaXY (V := Space)) plainXY discrepancy discrepancyXY,
      difference, ← intertwiningPowers deltaEnd plainXY lifting liftingLaw,
      Module.End.pow_apply]
    change lifting (delta^[thirdOrder] (superCommutator exchangeAB first second)) = 0
    rw [thirdKilled, map_zero]
  have residueLaw : res
      (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector) =
      fun left right => superCommutator (exchangeAC * exchangeBC)
        (normal exchangeAB first second) third left right vector := by
    funext left right
    have forwardFinite (value : Space) : Function.HasFiniteSupport
        (fun offset : ℕ => (first[[-(offset : ℤ) - 1]]) ((second[[left + offset]]) value)) := by
      simpa only [show ∀ offset : ℕ, (-1 : ℤ) - offset = -(offset : ℤ) - 1 by
        intro offset; omega] using SuperFieldProducts.forward_finite first second (-1) left value
    have reverseFinite (value : Space) : Function.HasFiniteSupport
        (fun offset : ℕ => (second[[left - offset - 1]]) ((first[[offset]]) value)) := by
      simpa only [zero_add, sub_right_comm] using
        SuperFieldProducts.forward_finite second first (left - 1) 0 value
    have mappedForward := (forwardFinite vector).comp ((third[[right]])).map_zero
    have mappedReverse := (reverseFinite vector).comp ((third[[right]])).map_zero
    have forwardScaled := mappedForward.smul_right (fun _ => exchangeAC * exchangeBC)
    have reverseScaled := (reverseFinite ((third[[right]]) vector)).smul_right
      (fun _ => exchangeAB)
    have reverseMappedScaled := mappedReverse.smul_right
      (fun _ => exchangeAB * (exchangeAC * exchangeBC))
    simp only [Pi.smul_def', Function.comp_def] at mappedForward mappedReverse forwardScaled reverseScaled reverseMappedScaled
    change residue _ _ left right = _
    unfold residue
    simp_rw [(signedTripleCoefficients exchangeAB exchangeAC exchangeBC first second third
      vector _ _ right).1, (signedTripleCoefficients exchangeAB exchangeAC exchangeBC
      first second third vector _ _ right).2]
    rw [finsum_sub_distrib (forwardFinite ((third[[right]]) vector))
        forwardScaled, finsum_sub_distrib reverseScaled reverseMappedScaled]
    rw [← smul_finsum' (exchangeAC * exchangeBC) mappedForward,
      ← smul_finsum' exchangeAB (reverseFinite ((third[[right]]) vector)),
      ← smul_finsum' (exchangeAB * (exchangeAC * exchangeBC)) mappedReverse,
      ← map_finsum ((third[[right]])) (forwardFinite vector),
      ← map_finsum ((third[[right]])) (reverseFinite vector)]
    rw [superCommutator, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.mul_apply, SuperFieldProducts.normal_modes, SuperFieldProducts.normal_modes,
      map_add, map_smul]
    module
  have cancelled := cancellationBound
    (signedTriplePair exchangeAB exchangeAC exchangeBC first second third vector)
    firstOrder secondOrder thirdOrder low high
  rw [residueLaw] at cancelled
  have evaluationLaw (distribution : ℤ → ℤ → Module.End ℂ Space) :
      evaluate vector (deltaEnd distribution) = plainDelta (evaluate vector distribution) := rfl
  have transport := intertwiningPowers deltaEnd plainDelta (evaluate vector) evaluationLaw
    (firstOrder + secondOrder + thirdOrder)
    (superCommutator (exchangeAC * exchangeBC) (normal exchangeAB first second) third)
  rw [Module.End.pow_apply, Module.End.pow_apply] at transport
  change evaluate vector (delta^[firstOrder + secondOrder + thirdOrder]
      (superCommutator (exchangeAC * exchangeBC) (normal exchangeAB first second) third)) =
    delta^[firstOrder + secondOrder + thirdOrder]
      (fun left right => superCommutator (exchangeAC * exchangeBC)
        (normal exchangeAB first second) third left right vector) at transport
  rw [cancelled] at transport
  exact congrFun (congrFun transport left) right

theorem dividedDerivative_locality (exchange : ℂ) (first second : VertexOperator ℂ Space) (order degree : ℕ)
    (killed : delta^[order] (superCommutator exchange first second) = 0) :
    delta^[order + degree] (superCommutator exchange (dividedDerivative degree first) second) = 0 := by
  have leftDerivativeLocal (first second : VertexOperator ℂ Space) (order : ℕ)
      (killed : delta^[order] (superCommutator exchange first second) = 0) :
      delta^[order + 1] (superCommutator exchange (dividedDerivative 1 first) second) = 0 := by
    have modes (index : ℤ) : (((dividedDerivative 1 first) [[index]])) =
        -(index : ℂ) • ((first [[index - 1]])) := by
      apply LinearMap.ext
      intro vector
      change Ring.choose (-index - 1 + 1) 1 •
        HVertexOperator.coeff first (-index - 1 + 1) vector = _
      rw [Ring.choose_one_right, VertexOperator.coeff_eq_ncoeff]
      rw [show -(-index - 1 + 1) - 1 = index - 1 by omega]
      simp only [LinearMap.smul_apply,
        show -index - 1 + 1 = -index by omega]
      rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg]
    have differentiated : superCommutator exchange (dividedDerivative 1 first) second = weighted (superCommutator exchange
      first second) := by
      funext left right
      rw [superCommutator, modes, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        smul_comm exchange (-(left : ℂ)), ← smul_sub]
      rfl
    rw [differentiated]
    have linearDelta (first second : ℤ → ℤ → Module.End ℂ Space) :
        delta (first - second) = delta first - delta second := by
      funext left right
      dsimp [delta]
      abel
    have scaledDelta (scalar : ℂ) (distribution : ℤ → ℤ → Module.End ℂ Space) :
        delta (scalar • distribution) = scalar • delta distribution := by
      funext left right
      simp [delta, smul_sub]
    have leibniz (distribution : ℤ → ℤ → Module.End ℂ Space) :
        delta (weighted distribution) = weighted (delta distribution) - distribution := by
      funext left right
      dsimp [delta, weighted]
      rw [show left + 1 - 1 = left by omega, show left - 1 + 1 = left by omega]
      push_cast
      module
    have iterated (distribution : ℤ → ℤ → Module.End ℂ Space) : ∀ degree : ℕ,
        delta^[degree + 1] (weighted distribution) = weighted (delta^[degree + 1] distribution) -
          ((degree + 1 : ℕ) : ℂ) • delta^[degree] distribution := by
      intro degree
      induction degree with
      | zero => simpa using leibniz distribution
      | succ degree inductionHypothesis =>
        rw [Function.iterate_succ_apply', inductionHypothesis, linearDelta, scaledDelta, leibniz]
        rw [← Function.iterate_succ_apply' (f := delta) degree distribution,
          ← Function.iterate_succ_apply' (f := delta) (degree + 1) distribution]
        funext left right
        simp only [Pi.sub_apply, Pi.smul_apply]
        push_cast
        module
    rw [iterated]
    have next : delta^[order + 1] (superCommutator exchange first second) = 0 := by
      rw [Function.iterate_succ_apply', killed]
      funext left right
      simp [delta]
    rw [killed, next]
    funext left right
    simp [weighted]
  have successive : ∀ count : ℕ,
      delta^[order + count] (superCommutator exchange ((dividedDerivative 1)^[count] first) second) = 0 := by
    intro count
    induction count with
    | zero => simpa using killed
    | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      simpa only [Nat.add_assoc] using leftDerivativeLocal
        ((dividedDerivative 1)^[count] first) second (order + count) inductionHypothesis
  have evaluation (vector : Space) : ∀ (count : ℕ) (operator : VertexOperator ℂ Space),
      ((dividedDerivative 1)^[count] operator) vector =
        HahnModule.of ℂ ((LaurentSeries.derivative ℂ)^[count]
          ((HahnModule.of ℂ).symm (operator vector))) := by
    intro count
    induction count with
    | zero => intro operator; simp
    | succ count inductionHypothesis =>
      intro operator
      rw [Function.iterate_succ_apply']
      change HahnModule.of ℂ (LaurentSeries.hasseDeriv ℂ 1
          ((HahnModule.of ℂ).symm (((dividedDerivative 1)^[count] operator) vector))) = _
      rw [inductionHypothesis operator, Equiv.symm_apply_apply,
        Function.iterate_succ_apply']
      rfl
  have identity : (dividedDerivative 1)^[degree] first =
      (degree.factorial : ℂ) • dividedDerivative degree first := by
    apply LinearMap.ext
    intro vector
    rw [evaluation vector, LaurentSeries.derivative_iterate]
    change degree.factorial • (dividedDerivative degree first) vector =
      (degree.factorial : ℂ) • (dividedDerivative degree first) vector
    simp only [Nat.cast_smul_eq_nsmul]
  have scaled : superCommutator exchange ((degree.factorial : ℂ) • dividedDerivative degree first) second =
      (degree.factorial : ℂ) • superCommutator exchange (dividedDerivative degree first) second := by
    funext left right
    simp only [superCommutator, map_smul, Pi.smul_apply, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  have result := successive degree
  rw [identity, scaled] at result
  have linearity : delta^[order + degree]
      ((degree.factorial : ℂ) • superCommutator exchange (dividedDerivative degree first) second) =
      (degree.factorial : ℂ) • delta^[order + degree]
        (superCommutator exchange (dividedDerivative degree first) second) := by
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Space))^[order + degree] _ =
      (degree.factorial : ℂ) • (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Space))^[order + degree] _
    rw [← Module.End.pow_apply, ← Module.End.pow_apply, map_smul]
  rw [linearity] at result
  exact (smul_eq_zero.mp result).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero degree))


theorem locality_raise (exchange : ℂ) (first second : VertexOperator ℂ Space)
    (order larger : ℕ) (bound : order ≤ larger)
    (killed : delta^[order] (superCommutator exchange first second) = 0) :
    delta^[larger] (superCommutator exchange first second) = 0 := by
  rw [delta_iterate_eq_pow]
  rw [show larger = (larger - order) + order by omega, pow_add, Module.End.mul_apply]
  have zeroAtOrder : (deltaEnd ^ order) (superCommutator exchange first second) = 0 := by
    rw [Module.End.pow_apply]
    exact killed
  rw [zeroAtOrder, map_zero]

theorem symmetry_killed (exchange : ℂ) (square : exchange * exchange = 1)
    (first second : VertexOperator ℂ Space) (order : ℕ)
    (killed : delta^[order] (superCommutator exchange first second) = 0) :
    delta^[order] (superCommutator exchange second first) = 0 := by
  have reverse : superCommutator exchange second first =
      -exchange • flipDistribution (superCommutator exchange first second) := by
    funext left right
    dsimp [superCommutator, flipDistribution]
    rw [smul_sub, smul_smul, neg_mul, square, neg_one_smul, sub_neg_eq_add]
    module
  have flipLaw (distribution : ℤ → ℤ → Module.End ℂ Space) :
      delta (flipDistribution distribution) = -flipDistribution (delta distribution) := by
    funext left right
    dsimp [delta, flipDistribution]
    abel
  have flipped (distribution : ℤ → ℤ → Module.End ℂ Space) : ∀ count : ℕ,
      delta^[count] (flipDistribution distribution) =
        (-1 : ℂ) ^ count • flipDistribution (delta^[count] distribution) := by
    intro count
    induction count with
    | zero => simp
    | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis]
      change deltaEnd ((-1 : ℂ) ^ count • flipDistribution (delta^[count] distribution)) = _
      rw [map_smul]
      change (-1 : ℂ) ^ count • delta (flipDistribution (delta^[count] distribution)) = _
      rw [flipLaw, Function.iterate_succ_apply', pow_succ]
      simp only [mul_smul, neg_one_smul, smul_neg]
  rw [reverse]
  rw [delta_iterate_eq_pow]
  rw [map_smul, ← delta_iterate_eq_pow, flipped, killed, map_zero, smul_zero, smul_zero]

theorem superLocal_symm (leftParity rightParity : ℕ) (first second : VertexOperator ℂ Space)
    (localWitness : SuperLocal leftParity rightParity first second) :
    SuperLocal rightParity leftParity second first := by
  rcases localWitness with ⟨order, killed⟩
  refine ⟨order, ?_⟩
  rw [SuperFieldProducts.koszul_symm rightParity leftParity]
  exact symmetry_killed (koszul leftParity rightParity)
    (SuperFieldProducts.koszul_square leftParity rightParity) first second order killed

theorem normal_superLocal (firstParity secondParity thirdParity : ℕ)
    (first second third : VertexOperator ℂ Space)
    (firstLocal : SuperLocal firstParity thirdParity first third)
    (secondLocal : SuperLocal secondParity thirdParity second third)
    (pairLocal : SuperLocal firstParity secondParity first second) :
    SuperLocal (firstParity + secondParity) thirdParity
      (normal (koszul firstParity secondParity) first second) third := by
  rcases firstLocal with ⟨firstOrder, firstKilled⟩
  rcases secondLocal with ⟨secondOrder, secondKilled⟩
  rcases pairLocal with ⟨thirdOrder, thirdKilled⟩
  refine ⟨firstOrder + secondOrder + thirdOrder, ?_⟩
  rw [SuperFieldProducts.koszul_add_left]
  exact normal_locality (koszul firstParity secondParity) (koszul firstParity thirdParity)
    (koszul secondParity thirdParity) first second third firstOrder secondOrder thirdOrder
    firstKilled secondKilled thirdKilled

theorem superLocal_add_left (leftParity rightParity : ℕ) (first second third : VertexOperator ℂ Space)
    (firstLocal : SuperLocal leftParity rightParity first third)
    (secondLocal : SuperLocal leftParity rightParity second third) :
    SuperLocal leftParity rightParity (first + second) third := by
  rcases firstLocal with ⟨firstOrder, firstKilled⟩
  rcases secondLocal with ⟨secondOrder, secondKilled⟩
  refine ⟨firstOrder + secondOrder, ?_⟩
  rw [SuperFieldProducts.superCommutator_add_left]
  change delta^[firstOrder + secondOrder]
    (superCommutator (koszul leftParity rightParity) first third +
      superCommutator (koszul leftParity rightParity) second third) = 0
  rw [delta_iterate_eq_pow]
  rw [map_add, ← delta_iterate_eq_pow, ← delta_iterate_eq_pow,
    locality_raise _ first third firstOrder (firstOrder + secondOrder) (by omega) firstKilled,
    locality_raise _ second third secondOrder (firstOrder + secondOrder) (by omega) secondKilled,
    add_zero]

theorem superLocal_smul_left (leftParity rightParity : ℕ) (scalar : ℂ)
    (first second : VertexOperator ℂ Space) (localWitness : SuperLocal leftParity rightParity first second) :
    SuperLocal leftParity rightParity (scalar • first) second := by
  rcases localWitness with ⟨order, killed⟩
  refine ⟨order, ?_⟩
  rw [SuperFieldProducts.superCommutator_smul_left]
  change delta^[order] (scalar • superCommutator (koszul leftParity rightParity) first second) = 0
  change delta^[order] (superCommutator (koszul leftParity rightParity) first second) = 0 at killed
  rw [delta_iterate_eq_pow]
  rw [map_smul, ← delta_iterate_eq_pow, killed, smul_zero]

theorem superLocal_zero_left (leftParity rightParity : ℕ) (second : VertexOperator ℂ Space) :
    SuperLocal leftParity rightParity 0 second := by
  refine ⟨0, ?_⟩
  funext left right
  simp [superCommutator]

theorem superLocal_sum_left {Index : Type*} (indices : Finset Index)
    (leftParity rightParity : ℕ) (fields : Index → VertexOperator ℂ Space) (second : VertexOperator ℂ Space)
    (localWitness : ∀ index ∈ indices, SuperLocal leftParity rightParity (fields index) second) :
    SuperLocal leftParity rightParity (∑ index ∈ indices, fields index) second := by
  classical
  revert localWitness
  induction indices using Finset.induction_on with
  | empty =>
    intro localWitness
    simpa using superLocal_zero_left leftParity rightParity second
  | @insert index indices absent inductionHypothesis =>
    intro localWitness
    rw [Finset.sum_insert absent]
    exact superLocal_add_left leftParity rightParity _ _ second
      (localWitness index (Finset.mem_insert_self index indices))
      (inductionHypothesis (fun other member => localWitness other (Finset.mem_insert_of_mem member)))

theorem superLocal_add_right (leftParity rightParity : ℕ) (first second third : VertexOperator ℂ Space)
    (secondLocal : SuperLocal leftParity rightParity first second)
    (thirdLocal : SuperLocal leftParity rightParity first third) :
    SuperLocal leftParity rightParity first (second + third) := by
  rcases secondLocal with ⟨secondOrder, secondKilled⟩
  rcases thirdLocal with ⟨thirdOrder, thirdKilled⟩
  refine ⟨secondOrder + thirdOrder, ?_⟩
  rw [SuperFieldProducts.superCommutator_add_right]
  change delta^[secondOrder + thirdOrder]
    (superCommutator (koszul leftParity rightParity) first second +
      superCommutator (koszul leftParity rightParity) first third) = 0
  rw [delta_iterate_eq_pow]
  rw [map_add, ← delta_iterate_eq_pow, ← delta_iterate_eq_pow,
    locality_raise _ first second secondOrder (secondOrder + thirdOrder) (by omega) secondKilled,
    locality_raise _ first third thirdOrder (secondOrder + thirdOrder) (by omega) thirdKilled,
    add_zero]

theorem superLocal_smul_right (leftParity rightParity : ℕ) (scalar : ℂ)
    (first second : VertexOperator ℂ Space) (localWitness : SuperLocal leftParity rightParity first second) :
    SuperLocal leftParity rightParity first (scalar • second) := by
  rcases localWitness with ⟨order, killed⟩
  refine ⟨order, ?_⟩
  rw [SuperFieldProducts.superCommutator_smul_right]
  change delta^[order] (scalar • superCommutator (koszul leftParity rightParity) first second) = 0
  change delta^[order] (superCommutator (koszul leftParity rightParity) first second) = 0 at killed
  rw [delta_iterate_eq_pow]
  rw [map_smul, ← delta_iterate_eq_pow, killed, smul_zero]

theorem superLocal_zero_right (leftParity rightParity : ℕ) (first : VertexOperator ℂ Space) :
    SuperLocal leftParity rightParity first 0 := by
  refine ⟨0, ?_⟩
  funext left right
  simp [superCommutator]

theorem superLocal_sum_right {Index : Type*} (indices : Finset Index)
    (leftParity rightParity : ℕ) (first : VertexOperator ℂ Space) (fields : Index → VertexOperator ℂ Space)
    (localWitness : ∀ index ∈ indices, SuperLocal leftParity rightParity first (fields index)) :
    SuperLocal leftParity rightParity first (∑ index ∈ indices, fields index) := by
  classical
  revert localWitness
  induction indices using Finset.induction_on with
  | empty =>
    intro localWitness
    simpa using superLocal_zero_right leftParity rightParity first
  | @insert index indices absent inductionHypothesis =>
    intro localWitness
    rw [Finset.sum_insert absent]
    exact superLocal_add_right leftParity rightParity first _ _
      (localWitness index (Finset.mem_insert_self index indices))
      (inductionHypothesis (fun other member => localWitness other (Finset.mem_insert_of_mem member)))

theorem dividedDerivative_superLocal (leftParity rightParity degree : ℕ)
    (first second : VertexOperator ℂ Space) (localWitness : SuperLocal leftParity rightParity first second) :
    SuperLocal leftParity rightParity (dividedDerivative degree first) second := by
  rcases localWitness with ⟨order, killed⟩
  exact ⟨order + degree, dividedDerivative_locality _ first second order degree killed⟩

end
end D5.S3.VertexAlgebra.SuperFieldLocality
