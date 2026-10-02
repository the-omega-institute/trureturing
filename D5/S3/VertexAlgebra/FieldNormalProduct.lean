/- GID: D5/S3/VertexAlgebra/FieldNormalProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FieldNormalProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise finite ordered normal products for polynomial Fock state fields. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Scott Carnahan
Modified source: Hasse lifting and finite-support arguments adapted from
ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea,
VertexAlg/VertexBasic/VertexOperator.lean. Only the minus-one product is retained;
its bounded-pole proof uses finitely many actual intermediate states.
proof_shape: normalMinusOne_translation: content
escape_witness: The two finite mode sums telescope across the zero-mode boundary;
the resulting coefficient covariance is used by the unrestricted Fock state fields.
admission_basis: escape-witness
-/

import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.FieldNormalProduct

open scoped VertexOperator

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

noncomputable def identityField : VertexOperator ℂ V :=
  VertexOperator.of_coeff (fun power => if power = 0 then LinearMap.id else 0) (by
    intro vector
    refine ⟨0, ?_⟩
    intro power member
    by_contra negative
    exact member (by simp [show power ≠ 0 by omega]))

set_option backward.isDefEq.respectTransparency false in
noncomputable def dividedDerivative (order : ℕ)
    (operator : VertexOperator ℂ V) : VertexOperator ℂ V where
  toFun vector := HahnModule.of ℂ
    (LaurentSeries.hasseDeriv ℂ order ((HahnModule.of ℂ).symm (operator vector)))
  map_add' first second := by simp
  map_smul' scalar vector := by
    simp

noncomputable def normalMinusOne (left right : VertexOperator ℂ V) :
    {operator : VertexOperator ℂ V // ∀ index vector,
      (operator [[index]]) vector =
        (∑ᶠ offset : ℕ, (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) +
        (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))} := by
  classical
  have leftFinite (index : ℤ) (vector : V) : Function.HasFiniteSupport
      (fun offset : ℕ => (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (right vector)).order - index).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (right [[index + offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  have rightFinite (index : ℤ) (vector : V) : Function.HasFiniteSupport
      (fun offset : ℕ => (right [[index - offset - 1]]) ((left [[offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (left vector)).order - 1).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (left [[offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  let coefficient (index : ℤ) : Module.End ℂ V := {
    toFun vector :=
      (∑ᶠ offset : ℕ, (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) +
      (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))
    map_add' first second := by
      simp only [map_add]
      rw [finsum_add_distrib (leftFinite index first) (leftFinite index second),
        finsum_add_distrib (rightFinite index first) (rightFinite index second)]
      abel
    map_smul' scalar vector := by
      simp only [map_smul]
      rw [← smul_finsum' scalar (leftFinite index vector),
        ← smul_finsum' scalar (rightFinite index vector)]
      simp [smul_add] }
  have bounded (vector : V) :
      BddBelow (Function.support (fun power : ℤ => coefficient (-power - 1) vector)) := by
    let cutoff : ℕ := (-((HahnModule.of ℂ).symm (left vector)).order - 1).toNat
    let orders : Finset ℤ := (Finset.range (cutoff + 1)).image
      (fun offset : ℕ => ((HahnModule.of ℂ).symm
        (right ((left [[(offset : ℤ)]]) vector))).order - (offset : ℤ) - 1)
    let lower : ℤ := min ((HahnModule.of ℂ).symm (right vector)).order
      (orders.min' (by
        apply Finset.image_nonempty.mpr
        exact ⟨0, Finset.mem_range.mpr (by omega)⟩))
    refine ⟨lower, ?_⟩
    intro power member
    by_contra notLower
    have small : power < lower := lt_of_not_ge notLower
    have firstZero : ∀ offset : ℕ,
        (left [[-(offset : ℤ) - 1]]) ((right [[-power - 1 + offset]]) vector) = 0 := by
      intro offset
      have vanish : (right [[-power - 1 + offset]]) vector = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [lower] at small
        omega
      simp [vanish]
    have secondZero : ∀ offset : ℕ,
        (right [[-power - 1 - offset - 1]]) ((left [[offset]]) vector) = 0 := by
      intro offset
      by_cases within : offset ≤ cutoff
      · have inOrders : ((HahnModule.of ℂ).symm
            (right ((left [[offset]]) vector))).order - offset - 1 ∈ orders := by
          exact Finset.mem_image.mpr ⟨offset, Finset.mem_range.mpr (by omega), rfl⟩
        have bound := Finset.min'_le orders _ inOrders
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [lower] at small
        omega
      · have vanish : (left [[offset]]) vector = 0 := by
          apply VertexOperator.ncoeff_eq_zero_of_lt_order
          dsimp [cutoff] at within
          omega
        simp [vanish]
    exact member (by simp [coefficient, firstZero, secondZero])
  refine ⟨VertexOperator.of_coeff (fun power => coefficient (-power - 1)) bounded, ?_⟩
  intro index vector
  rw [VertexOperator.ncoeff_of_coeff]
  rw [show -(-index - 1) - 1 = index by omega]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem normalMinusOne_translation (translation : Module.End ℂ V)
    (left right : VertexOperator ℂ V)
    (leftLaw : ∀ index : ℤ,
      translation * (left [[index]]) - (left [[index]]) * translation =
        -(index : ℂ) • (left [[index - 1]]))
    (rightLaw : ∀ index : ℤ,
      translation * (right [[index]]) - (right [[index]]) * translation =
        -(index : ℂ) • (right [[index - 1]])) (index : ℤ) :
    translation * ((normalMinusOne left right).1 [[index]]) -
        ((normalMinusOne left right).1 [[index]]) * translation =
      -(index : ℂ) • ((normalMinusOne left right).1 [[index - 1]]) := by
  classical
  have forwardFinite (first second : VertexOperator ℂ V) (start finish : ℤ) (vector : V) :
      Function.HasFiniteSupport
        (fun offset : ℕ => (first [[start - offset]]) ((second [[finish + offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (second vector)).order - finish).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (second [[finish + offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  have reverseFinite (first second : VertexOperator ℂ V) (start : ℤ) (vector : V) :
      Function.HasFiniteSupport
        (fun offset : ℕ => (first [[start - offset]]) ((second [[offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (second vector)).order - 1).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (second [[offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  let zeroSucc : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some offset => offset + 1
    invFun value := match value with | 0 => none | offset + 1 => some offset
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  have shiftSum (term : ℕ → V) (finite : Function.HasFiniteSupport term) (atZero : term 0 = 0) :
      ∑ᶠ offset : ℕ, term offset = ∑ᶠ offset : ℕ, term (offset + 1) := by
    rw [← finsum_comp_equiv zeroSucc]
    rw [finsum_option]
    · simp [zeroSucc, atZero]
    · change Function.HasFiniteSupport (fun offset : ℕ => term (offset + 1))
      exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1)
        (fun first second equality => Nat.add_right_cancel equality)
  have productLaw (first second : ℤ) :
      translation * ((left [[first]]) * (right [[second]])) -
          ((left [[first]]) * (right [[second]])) * translation =
        -(first : ℂ) • ((left [[first - 1]]) * (right [[second]])) +
        -(second : ℂ) • ((left [[first]]) * (right [[second - 1]])) := by
    calc
      _ = (translation * (left [[first]]) - (left [[first]]) * translation) *
          (right [[second]]) + (left [[first]]) *
          (translation * (right [[second]]) - (right [[second]]) * translation) := by
            noncomm_ring
      _ = _ := by
        rw [leftLaw, rightLaw]
        simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  have reverseLaw (first second : ℤ) :
      translation * ((right [[first]]) * (left [[second]])) -
          ((right [[first]]) * (left [[second]])) * translation =
        -(first : ℂ) • ((right [[first - 1]]) * (left [[second]])) +
        -(second : ℂ) • ((right [[first]]) * (left [[second - 1]])) := by
    calc
      _ = (translation * (right [[first]]) - (right [[first]]) * translation) *
          (left [[second]]) + (right [[first]]) *
          (translation * (left [[second]]) - (left [[second]]) * translation) := by
            noncomm_ring
      _ = _ := by
        rw [rightLaw, leftLaw]
        simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  apply LinearMap.ext
  intro vector
  let firstTerm (offset : ℕ) : V :=
    ((offset : ℂ) + 1) • (left [[-(offset : ℤ) - 2]]) ((right [[index + offset]]) vector)
  let secondTerm (offset : ℕ) : V :=
    -((index : ℂ) + offset) •
      (left [[-(offset : ℤ) - 1]]) ((right [[index + offset - 1]]) vector)
  let thirdTerm (offset : ℕ) : V :=
    -((index : ℂ) - offset - 1) • (right [[index - offset - 2]]) ((left [[offset]]) vector)
  let fourthTerm (offset : ℕ) : V :=
    -(offset : ℂ) • (right [[index - offset - 1]]) ((left [[(offset : ℤ) - 1]]) vector)
  have forwardReindex (offset : ℕ) : (-1 : ℤ) - offset = -(offset : ℤ) - 1 := by omega
  have reverseReindex (offset : ℕ) : index - 2 - offset = index - offset - 2 := by omega
  have finiteFirst : Function.HasFiniteSupport firstTerm := by
    have finite := (forwardFinite left right (-2) index vector).smul_right
      (fun offset : ℕ => (offset : ℂ) + 1)
    simpa only [Pi.smul_def', firstTerm,
      show ∀ offset : ℕ, (-2 : ℤ) - offset = -(offset : ℤ) - 2 by
      intro offset; omega] using finite
  have finiteSecond : Function.HasFiniteSupport secondTerm := by
    have finite := (forwardFinite left right (-1) (index - 1) vector).smul_right
      (fun offset : ℕ => -((index : ℂ) + offset))
    simpa only [Pi.smul_def', secondTerm, sub_add_eq_add_sub, forwardReindex] using finite
  have finiteThird : Function.HasFiniteSupport thirdTerm := by
    have finite := (reverseFinite right left (index - 2) vector).smul_right
      (fun offset : ℕ => -((index : ℂ) - offset - 1))
    simpa only [Pi.smul_def', thirdTerm, reverseReindex] using finite
  have finiteFourth : Function.HasFiniteSupport fourthTerm := by
    refine (((reverseFinite right left (index - 2) vector).image
      (fun offset => offset + 1)).insert 0).subset ?_
    intro offset member
    cases offset with
    | zero => simp
    | succ offset =>
      apply Set.mem_insert_of_mem
      refine ⟨offset, ?_, rfl⟩
      intro vanish
      apply member
      simp only [fourthTerm, Nat.cast_add, Nat.cast_one]
      rw [show index - ((offset : ℤ) + 1) - 1 = index - 2 - offset by omega,
        show (offset : ℤ) + 1 - 1 = offset by omega]
      change -(offset + 1 : ℂ) •
        (right [[index - 2 - offset]]) ((left [[offset]]) vector) = 0
      change (right [[index - 2 - offset]]) ((left [[offset]]) vector) = 0 at vanish
      rw [vanish, smul_zero]
  have commuteSum (terms : ℕ → Module.End ℂ V)
      (finite : ∀ input, Function.HasFiniteSupport (fun offset => terms offset input)) :
      translation (∑ᶠ offset, terms offset vector) -
        ∑ᶠ offset, terms offset (translation vector) =
        ∑ᶠ offset, (translation * terms offset - terms offset * translation) vector := by
    rw [map_finsum translation (finite vector),
      ← finsum_sub_distrib ((finite vector).fun_comp (map_zero translation))
        (finite (translation vector))]
    rfl
  have expansion :
      (translation * ((normalMinusOne left right).1 [[index]]) -
          ((normalMinusOne left right).1 [[index]]) * translation) vector =
        (∑ᶠ offset, firstTerm offset) + (∑ᶠ offset, secondTerm offset) +
          ((∑ᶠ offset, thirdTerm offset) + (∑ᶠ offset, fourthTerm offset)) := by
    change translation (((normalMinusOne left right).1 [[index]]) vector) -
      ((normalMinusOne left right).1 [[index]]) (translation vector) = _
    rw [(normalMinusOne left right).2, (normalMinusOne left right).2, map_add]
    rw [show ∀ first second third fourth : V,
      (first + second) - (third + fourth) = (first - third) + (second - fourth) by
        intros; abel]
    have firstCommute := commuteSum
      (fun offset => (left [[-(offset : ℤ) - 1]]) * (right [[index + offset]]))
        (by
          intro input
          simpa only [Module.End.mul_apply,
            show ∀ offset : ℕ, (-1 : ℤ) - offset = -(offset : ℤ) - 1 by intro offset; omega]
            using (forwardFinite left right (-1) index input))
    have secondCommute := commuteSum
      (fun offset => (right [[index - offset - 1]]) * (left [[offset]]))
        (by
          intro input
          simpa only [Module.End.mul_apply,
            show ∀ offset : ℕ, index - 1 - offset = index - offset - 1 by intro offset; omega]
            using (reverseFinite right left (index - 1) input))
    change translation (∑ᶠ offset : ℕ,
      (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) -
      (∑ᶠ offset : ℕ,
        (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) (translation vector))) = _
      at firstCommute
    change translation (∑ᶠ offset : ℕ,
      (right [[index - offset - 1]]) ((left [[offset]]) vector)) -
      (∑ᶠ offset : ℕ,
        (right [[index - offset - 1]]) ((left [[offset]]) (translation vector))) = _
      at secondCommute
    rw [firstCommute, secondCommute]
    simp_rw [productLaw, reverseLaw, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, Int.cast_natCast]
    have firstEquality (offset : ℕ) :
        -((-(offset : ℤ) - 1 : ℤ) : ℂ) •
          (left [[-(offset : ℤ) - 1 - 1]]) ((right [[index + offset]]) vector) +
        -((index + offset : ℤ) : ℂ) •
          (left [[-(offset : ℤ) - 1]]) ((right [[index + offset - 1]]) vector) =
        firstTerm offset + secondTerm offset := by
      dsimp [firstTerm, secondTerm]
      rw [show -(offset : ℤ) - 1 - 1 = -(offset : ℤ) - 2 by omega]
      simp only [Int.cast_neg, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [show -(-(offset : ℂ) - 1) = (offset : ℂ) + 1 by ring]
    have secondEquality (offset : ℕ) :
        -((index - offset - 1 : ℤ) : ℂ) •
          (right [[index - offset - 1 - 1]]) ((left [[offset]]) vector) +
        -(offset : ℂ) •
          (right [[index - offset - 1]]) ((left [[(offset : ℤ) - 1]]) vector) =
        thirdTerm offset + fourthTerm offset := by
      dsimp [thirdTerm, fourthTerm]
      rw [show index - (offset : ℤ) - 1 - 1 = index - offset - 2 by omega]
      simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    simp only [firstEquality, secondEquality]
    rw [finsum_add_distrib finiteFirst finiteSecond,
      finsum_add_distrib finiteThird finiteFourth]
  have firstShift : (∑ᶠ offset, firstTerm offset) =
      ∑ᶠ offset : ℕ, (offset : ℂ) •
        (left [[-(offset : ℤ) - 1]]) ((right [[index + offset - 1]]) vector) := by
    let shifted (offset : ℕ) := (offset : ℂ) •
      (left [[-(offset : ℤ) - 1]]) ((right [[index + offset - 1]]) vector)
    have finite : Function.HasFiniteSupport shifted := by
      simpa only [shifted, Pi.smul_def', sub_add_eq_add_sub, forwardReindex] using
        ((forwardFinite left right (-1) (index - 1) vector).smul_right
          (fun offset : ℕ => (offset : ℂ)))
    rw [shiftSum shifted finite (by simp [shifted])]
    apply finsum_congr
    intro offset
    dsimp [shifted, firstTerm]
    rw [Nat.cast_add, Nat.cast_one,
      show -((offset : ℤ) + 1) - 1 = -(offset : ℤ) - 2 by omega,
      show index + ((offset : ℤ) + 1) - 1 = index + offset by omega]
  have fourthShift : (∑ᶠ offset, fourthTerm offset) =
      ∑ᶠ offset : ℕ, -((offset : ℂ) + 1) •
        (right [[index - offset - 2]]) ((left [[offset]]) vector) := by
    rw [shiftSum fourthTerm finiteFourth (by simp [fourthTerm])]
    apply finsum_congr
    intro offset
    dsimp [fourthTerm]
    rw [Nat.cast_add, Nat.cast_one,
      show index - ((offset : ℤ) + 1) - 1 = index - offset - 2 by omega,
      show (offset : ℤ) + 1 - 1 = offset by omega]
  rw [expansion, firstShift, fourthShift]
  rw [← finsum_add_distrib
      (by simpa only [Pi.smul_def', sub_add_eq_add_sub, forwardReindex] using
        ((forwardFinite left right (-1) (index - 1) vector).smul_right
          (fun offset : ℕ => (offset : ℂ))))
      finiteSecond,
    ← finsum_add_distrib finiteThird
      (by simpa only [Pi.smul_def', reverseReindex] using
        ((reverseFinite right left (index - 2) vector).smul_right
          (fun offset : ℕ => -((offset : ℂ) + 1))))]
  simp only [secondTerm, thirdTerm]
  simp_rw [← add_smul, show ∀ offset : ℕ, (offset : ℂ) + -((index : ℂ) + offset) =
      -(index : ℂ) by intro offset; ring,
    show ∀ offset : ℕ, -((index : ℂ) - offset - 1) + -((offset : ℂ) + 1) =
      -(index : ℂ) by intro offset; ring]
  rw [← smul_finsum' (-(index : ℂ))
      (by simpa only [sub_add_eq_add_sub, forwardReindex]
        using (forwardFinite left right (-1) (index - 1) vector)),
    ← smul_finsum' (-(index : ℂ))
      (by simpa only [reverseReindex] using (reverseFinite right left (index - 2) vector)),
    ← smul_add]
  change _ = -(index : ℂ) • ((normalMinusOne left right).1 [[index - 1]]) vector
  rw [(normalMinusOne left right).2]
  congr 2
  · apply finsum_congr
    intro offset
    rw [show index - 1 + offset = index + offset - 1 by omega]
  · apply finsum_congr
    intro offset
    rw [show index - 1 - offset - 1 = index - offset - 2 by omega]

end D5.S3.VertexAlgebra.FieldNormalProduct
