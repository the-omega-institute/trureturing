/- GID: D5/S3/Quantum/Fermionic/BcGhostStateField
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostStateField
   mirror-E: none(waiver:algebraic-ghost-state-fields)
   anchors: []
   utility: none
   digest: Signed ordered fields on every actual finite occupation ghost state. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The pointwise finite normal-product construction below adapts
D5.S3.VertexAlgebra.FieldNormalProduct (ScottCarnahan/vertexAlg,
revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea), with a scalar in the
reverse-ordered half. The ghost word construction uses the original occupation
carrier, not a transported vertex algebra. The intended all-state locality and
signed iterate theorem remain separate obligations until proved below.
-/

/-
proof_shape: stateField_creation, stateField_translation, stateField_parity: content
escape_witness: Sorted actual occupation creators and signed normal products construct
all coefficients. Finite-support telescopes give creation and original translation;
actual CAR parity extends to arbitrary finite state sums.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostVirasoro
import D5.S3.VertexAlgebra.FieldNormalProduct
import Mathlib.Data.Finset.Sort

/-! Actual ghost fields, signed normal ordering and the occupation basis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.VertexAlgebra.FieldNormalProduct

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostStateField

private noncomputable def signedNormalMinusOne (sign : ℂ) (left right : VertexOperator ℂ Fock) :
    {operator : VertexOperator ℂ Fock // ∀ index vector,
      (operator [[index]]) vector =
        (∑ᶠ offset : ℕ, (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) +
        sign • (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))} := by
  classical
  have leftFinite (index : ℤ) (vector : Fock) : Function.HasFiniteSupport
      (fun offset : ℕ => (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (right vector)).order - index).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (right [[index + offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  have rightFinite (index : ℤ) (vector : Fock) : Function.HasFiniteSupport
      (fun offset : ℕ => (right [[index - offset - 1]]) ((left [[offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (left vector)).order - 1).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (left [[offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  let coefficient (index : ℤ) : Module.End ℂ Fock := {
    toFun vector :=
      (∑ᶠ offset : ℕ, (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) +
      sign • (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))
    map_add' first second := by
      simp only [map_add]
      rw [finsum_add_distrib (leftFinite index first) (leftFinite index second),
        finsum_add_distrib (rightFinite index first) (rightFinite index second)]
      module
    map_smul' scalar vector := by
      simp only [map_smul]
      rw [← smul_finsum' scalar (leftFinite index vector),
        ← smul_finsum' scalar (rightFinite index vector)]
      simp only [RingHom.id_apply, id_eq]
      module }
  have bounded (vector : Fock) :
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

private theorem signedNormal_translation (sign : ℂ) (translation : Module.End ℂ Fock)
    (left right : VertexOperator ℂ Fock)
    (leftLaw : ∀ index : ℤ,
      translation * (left [[index]]) - (left [[index]]) * translation =
        -(index : ℂ) • (left [[index - 1]]))
    (rightLaw : ∀ index : ℤ,
      translation * (right [[index]]) - (right [[index]]) * translation =
        -(index : ℂ) • (right [[index - 1]])) (index : ℤ) :
    translation * ((signedNormalMinusOne sign left right).1 [[index]]) -
        ((signedNormalMinusOne sign left right).1 [[index]]) * translation =
      -(index : ℂ) • ((signedNormalMinusOne sign left right).1 [[index - 1]]) := by
  classical
  have forwardFinite (first second : VertexOperator ℂ Fock) (start finish : ℤ) (vector : Fock) :
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
  have reverseFinite (first second : VertexOperator ℂ Fock) (start : ℤ) (vector : Fock) :
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
  have shiftSum (term : ℕ → Fock) (finite : Function.HasFiniteSupport term) (atZero : term 0 = 0) :
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
  let firstTerm (offset : ℕ) : Fock :=
    ((offset : ℂ) + 1) • (left [[-(offset : ℤ) - 2]]) ((right [[index + offset]]) vector)
  let secondTerm (offset : ℕ) : Fock :=
    -((index : ℂ) + offset) •
      (left [[-(offset : ℤ) - 1]]) ((right [[index + offset - 1]]) vector)
  let thirdTerm (offset : ℕ) : Fock :=
    -((index : ℂ) - offset - 1) • (right [[index - offset - 2]]) ((left [[offset]]) vector)
  let fourthTerm (offset : ℕ) : Fock :=
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
  have commuteSum (terms : ℕ → Module.End ℂ Fock)
      (finite : ∀ input, Function.HasFiniteSupport (fun offset => terms offset input)) :
      translation (∑ᶠ offset, terms offset vector) -
        ∑ᶠ offset, terms offset (translation vector) =
        ∑ᶠ offset, (translation * terms offset - terms offset * translation) vector := by
    rw [map_finsum translation (finite vector),
      ← finsum_sub_distrib ((finite vector).fun_comp (map_zero translation))
        (finite (translation vector))]
    rfl
  have expansion :
      (translation * ((signedNormalMinusOne sign left right).1 [[index]]) -
          ((signedNormalMinusOne sign left right).1 [[index]]) * translation) vector =
        (∑ᶠ offset, firstTerm offset) + (∑ᶠ offset, secondTerm offset) +
          sign • ((∑ᶠ offset, thirdTerm offset) + (∑ᶠ offset, fourthTerm offset)) := by
    change translation (((signedNormalMinusOne sign left right).1 [[index]]) vector) -
      ((signedNormalMinusOne sign left right).1 [[index]]) (translation vector) = _
    rw [(signedNormalMinusOne sign left right).2, (signedNormalMinusOne sign left right).2, map_add, map_smul]
    rw [show ∀ first second third fourth : Fock,
      (first + sign • second) - (third + sign • fourth) =
        (first - third) + sign • (second - fourth) by intros; module]
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
    ]
  change _ = -(index : ℂ) • ((signedNormalMinusOne sign left right).1 [[index - 1]]) vector
  rw [(signedNormalMinusOne sign left right).2]
  rw [smul_add, smul_comm sign (-(index : ℂ))]
  congr 1
  · congr 1
    apply finsum_congr
    intro offset
    rw [show index - 1 + offset = index + offset - 1 by omega]
  · congr 2
    apply finsum_congr
    intro offset
    rw [show index - 1 - offset - 1 = index - offset - 2 by omega]


private def generatingMode (species : Bool) (n : ℤ) : Module.End ℂ Fock :=
  if species then c (n + 2) else b (n - 1)

private theorem generating_ket_tail (species : Bool) (S : Finset ℕ) (n : ℤ)
    (hn : ((S.sup id : ℕ) : ℤ) + 3 ≤ n) : generatingMode species n (ket S) = 0 := by
  have hbound (j : ℕ) (hj : j ∈ S) : j ≤ S.sup id := Finset.le_sup (f := id) hj
  cases species
  · have hcut : ¬n - 1 ≤ -2 := by omega
    have hsite : 2 * n.toNat + 1 ∉ S := by
      intro h
      have := hbound _ h
      omega
    simp [generatingMode, b, hcut, annihilate_ket, hsite]
  · have hcut : ¬n + 2 ≤ 1 := by omega
    have hsite : 2 * n.toNat ∉ S := by
      intro h
      have := hbound _ h
      omega
    simp [generatingMode, c, hcut, annihilate_ket, hsite]

private theorem generating_tail (species : Bool) (v : Fock) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → generatingMode species n v = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add v w hv hw =>
    obtain ⟨Nv, hv⟩ := hv
    obtain ⟨Nw, hw⟩ := hw
    exact ⟨max Nv Nw, fun n hn => by
      rw [map_add, hv n (by omega), hw n (by omega), add_zero]⟩
  | single S a =>
    refine ⟨S.sup id + 3, ?_⟩
    intro n hn
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs, map_smul, generating_ket_tail species S n (by exact_mod_cast hn), smul_zero]

private def generatingField (species : Bool) : VertexOperator ℂ Fock :=
  VertexOperator.of_coeff (fun power => generatingMode species (-power - 1)) (by
    intro v
    obtain ⟨N, hN⟩ := generating_tail species v
    refine ⟨-(N : ℤ) - 1, ?_⟩
    intro power member
    by_contra h
    exact member (hN (-power - 1) (by omega)))

private theorem generating_modes (species : Bool) (n : ℤ) :
    ((generatingField species) [[n]]) = generatingMode species n := by
  rw [generatingField, VertexOperator.ncoeff_of_coeff]
  congr 1
  omega

/-- Sorted occupation sites are physical divided derivatives: even sites are b,
odd sites are c. Each step has the sign of two odd homogeneous factors exactly
when the tail contains an odd number of sites. -/
private def wordField : List ℕ → VertexOperator ℂ Fock
  | [] => identityField
  | j :: tail =>
    (signedNormalMinusOne ((-1 : ℂ) ^ tail.length)
      (dividedDerivative (j / 2) (generatingField (j % 2 == 1))) (wordField tail)).1

/-- The actual linear state-field map on the entire finite-occupation carrier. -/
def Y : Fock →ₗ[ℂ] VertexOperator ℂ Fock :=
  Finsupp.lsum ℂ fun S => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (wordField S.sort)

private theorem Y_ket (S : Finset ℕ) : Y (ket S) = wordField S.sort := by
  simp [Y, ket]

private theorem derivative_modes (species : Bool) (order : ℕ) (n : ℤ) :
    ((dividedDerivative order (generatingField species)) [[n]]) =
      ((Ring.choose (-n - 1 + order) order : ℤ) : ℂ) • generatingMode species (n - order) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-n - 1 + order) order •
    HVertexOperator.coeff (generatingField species) (-n - 1 + order) v = _
  rw [VertexOperator.coeff_eq_ncoeff, generating_modes]
  rw [show -(-n - 1 + order) - 1 = n - order by omega]
  simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]

private theorem derivative_creative (species : Bool) (order : ℕ) (n : ℤ)
    (hn : 0 ≤ n) :
    ((dividedDerivative order (generatingField species)) [[n]]) vacuum = 0 := by
  rw [derivative_modes, LinearMap.smul_apply]
  by_cases large : (order : ℤ) ≤ n
  · have hvac : generatingMode species (n - order) vacuum = 0 := by
      cases species
      · exact ghost_vacuum.1 _ (by omega)
      · exact ghost_vacuum.2.1 _ (by omega)
    rw [hvac, smul_zero]
  · have positive : 0 ≤ -n - 1 + (order : ℤ) := by omega
    obtain ⟨number, equality⟩ := Int.eq_ofNat_of_zero_le positive
    have smaller : number < order := by omega
    rw [equality, Ring.choose_natCast, Nat.choose_eq_zero_of_lt smaller]
    simp

private theorem site_creation (j : ℕ) :
    ((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[-1]]) = create j := by
  rw [derivative_modes]
  norm_num only [neg_neg, sub_self, zero_add, Ring.choose_natCast, Nat.choose_self,
    Int.cast_one, one_smul]
  by_cases he : j % 2 = 0
  · have hj : j = 2 * (j / 2) := by omega
    have hspecies : (j % 2 == 1) = false := by simp [he]
    simp only [hspecies, generatingMode, Bool.false_eq_true, ite_false]
    have hindex : (-1 : ℤ) - (j / 2 : ℕ) - 1 = -(j / 2 : ℕ) - 2 := by omega
    rw [hindex, (mode_correspondence (j / 2)).1, ← hj]
  · have hj : j = 2 * (j / 2) + 1 := by omega
    have hspecies : (j % 2 == 1) = true := by simp [show j % 2 = 1 by omega]
    simp only [hspecies, generatingMode, ite_true]
    have hindex : (-1 : ℤ) - (j / 2 : ℕ) + 2 = 1 - (j / 2 : ℕ) := by omega
    rw [hindex, (mode_correspondence (j / 2)).2.2.1, ← hj]

private theorem word_vacuum (w : List ℕ) :
    ((wordField w) [[-1]]) vacuum = word (w.map (fun j => (j, true))) vacuum ∧
    ∀ n : ℤ, 0 ≤ n → ((wordField w) [[n]]) vacuum = 0 := by
  have identityModes (n : ℤ) : ((identityField : VertexOperator ℂ Fock) [[n]]) =
      if n = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -n - 1 = 0 ↔ n = -1 by omega]
  induction w with
  | nil =>
    constructor
    · simp [wordField, identityModes, word]
    · intro n hn
      simp [wordField, identityModes, show n ≠ -1 by omega]
  | cons j tail ih =>
    have coefficient (n : ℤ) := (signedNormalMinusOne ((-1 : ℂ) ^ tail.length)
      (dividedDerivative (j / 2) (generatingField (j % 2 == 1))) (wordField tail)).2 n vacuum
    constructor
    · rw [wordField, coefficient]
      have secondZero : ∀ i : ℕ,
          ((wordField tail) [[-1 - i - 1]])
            (((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[i]]) vacuum) = 0 := by
        intro i
        rw [derivative_creative _ _ _ (by omega), map_zero]
      simp only [secondZero, finsum_zero, smul_zero, add_zero]
      rw [finsum_eq_single _ 0]
      · simp only [Nat.cast_zero, neg_zero, zero_sub, add_zero, site_creation, ih.1,
          List.map_cons, word, mode, ite_true, Module.End.mul_apply]
      · intro i hi
        rw [ih.2 (-1 + i) (by omega), map_zero]
    · intro n hn
      rw [wordField, coefficient]
      have firstZero : ∀ i : ℕ,
          ((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[-(i : ℤ) - 1]])
            (((wordField tail) [[n + i]]) vacuum) = 0 := by
        intro i
        rw [ih.2 _ (by omega), map_zero]
      have secondZero : ∀ i : ℕ,
          ((wordField tail) [[n - i - 1]])
            (((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[i]]) vacuum) = 0 := by
        intro i
        rw [derivative_creative _ _ _ (by omega), map_zero]
      simp [firstZero, secondZero]

private theorem sorted_creator_vacuum (S : Finset ℕ) :
    word (S.sort.map (fun j => (j, true))) vacuum = ket S := by
  classical
  induction S using Finset.eraseInduction with
  | H S ih =>
    by_cases empty : S = ∅
    · subst S
      simp [word, vacuum]
    · have hS := Finset.nonempty_iff_ne_empty.mpr empty
      let j := S.min' hS
      have hj : j ∈ S := Finset.min'_mem S hS
      have hnot : j ∉ S.erase j := Finset.notMem_erase j S
      have hbound : ∀ k ∈ S.erase j, j ≤ k := by
        intro k hk
        exact Finset.min'_le S k (Finset.mem_of_mem_erase hk)
      have hsort : S.sort = j :: (S.erase j).sort := by
        conv_lhs => rw [← Finset.insert_erase hj]
        exact Finset.sort_insert (· ≤ ·) hbound hnot
      have hphase : phase j (S.erase j) = 1 := by
        have hz : (S.erase j).filter (· < j) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro k hk
          obtain ⟨hk, hkj⟩ := Finset.mem_filter.mp hk
          exact (not_lt_of_ge (hbound k hk)) hkj
        simp [phase, lowerCount, hz]
      rw [hsort, List.map_cons, word, Module.End.mul_apply, mode, if_pos rfl,
        ih j hj, create_ket, if_neg hnot, hphase, one_smul, Finset.insert_erase hj]

/-- Every actual finite occupation is created, and all nonnegative modes kill
its vacuum. The generating states use the original physical mode shifts. -/
theorem stateField_creation :
    Y vacuum = identityField ∧
    (∀ a : Fock, ((Y a) [[-1]]) vacuum = a) ∧
    (∀ (a : Fock) (n : ℤ), 0 ≤ n → ((Y a) [[n]]) vacuum = 0) ∧
    (∀ n : ℤ, ((Y (ket {0})) [[n]]) = b (n - 1)) ∧
    (∀ n : ℤ, ((Y (ket {1})) [[n]]) = c (n + 2)) := by
  classical
  have hcreation (a : Fock) : ((Y a) [[-1]]) vacuum = a := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa [map_add, ha, hb]
    | single S z =>
      have hs : Finsupp.single S z = z • ket S := by simp [ket]
      rw [hs, map_smul]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, Y_ket, (word_vacuum S.sort).1,
        sorted_creator_vacuum]
  have hcreative (a : Fock) (n : ℤ) (hn : 0 ≤ n) : ((Y a) [[n]]) vacuum = 0 := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa [map_add, ha, hb]
    | single S z =>
      have hs : Finsupp.single S z = z • ket S := by simp [ket]
      rw [hs, map_smul]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, Y_ket, (word_vacuum S.sort).2 n hn,
        smul_zero]
  have rightIdentity (A : VertexOperator ℂ Fock) :
      (signedNormalMinusOne 1 A identityField).1 = A := by
    apply HVertexOperator.coeff_inj
    funext power
    apply LinearMap.ext
    intro v
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
      (signedNormalMinusOne 1 A identityField).2]
    simp only [one_smul]
    have identityModes (n : ℤ) : ((identityField : VertexOperator ℂ Fock) [[n]]) =
        if n = -1 then LinearMap.id else 0 := by
      rw [identityField, VertexOperator.ncoeff_of_coeff]
      simp only [show -n - 1 = 0 ↔ n = -1 by omega]
    let index : ℤ := -power - 1
    change (∑ᶠ offset : ℕ, (A [[-(offset : ℤ) - 1]])
        (((identityField : VertexOperator ℂ Fock) [[index + offset]]) v)) +
      (∑ᶠ offset : ℕ, ((identityField : VertexOperator ℂ Fock) [[index - offset - 1]])
        ((A [[offset]]) v)) = (A [[index]]) v
    by_cases positive : 0 ≤ index
    · have firstZero : ∀ offset : ℕ,
          (A [[-(offset : ℤ) - 1]])
            (((identityField : VertexOperator ℂ Fock) [[index + offset]]) v) = 0 := by
        intro offset
        simp [identityModes, show index + offset ≠ -1 by omega]
      simp only [firstZero, finsum_zero, zero_add]
      rw [finsum_eq_single _ index.toNat]
      · simp [identityModes, Int.toNat_of_nonneg positive]
      · intro offset distinct
        have different : index - (offset : ℤ) - 1 ≠ -1 := by omega
        simp [identityModes, different]
    · have secondZero : ∀ offset : ℕ,
          ((identityField : VertexOperator ℂ Fock) [[index - offset - 1]])
            ((A [[offset]]) v) = 0 := by
        intro offset
        simp [identityModes, show index - offset - 1 ≠ -1 by omega]
      simp only [secondZero, finsum_zero, add_zero]
      rw [finsum_eq_single _ (-index - 1).toNat]
      · have nonnegative : 0 ≤ -index - 1 := by omega
        rw [identityModes, Int.toNat_of_nonneg nonnegative,
          if_pos (by omega)]
        simp only [LinearMap.id_apply]
        rw [show -(-index - 1) - 1 = index by omega]
      · intro offset distinct
        have different : index + (offset : ℤ) ≠ -1 := by omega
        simp [identityModes, different]
  refine ⟨by simp [vacuum, Y_ket, wordField], hcreation, hcreative, ?_, ?_⟩
  · intro n
    have hY : Y (ket {0}) = generatingField false := by
      rw [Y_ket]
      simp only [Finset.sort_singleton, wordField, List.length_nil, pow_zero]
      change (signedNormalMinusOne 1 (dividedDerivative 0 (generatingField _)) identityField).1 = _
      rw [rightIdentity]
      apply VertexOperator.ext
      intro v
      simp [dividedDerivative]
    rw [hY, generating_modes]
    rfl
  · intro n
    have hY : Y (ket {1}) = generatingField true := by
      rw [Y_ket]
      simp only [Finset.sort_singleton, wordField, List.length_nil, pow_zero]
      change (signedNormalMinusOne 1 (dividedDerivative 0 (generatingField _)) identityField).1 = _
      rw [rightIdentity]
      apply VertexOperator.ext
      intro v
      simp [dividedDerivative]
    rw [hY, generating_modes]
    rfl

open private L_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro

set_option maxHeartbeats 800000 in
-- The finite-sum telescope and linear extension share this declaration's budget.
/-- The translation is the original ghost Virasoro minus-one mode. -/
theorem stateField_translation :
    BcGhostVirasoro.L (-1) vacuum = 0 ∧ ∀ (a : Fock) (n : ℤ),
      BcGhostVirasoro.L (-1) * ((Y a) [[n]]) -
          ((Y a) [[n]]) * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • ((Y a) [[n - 1]]) := by
  classical
  have generatorLaw (species : Bool) (n : ℤ) :
      BcGhostVirasoro.L (-1) * generatingMode species n -
          generatingMode species n * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • generatingMode species (n - 1) := by
    cases species
    · have hi : (-1 : ℤ) - (n - 1) = -n := by omega
      have hj : (-1 : ℤ) + (n - 1) = n - 1 - 1 := by omega
      simpa only [generatingMode, Bool.false_eq_true, ite_false, hi, hj, Int.cast_neg] using
        BcGhostVirasoro.ward_b (-1) (n - 1)
    · have hi : (-2 : ℤ) * (-1) - (n + 2) = -n := by omega
      have hj : (-1 : ℤ) + (n + 2) = n - 1 + 2 := by omega
      simpa only [generatingMode, ite_true, hi, hj, Int.cast_neg] using
        BcGhostVirasoro.ward_c (-1) (n + 2)
  have binomialShift (argument : ℤ) (order : ℕ) :
      Ring.choose argument order * (argument - order) =
        argument * Ring.choose (argument - 1) order := by
    have first := Ring.choose_smul_choose argument (n := order + 1) (k := order) (by omega)
    have second := Ring.choose_smul_choose argument (n := order + 1) (k := 1) (by omega)
    rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] at first
    rw [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel] at second
    exact first.symm.trans second
  have derivativeLaw (species : Bool) (order : ℕ) (n : ℤ) :
      BcGhostVirasoro.L (-1) * ((dividedDerivative order (generatingField species)) [[n]]) -
          ((dividedDerivative order (generatingField species)) [[n]]) * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • ((dividedDerivative order (generatingField species)) [[n - 1]]) := by
    rw [derivative_modes, derivative_modes, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, ← smul_sub, generatorLaw, smul_smul]
    rw [show n - order - 1 = n - 1 - order by omega, smul_smul]
    have integerEquality := binomialShift (-n + order) order
    have complexEquality := congrArg (fun integer : ℤ => (integer : ℂ)) integerEquality
    push_cast at complexEquality
    have firstIndex : -n + (order : ℤ) - 1 = -n - 1 + order := by omega
    have secondIndex : -(n - 1) - 1 + (order : ℤ) = -n + order := by omega
    rw [firstIndex] at complexEquality
    rw [secondIndex]
    congr 1
    push_cast
    linear_combination -complexEquality
  have wordLaw : ∀ (w : List ℕ) (n : ℤ),
      BcGhostVirasoro.L (-1) * ((wordField w) [[n]]) -
          ((wordField w) [[n]]) * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • ((wordField w) [[n - 1]]) := by
    intro w
    induction w with
    | nil =>
      intro n
      have identityModes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
          if n = -1 then LinearMap.id else 0 := by
        rw [identityField, VertexOperator.ncoeff_of_coeff]
        simp only [show -n - 1 = 0 ↔ n = -1 by omega]
      simp only [wordField, identityModes]
      by_cases hz : n = 0
      · subst n
        simp
      · simp only [if_neg (show n - 1 ≠ -1 by omega), smul_zero]
        split_ifs <;> simp only [Module.End.mul_eq_comp, LinearMap.comp_id,
          LinearMap.id_comp, mul_zero, zero_mul, sub_self]
    | cons j tail ih =>
      intro n
      exact signedNormal_translation _ (BcGhostVirasoro.L (-1))
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
        (wordField tail) (derivativeLaw _ _) ih n
  refine ⟨?_, ?_⟩
  · rw [L_vacuum]
    norm_num
  · intro a n
    let defect : VertexOperator ℂ Fock →ₗ[ℂ] Module.End ℂ Fock := {
      toFun A := BcGhostVirasoro.L (-1) * (A [[n]]) - (A [[n]]) * BcGhostVirasoro.L (-1) +
        (n : ℂ) • (A [[n - 1]])
      map_add' A B := by
        simp only [map_add, Pi.add_apply, mul_add, add_mul, smul_add]
        abel
      map_smul' z A := by
        simp only [map_smul, RingHom.id_apply, Pi.smul_apply, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, ← smul_sub, ← smul_add, smul_comm (n : ℂ) z] }
    have defect_apply (A : VertexOperator ℂ Fock) : defect A =
        BcGhostVirasoro.L (-1) * (A [[n]]) - (A [[n]]) * BcGhostVirasoro.L (-1) +
          (n : ℂ) • (A [[n - 1]]) := rfl
    have heq : defect.comp Y = 0 := by
      apply Finsupp.lhom_ext
      intro S z
      have hs : Finsupp.single S z = z • ket S := by simp [ket]
      simp only [LinearMap.comp_apply, hs, map_smul, Y_ket, LinearMap.zero_apply]
      suffices hzero : defect (wordField S.sort) = 0 by rw [hzero, smul_zero]
      rw [defect_apply, wordLaw]
      simp only [neg_smul, neg_add_cancel]
    have hd (v : Fock) : defect (Y v) = 0 := LinearMap.congr_fun heq v
    have h := hd a
    rw [defect_apply] at h
    simpa only [neg_smul] using eq_neg_iff_add_eq_zero.mpr h

private theorem forward_finite (A B : VertexOperator ℂ Fock) (start finish : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun i : ℕ => (A [[start - i]]) ((B [[finish + i]]) v)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (B v)).order - finish).toNat, ?_⟩
  intro i hi
  contrapose! hi
  have hz : (B [[finish + i]]) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

private theorem reverse_finite (A B : VertexOperator ℂ Fock) (start : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun i : ℕ => (A [[start - i]]) ((B [[i]]) v)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (B v)).order - 1).toNat, ?_⟩
  intro i hi
  contrapose! hi
  have hz : (B [[i]]) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

private theorem signedNormal_parity (sign x y : ℂ) (A B : VertexOperator ℂ Fock)
    (hA : ∀ n : ℤ, parity * (A [[n]]) = x • ((A [[n]]) * parity))
    (hB : ∀ n : ℤ, parity * (B [[n]]) = y • ((B [[n]]) * parity)) (n : ℤ) :
    parity * ((signedNormalMinusOne sign A B).1 [[n]]) =
      (x * y) • (((signedNormalMinusOne sign A B).1 [[n]]) * parity) := by
  have hA' (m : ℤ) (w : Fock) : parity ((A [[m]]) w) = x • (A [[m]]) (parity w) :=
    LinearMap.congr_fun (hA m) w
  have hB' (m : ℤ) (w : Fock) : parity ((B [[m]]) w) = y • (B [[m]]) (parity w) :=
    LinearMap.congr_fun (hB m) w
  apply LinearMap.ext
  intro v
  change parity (((signedNormalMinusOne sign A B).1 [[n]]) v) =
    (x * y) • ((signedNormalMinusOne sign A B).1 [[n]]) (parity v)
  rw [(signedNormalMinusOne sign A B).2, (signedNormalMinusOne sign A B).2,
    map_add, map_smul]
  have hf (w : Fock) : Function.HasFiniteSupport
      (fun i : ℕ => (A [[-(i : ℤ) - 1]]) ((B [[n + i]]) w)) := by
    simpa only [show ∀ i : ℕ, (-1 : ℤ) - i = -(i : ℤ) - 1 by intro i; omega] using
      forward_finite A B (-1) n w
  have hr (w : Fock) : Function.HasFiniteSupport
      (fun i : ℕ => (B [[n - i - 1]]) ((A [[i]]) w)) := by
    simpa only [show ∀ i : ℕ, n - 1 - i = n - i - 1 by intro i; omega] using
      reverse_finite B A (n - 1) w
  rw [map_finsum parity (hf v), map_finsum parity (hr v)]
  simp_rw [hA', hB', hA', map_smul, smul_smul]
  rw [show y * x = x * y by ring,
    ← smul_finsum' (x * y) (hf (parity v)), ← smul_finsum' (x * y) (hr (parity v))]
  module

open D5.S3.Quantum.Fermionic.CountableOccupationFock (parity_ket)

/-- Parity compatibility holds on every state, including inhomogeneous sums. -/
theorem stateField_parity (a : Fock) (n : ℤ) :
    parity * ((Y a) [[n]]) = ((Y (parity a)) [[n]]) * parity := by
  classical
  have derivativeParity (species : Bool) (order : ℕ) (n : ℤ) :
      parity * ((dividedDerivative order (generatingField species)) [[n]]) =
        (-1 : ℂ) • (((dividedDerivative order (generatingField species)) [[n]]) * parity) := by
    have ho : parity * generatingMode species (n - order) =
        -(generatingMode species (n - order) * parity) := by
      cases species
      · exact eq_neg_of_add_eq_zero_left (ghost_parity (n - order - 1)).1
      · exact eq_neg_of_add_eq_zero_left (ghost_parity (n - order + 2)).2
    rw [derivative_modes, Algebra.mul_smul_comm, ho, Algebra.smul_mul_assoc]
    simp only [smul_neg, neg_one_smul]
  have wordParity : ∀ (w : List ℕ) (n : ℤ),
      parity * ((wordField w) [[n]]) =
        ((-1 : ℂ) ^ w.length) • (((wordField w) [[n]]) * parity) := by
    intro w
    induction w with
    | nil =>
      intro n
      have identityModes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
          if n = -1 then LinearMap.id else 0 := by
        rw [identityField, VertexOperator.ncoeff_of_coeff]
        simp only [show -n - 1 = 0 ↔ n = -1 by omega]
      simp only [wordField, List.length_nil, pow_zero, one_smul, identityModes]
      split_ifs <;> simp only [Module.End.mul_eq_comp, LinearMap.comp_id,
        LinearMap.id_comp, mul_zero, zero_mul]
    | cons j tail ih =>
      intro n
      have h := signedNormal_parity ((-1 : ℂ) ^ tail.length) (-1)
        ((-1 : ℂ) ^ tail.length)
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
        (wordField tail) (derivativeParity _ _) ih n
      simpa only [wordField, List.length_cons, pow_succ, mul_comm (-1 : ℂ)] using h
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, mul_add, add_mul, ha, hb]
  | single S z =>
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    simp only [hs, map_smul, Pi.smul_apply, parity_ket, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Y_ket, wordParity, Finset.length_sort, smul_smul]

end D5.S3.Quantum.Fermionic.BcGhostStateField
