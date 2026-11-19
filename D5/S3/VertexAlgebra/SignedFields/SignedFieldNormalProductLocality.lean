/- GID: D5/S3/VertexAlgebra/SignedFields/SignedFieldNormalProductLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SignedFields/SignedFieldNormalProductLocality
   mirror-E: none(waiver:algebraic-signed-field-calculus)
   anchors: []
   utility: none
   digest: Signed normal-product and divided-derivative locality on arbitrary complex modules. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The vectorwise finite-support construction follows the attributed vertexAlg
supplier in StateFieldResidueReconstruction. Signed pair calculations adapt
BcGhostStateFieldLocality to arbitrary complex modules. The original generic
PairSpace, shifts and residue cancellation are reused without re-proving them.
Classical source: Matsuo–Nagatomo, Dong locality. No novelty claim is made.
proof_shape: signedNormal_locality, signedDerivative_locality: content
admission_basis: escape-witness
escape_witness: Independent AB, AC and BC signs give a signed discrepancy;
its two polynomial annihilators feed the existing residue-cancellation kernel.
A finite-difference Leibniz identity controls every divided derivative.
-/

import D5.S3.VertexAlgebra.FieldNormalProductLocality
import Batteries.Tactic.OpenPrivate

/-! Vectorwise signed normal products and their polynomial locality. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open private shiftsCommute discrepancyXY intertwiningPowers cancellationBound from
  D5.S3.VertexAlgebra.FieldNormalProductLocality

noncomputable section
namespace D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

noncomputable def signedNormalMinusOne (sign : ℂ) (left right : VertexOperator ℂ V) :
    {operator : VertexOperator ℂ V // ∀ index vector,
      (operator [[index]]) vector =
        (∑ᶠ offset : ℕ, (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) +
        sign • (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))} := by
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
      simp only [RingHom.id_apply]
      module }
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

theorem forward_finite (A B : VertexOperator ℂ V) (start finish : ℤ) (v : V) :
    Function.HasFiniteSupport (fun i : ℕ => (A [[start - i]]) ((B [[finish + i]]) v)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (B v)).order - finish).toNat, ?_⟩
  intro i hi
  contrapose! hi
  have hz : (B [[finish + i]]) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

theorem reverse_finite (A B : VertexOperator ℂ V) (start : ℤ) (v : V) :
    Function.HasFiniteSupport (fun i : ℕ => (A [[start - i]]) ((B [[i]]) v)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (B v)).order - 1).toNat, ?_⟩
  intro i hi
  contrapose! hi
  have hz : (B [[i]]) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

def signedComm (s : ℂ) (A B : VertexOperator ℂ V) :
    ℤ → ℤ → Module.End ℂ V := fun m n =>
  (A [[m]]) * (B [[n]]) - s • ((B [[n]]) * (A [[m]]))

private def signedPairAC (s : ℂ) (first second third : VertexOperator ℂ V) (vector : V) : PairSpace V := by
  have increasingFinite (operator : VertexOperator ℂ V) (start : ℤ) (vector : V) :
      Function.HasFiniteSupport (fun offset : ℕ => (operator [[start + offset]]) vector) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (operator vector)).order - start).toNat, ?_⟩
    intro offset member
    contrapose! member
    rw [Function.notMem_support]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  exact ⟨(fun left middle right => signedComm s first third left right ((second [[middle]]) vector),
    fun left middle right => (second [[middle]]) (signedComm s first third left right vector)), by
    constructor
    · intro left middle right
      refine (increasingFinite second middle vector).subset ?_
      intro offset member vanish
      change (second [[middle + offset]]) vector = 0 at vanish
      apply member
      change signedComm s first third (left - offset) right
        ((second [[middle + offset]]) vector) = 0
      rw [vanish, map_zero]
    · intro left middle right
      have firstFinite := increasingFinite first left ((third [[right]]) vector)
      have secondFinite := (increasingFinite first left vector).comp
        ((third [[right]]).map_zero)
      have finite := firstFinite.sub (secondFinite.smul_right (fun _ => s))
      refine finite.subset ?_
      intro offset member vanish
      apply member
      have zero : signedComm s first third (left + offset) right vector = 0 := vanish
      change (second [[middle - offset]]) (signedComm s first third (left + offset) right vector) = 0
      rw [zero, map_zero]⟩

private def signedPairBC (s : ℂ) (first second third : VertexOperator ℂ V) (vector : V) : PairSpace V := by
  have increasingFinite (operator : VertexOperator ℂ V) (start : ℤ) (vector : V) :
      Function.HasFiniteSupport (fun offset : ℕ => (operator [[start + offset]]) vector) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (operator vector)).order - start).toNat, ?_⟩
    intro offset member
    contrapose! member
    rw [Function.notMem_support]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  exact ⟨(fun left middle right => (first [[left]]) (signedComm s second third middle right vector),
    fun left middle right => signedComm s second third middle right ((first [[left]]) vector)), by
    constructor
    · intro left middle right
      have firstFinite := increasingFinite second middle ((third [[right]]) vector)
      have secondFinite := (increasingFinite second middle vector).comp
        ((third [[right]]).map_zero)
      have finite := firstFinite.sub (secondFinite.smul_right (fun _ => s))
      refine finite.subset ?_
      intro offset member vanish
      apply member
      have zero : signedComm s second third (middle + offset) right vector = 0 := vanish
      change (first [[left - offset]]) (signedComm s second third (middle + offset) right vector) = 0
      rw [zero, map_zero]
    · intro left middle right
      refine (increasingFinite first left vector).subset ?_
      intro offset member vanish
      change (first [[left + offset]]) vector = 0 at vanish
      apply member
      change signedComm s second third (middle - offset) right
        ((first [[left + offset]]) vector) = 0
      rw [vanish, map_zero]⟩

private def twistPair (x y : ℂ) : Module.End ℂ (PairSpace V) where
  toFun pair := ⟨(x • pair.val.1, y • pair.val.2), by
    constructor
    · intro l m r
      exact (pair.property.1 l m r).smul_right (fun _ => x)
    · intro l m r
      exact (pair.property.2 l m r).smul_right (fun _ => y)⟩
  map_add' a b := by apply Subtype.ext; ext <;> simp [smul_add]
  map_smul' s a := by apply Subtype.ext; ext <;> simp [smul_smul, mul_comm s]

private theorem twistXY (x y : ℂ) (pair : PairSpace V) :
    twistPair x y (deltaXY pair) = deltaXY (twistPair x y pair) := by
  apply Subtype.ext
  ext <;> simp [twistPair, deltaXY, shiftXY, smul_sub]

private theorem twistYZ (x y : ℂ) (pair : PairSpace V) :
    twistPair x y (deltaYZ pair) = deltaYZ (twistPair x y pair) := by
  apply Subtype.ext
  ext <;> simp [twistPair, deltaYZ, shiftYZ, smul_sub]

private def signedTriple (x y z : ℂ) (A B C : VertexOperator ℂ V) (v : V) :
    PairSpace V :=
  twistPair z x (signedPairAC y A B C v) +
    twistPair 1 (x * y) (signedPairBC z A B C v)

private theorem signedTriple_coefficients (x y z : ℂ) (A B C : VertexOperator ℂ V)
    (v : V) (l m r : ℤ) :
    (signedTriple x y z A B C v).val.1 l m r =
      (A [[l]]) ((B [[m]]) ((C [[r]]) v)) -
        (y * z) • (C [[r]]) ((A [[l]]) ((B [[m]]) v)) ∧
    (signedTriple x y z A B C v).val.2 l m r =
      x • (B [[m]]) ((A [[l]]) ((C [[r]]) v)) -
        (x * y * z) • (C [[r]]) ((B [[m]]) ((A [[l]]) v)) := by
  constructor <;>
    simp only [signedTriple, signedPairAC, signedPairBC, twistPair, Submodule.coe_add,
      Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply, signedComm,
      LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sub,
      map_smul, smul_sub, smul_smul, one_smul] <;> module

private theorem signedPair_low (x y z : ℂ) (A B C : VertexOperator ℂ V) (v : V)
    (Na Nb : ℕ) (hAC : delta^[Na] (signedComm y A C) = 0)
    (hBC : delta^[Nb] (signedComm z B C) = 0) :
    (((deltaXY + deltaYZ) ^ Na * deltaYZ ^ Nb : Module.End ℂ (PairSpace V)))
      (signedTriple x y z A B C v) = 0 := by
  let combined : Module.End ℂ (PairSpace V) := deltaXY + deltaYZ
  let combinedPlain : Module.End ℂ (Triple V) := plainXY + plainYZ
  have firstProjection (value : PairSpace V) : projectionFirst (combined value) =
      combinedPlain (projectionFirst value) := rfl
  have secondProjection (value : PairSpace V) : projectionSecond (combined value) =
      combinedPlain (projectionSecond value) := rfl
  have projectionYZFirst (value : PairSpace V) : projectionFirst (deltaYZ value) =
      plainYZ (projectionFirst value) := rfl
  have projectionYZSecond (value : PairSpace V) : projectionSecond (deltaYZ value) =
      plainYZ (projectionSecond value) := rfl
  have acLaw (factor : Bool) (D : ℤ → ℤ → Module.End ℂ V) :
      liftAC B v factor (deltaEnd D) = combinedPlain (liftAC B v factor D) := by
    funext l m r
    dsimp [liftAC, deltaEnd, delta, combinedPlain, plainXY, plainYZ, shiftXY, shiftYZ]
    cases factor <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_sub] <;> abel
  have bcLaw (factor : Bool) (D : ℤ → ℤ → Module.End ℂ V) :
      liftBC A v factor (deltaEnd D) = plainYZ (liftBC A v factor D) := by
    funext l m r
    dsimp [liftBC, deltaEnd, delta, plainYZ, shiftYZ]
    cases factor <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_sub]
  have acKilled : (combined ^ Na) (signedPairAC y A B C v) = 0 := by
    apply Subtype.ext
    apply Prod.ext
    · change projectionFirst ((combined ^ Na) (signedPairAC y A B C v)) = 0
      rw [intertwiningPowers combined combinedPlain projectionFirst firstProjection]
      change (combinedPlain ^ Na) (liftAC B v true (signedComm y A C)) = 0
      rw [← intertwiningPowers deltaEnd combinedPlain (liftAC B v true) (acLaw true)]
      rw [Module.End.pow_apply]
      change liftAC B v true (delta^[Na] (signedComm y A C)) = 0
      rw [hAC, map_zero]
    · change projectionSecond ((combined ^ Na) (signedPairAC y A B C v)) = 0
      rw [intertwiningPowers combined combinedPlain projectionSecond secondProjection]
      change (combinedPlain ^ Na) (liftAC B v false (signedComm y A C)) = 0
      rw [← intertwiningPowers deltaEnd combinedPlain (liftAC B v false) (acLaw false)]
      rw [Module.End.pow_apply]
      change liftAC B v false (delta^[Na] (signedComm y A C)) = 0
      rw [hAC, map_zero]
  have bcKilled : (deltaYZ ^ Nb) (signedPairBC z A B C v) = 0 := by
    apply Subtype.ext
    apply Prod.ext
    · change projectionFirst ((deltaYZ ^ Nb) (signedPairBC z A B C v)) = 0
      rw [intertwiningPowers (deltaYZ (V := V)) plainYZ projectionFirst projectionYZFirst]
      change (plainYZ ^ Nb) (liftBC A v true (signedComm z B C)) = 0
      rw [← intertwiningPowers deltaEnd plainYZ (liftBC A v true) (bcLaw true)]
      rw [Module.End.pow_apply]
      change liftBC A v true (delta^[Nb] (signedComm z B C)) = 0
      rw [hBC, map_zero]
    · change projectionSecond ((deltaYZ ^ Nb) (signedPairBC z A B C v)) = 0
      rw [intertwiningPowers (deltaYZ (V := V)) plainYZ projectionSecond projectionYZSecond]
      change (plainYZ ^ Nb) (liftBC A v false (signedComm z B C)) = 0
      rw [← intertwiningPowers deltaEnd plainYZ (liftBC A v false) (bcLaw false)]
      rw [Module.End.pow_apply]
      change liftBC A v false (delta^[Nb] (signedComm z B C)) = 0
      rw [hBC, map_zero]
  have twistCombined (s t : ℂ) (pair : PairSpace V) :
      twistPair s t (combined pair) = combined (twistPair s t pair) := by
    change twistPair s t (deltaXY pair + deltaYZ pair) = _
    rw [map_add, twistXY, twistYZ]
    rfl
  have twistedAC : (combined ^ Na) (twistPair z x (signedPairAC y A B C v)) = 0 := by
    rw [← intertwiningPowers combined combined (twistPair z x) (twistCombined z x),
      acKilled, map_zero]
  have twistedBC : (deltaYZ ^ Nb) (twistPair 1 (x * y) (signedPairBC z A B C v)) = 0 := by
    rw [← intertwiningPowers (deltaYZ (V := V)) deltaYZ (twistPair 1 (x * y))
      (twistYZ 1 (x * y)),
      bcKilled, map_zero]
  change ((combined ^ Na * deltaYZ ^ Nb : Module.End ℂ (PairSpace V))) _ = 0
  rw [signedTriple, Module.End.mul_apply, map_add, map_add]
  have commute : Commute combined deltaYZ := shiftsCommute.add_left (Commute.refl deltaYZ)
  rw [← Module.End.mul_apply, (commute.pow_pow Na Nb).eq, Module.End.mul_apply,
    twistedAC, map_zero, twistedBC, map_zero, add_zero]

private theorem signedPair_high (x y z : ℂ) (A B C : VertexOperator ℂ V) (v : V)
    (N : ℕ) (hAB : delta^[N] (signedComm x A B) = 0) :
    discrepancy ((deltaXY ^ N) (signedTriple x y z A B C v)) = 0 := by
  let lifting := liftAB C v true - (y * z) • liftAB C v false
  have pairDifference : discrepancy (signedTriple x y z A B C v) =
      lifting (signedComm x A B) := by
    funext l m r
    change (signedTriple x y z A B C v).val.1 l m r -
      (signedTriple x y z A B C v).val.2 l m r = _
    rw [(signedTriple_coefficients x y z A B C v l m r).1,
      (signedTriple_coefficients x y z A B C v l m r).2]
    simp only [lifting, liftAB, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, ite_true, Bool.false_eq_true, ite_false, signedComm,
      Module.End.mul_apply, map_sub, map_smul, smul_smul, Pi.sub_apply, Pi.smul_apply]
    module
  have liftingLaw (D : ℤ → ℤ → Module.End ℂ V) :
      lifting (deltaEnd D) = plainXY (lifting D) := by
    funext l m r
    dsimp [lifting, liftAB, deltaEnd, delta, plainXY, shiftXY]
    simp only [map_sub]
    module
  rw [intertwiningPowers (deltaXY (V := V)) plainXY discrepancy discrepancyXY,
    pairDifference, ← intertwiningPowers deltaEnd plainXY lifting liftingLaw]
  rw [Module.End.pow_apply]
  change lifting (delta^[N] (signedComm x A B)) = 0
  rw [hAB, map_zero]
private theorem signedTriple_residue (x y z : ℂ) (A B C : VertexOperator ℂ V) (v : V) :
    res (signedTriple x y z A B C v) = fun l r =>
      signedComm (y * z) (signedNormalMinusOne x A B).1 C l r v := by
  funext l r
  have hf (w : V) : Function.HasFiniteSupport
      (fun i : ℕ => (A [[-(i : ℤ) - 1]]) ((B [[l + i]]) w)) := by
    simpa only [show ∀ i : ℕ, (-1 : ℤ) - i = -(i : ℤ) - 1 by intro i; omega] using
      forward_finite A B (-1) l w
  have hr (w : V) : Function.HasFiniteSupport
      (fun i : ℕ => (B [[l - i - 1]]) ((A [[i]]) w)) := by
    simpa only [show ∀ i : ℕ, l - 1 - i = l - i - 1 by intro i; omega] using
      reverse_finite B A (l - 1) w
  have hmf := (hf v).fun_comp (map_zero (C [[r]]))
  have hmr := (hr v).fun_comp (map_zero (C [[r]]))
  change residue (signedTriple x y z A B C v).val.1
    (signedTriple x y z A B C v).val.2 l r = _
  unfold residue
  simp_rw [(signedTriple_coefficients x y z A B C v _ _ r).1,
    (signedTriple_coefficients x y z A B C v _ _ r).2]
  have hsf : Function.HasFiniteSupport (fun i : ℕ => (y * z) •
      (C [[r]]) ((A [[-(i : ℤ) - 1]]) ((B [[l + i]]) v))) :=
    hmf.smul_right (fun _ => y * z)
  have hsr : Function.HasFiniteSupport (fun i : ℕ => (x * y * z) •
      (C [[r]]) ((B [[l - i - 1]]) ((A [[i]]) v))) :=
    hmr.smul_right (fun _ => x * y * z)
  have hrx : Function.HasFiniteSupport (fun i : ℕ => x •
      (B [[l - i - 1]]) ((A [[i]]) ((C [[r]]) v))) :=
    (hr ((C [[r]]) v)).smul_right (fun _ => x)
  rw [finsum_sub_distrib (hf ((C [[r]]) v)) hsf,
    finsum_sub_distrib hrx hsr]
  rw [← smul_finsum' (y * z) hmf, ← smul_finsum' x (hr ((C [[r]]) v)),
    ← smul_finsum' (x * y * z) hmr]
  rw [← map_finsum (C [[r]]) (hf v), ← map_finsum (C [[r]]) (hr v)]
  simp only [signedComm, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
  rw [(signedNormalMinusOne x A B).2, (signedNormalMinusOne x A B).2, map_add, map_smul]
  module

theorem signedNormal_locality (x y z : ℂ) (A B C : VertexOperator ℂ V)
    (Na Nb Nc : ℕ) (hAC : delta^[Na] (signedComm y A C) = 0)
    (hBC : delta^[Nb] (signedComm z B C) = 0)
    (hAB : delta^[Nc] (signedComm x A B) = 0) :
    delta^[Na + Nb + Nc] (signedComm (y * z) (signedNormalMinusOne x A B).1 C) = 0 := by
  funext l r
  apply LinearMap.ext
  intro v
  have cancelled := cancellationBound (signedTriple x y z A B C v) Na Nb Nc
    (signedPair_low x y z A B C v Na Nb hAC hBC)
    (signedPair_high x y z A B C v Nc hAB)
  rw [signedTriple_residue] at cancelled
  have evaluationLaw (D : ℤ → ℤ → Module.End ℂ V) :
      evaluate v (deltaEnd D) = plainDelta (evaluate v D) := rfl
  have transport := intertwiningPowers deltaEnd plainDelta (evaluate v) evaluationLaw
    (Na + Nb + Nc) (signedComm (y * z) (signedNormalMinusOne x A B).1 C)
  rw [Module.End.pow_apply, Module.End.pow_apply] at transport
  change evaluate v (delta^[Na + Nb + Nc]
    (signedComm (y * z) (signedNormalMinusOne x A B).1 C)) =
      delta^[Na + Nb + Nc] (fun l r =>
        signedComm (y * z) (signedNormalMinusOne x A B).1 C l r v) at transport
  rw [cancelled] at transport
  exact congrFun (congrFun transport l) r

theorem signedDerivative_locality (s : ℂ) (first second : VertexOperator ℂ V) (order degree : ℕ)
    (killed : delta^[order] (signedComm s first second) = 0) :
    delta^[order + degree] (signedComm s (dividedDerivative degree first) second) = 0 := by
  have leftDerivativeLocal (first second : VertexOperator ℂ V) (order : ℕ)
      (killed : delta^[order] (signedComm s first second) = 0) :
      delta^[order + 1] (signedComm s (dividedDerivative 1 first) second) = 0 := by
    have modes (index : ℤ) : ((dividedDerivative 1 first) [[index]]) =
        -(index : ℂ) • (first [[index - 1]]) := by
      apply LinearMap.ext
      intro vector
      change Ring.choose (-index - 1 + 1) 1 •
        HVertexOperator.coeff first (-index - 1 + 1) vector = _
      rw [Ring.choose_one_right, VertexOperator.coeff_eq_ncoeff]
      rw [show -(-index - 1 + 1) - 1 = index - 1 by omega]
      simp only [LinearMap.smul_apply,
        show -index - 1 + 1 = -index by omega]
      rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg]
    have differentiated : signedComm s (dividedDerivative 1 first) second = weighted (signedComm s
      first second) := by
      funext left right
      rw [signedComm, modes, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      dsimp only [weighted, signedComm]
      module
    rw [differentiated]
    have linearDelta (first second : ℤ → ℤ → Module.End ℂ V) :
        delta (first - second) = delta first - delta second := by
      funext left right
      dsimp [delta]
      abel
    have scaledDelta (scalar : ℂ) (distribution : ℤ → ℤ → Module.End ℂ V) :
        delta (scalar • distribution) = scalar • delta distribution := by
      funext left right
      simp [delta, smul_sub]
    have leibniz (distribution : ℤ → ℤ → Module.End ℂ V) :
        delta (weighted distribution) = weighted (delta distribution) - distribution := by
      funext left right
      dsimp [delta, weighted]
      rw [show left + 1 - 1 = left by omega, show left - 1 + 1 = left by omega]
      push_cast
      module
    have iterated (distribution : ℤ → ℤ → Module.End ℂ V) : ∀ degree : ℕ,
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
    have next : delta^[order + 1] (signedComm s first second) = 0 := by
      rw [Function.iterate_succ_apply', killed]
      funext left right
      simp [delta]
    rw [killed, next]
    funext left right
    simp [weighted]
  have successive : ∀ count : ℕ,
      delta^[order + count] (signedComm s ((dividedDerivative 1)^[count] first) second) = 0 := by
    intro count
    induction count with
    | zero => simpa using killed
    | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      simpa only [Nat.add_assoc] using leftDerivativeLocal
        ((dividedDerivative 1)^[count] first) second (order + count) inductionHypothesis
  have evaluation (vector : V) : ∀ (count : ℕ) (operator : VertexOperator ℂ V),
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
  have scaled : signedComm s ((degree.factorial : ℂ) • dividedDerivative degree first) second =
      (degree.factorial : ℂ) • signedComm s (dividedDerivative degree first) second := by
    funext left right
    simp only [signedComm, map_smul, Pi.smul_apply, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  have result := successive degree
  rw [identity, scaled] at result
  have linearity : delta^[order + degree]
      ((degree.factorial : ℂ) • signedComm s (dividedDerivative degree first) second) =
      (degree.factorial : ℂ) • delta^[order + degree]
        (signedComm s (dividedDerivative degree first) second) := by
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order + degree] _ =
      (degree.factorial : ℂ) • (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order + degree] _
    rw [← Module.End.pow_apply, ← Module.End.pow_apply, map_smul]
  rw [linearity] at result
  exact (smul_eq_zero.mp result).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero degree))


end D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
