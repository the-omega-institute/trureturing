/- GID: D5/S3/Quantum/Fermionic/BcGhostStateFieldLocality
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostStateFieldLocality
   mirror-E: none(waiver:algebraic-ghost-superlocality)
   anchors: []
   utility: none
   digest: Signed finite-residue cancellation for the actual ghost word fields. -/

/-
proof_shape: stateField_locality: content
escape_witness: The signed three-field discrepancy obeys the existing finite-residue
cancellation kernel. Derivative closure, sorted occupation words and homogeneous
support-sign extraction prove operator-uniform locality on all actual states.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostStateField
import D5.S3.VertexAlgebra.FieldNormalProductLocality

/-! The finite-residue kernel is reused from ordinary Dong locality. The input
triple pair and its discrepancy are actually signed, and the resulting normal
product is the signed product used in the actual occupation construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostStateField
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open private signedNormalMinusOne wordField generatingField generating_modes
  generatingMode derivative_modes Y_ket forward_finite reverse_finite from
  D5.S3.Quantum.Fermionic.BcGhostStateField
open private shiftsCommute discrepancyXY intertwiningPowers cancellationBound from
  D5.S3.VertexAlgebra.FieldNormalProductLocality

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality

private def signedComm (s : ℂ) (A B : VertexOperator ℂ Fock) :
    ℤ → ℤ → Module.End ℂ Fock := fun m n =>
  (A [[m]]) * (B [[n]]) - s • ((B [[n]]) * (A [[m]]))

private def signedPairAC (s : ℂ) (first second third : VertexOperator ℂ Fock) (vector : Fock) : PairSpace Fock := by
  have increasingFinite (operator : VertexOperator ℂ Fock) (start : ℤ) (vector : Fock) :
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

private def signedPairBC (s : ℂ) (first second third : VertexOperator ℂ Fock) (vector : Fock) : PairSpace Fock := by
  have increasingFinite (operator : VertexOperator ℂ Fock) (start : ℤ) (vector : Fock) :
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

private def twistPair (x y : ℂ) : Module.End ℂ (PairSpace Fock) where
  toFun pair := ⟨(x • pair.val.1, y • pair.val.2), by
    constructor
    · intro l m r
      exact (pair.property.1 l m r).smul_right (fun _ => x)
    · intro l m r
      exact (pair.property.2 l m r).smul_right (fun _ => y)⟩
  map_add' a b := by apply Subtype.ext; ext <;> simp [smul_add]
  map_smul' s a := by apply Subtype.ext; ext <;> simp [smul_smul, mul_comm s]

private theorem twistXY (x y : ℂ) (pair : PairSpace Fock) :
    twistPair x y (deltaXY pair) = deltaXY (twistPair x y pair) := by
  apply Subtype.ext
  ext <;> simp [twistPair, deltaXY, shiftXY, smul_sub]

private theorem twistYZ (x y : ℂ) (pair : PairSpace Fock) :
    twistPair x y (deltaYZ pair) = deltaYZ (twistPair x y pair) := by
  apply Subtype.ext
  ext <;> simp [twistPair, deltaYZ, shiftYZ, smul_sub]

private def signedTriple (x y z : ℂ) (A B C : VertexOperator ℂ Fock) (v : Fock) :
    PairSpace Fock :=
  twistPair z x (signedPairAC y A B C v) +
    twistPair 1 (x * y) (signedPairBC z A B C v)

private theorem signedTriple_coefficients (x y z : ℂ) (A B C : VertexOperator ℂ Fock)
    (v : Fock) (l m r : ℤ) :
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

private theorem signedPair_low (x y z : ℂ) (A B C : VertexOperator ℂ Fock) (v : Fock)
    (Na Nb : ℕ) (hAC : delta^[Na] (signedComm y A C) = 0)
    (hBC : delta^[Nb] (signedComm z B C) = 0) :
    (((deltaXY + deltaYZ) ^ Na * deltaYZ ^ Nb : Module.End ℂ (PairSpace Fock)))
      (signedTriple x y z A B C v) = 0 := by
  let combined : Module.End ℂ (PairSpace Fock) := deltaXY + deltaYZ
  let combinedPlain : Module.End ℂ (Triple Fock) := plainXY + plainYZ
  have firstProjection (value : PairSpace Fock) : projectionFirst (combined value) =
      combinedPlain (projectionFirst value) := rfl
  have secondProjection (value : PairSpace Fock) : projectionSecond (combined value) =
      combinedPlain (projectionSecond value) := rfl
  have projectionYZFirst (value : PairSpace Fock) : projectionFirst (deltaYZ value) =
      plainYZ (projectionFirst value) := rfl
  have projectionYZSecond (value : PairSpace Fock) : projectionSecond (deltaYZ value) =
      plainYZ (projectionSecond value) := rfl
  have acLaw (factor : Bool) (D : ℤ → ℤ → Module.End ℂ Fock) :
      liftAC B v factor (deltaEnd D) = combinedPlain (liftAC B v factor D) := by
    funext l m r
    dsimp [liftAC, deltaEnd, delta, combinedPlain, plainXY, plainYZ, shiftXY, shiftYZ]
    cases factor <;> simp only [Bool.false_eq_true, if_false, if_true, map_sub] <;> abel
  have bcLaw (factor : Bool) (D : ℤ → ℤ → Module.End ℂ Fock) :
      liftBC A v factor (deltaEnd D) = plainYZ (liftBC A v factor D) := by
    funext l m r
    dsimp [liftBC, deltaEnd, delta, plainYZ, shiftYZ]
    cases factor <;> simp only [Bool.false_eq_true, if_false, if_true, map_sub]
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
      rw [intertwiningPowers (deltaYZ (V := Fock)) plainYZ projectionFirst projectionYZFirst]
      change (plainYZ ^ Nb) (liftBC A v true (signedComm z B C)) = 0
      rw [← intertwiningPowers deltaEnd plainYZ (liftBC A v true) (bcLaw true)]
      rw [Module.End.pow_apply]
      change liftBC A v true (delta^[Nb] (signedComm z B C)) = 0
      rw [hBC, map_zero]
    · change projectionSecond ((deltaYZ ^ Nb) (signedPairBC z A B C v)) = 0
      rw [intertwiningPowers (deltaYZ (V := Fock)) plainYZ projectionSecond projectionYZSecond]
      change (plainYZ ^ Nb) (liftBC A v false (signedComm z B C)) = 0
      rw [← intertwiningPowers deltaEnd plainYZ (liftBC A v false) (bcLaw false)]
      rw [Module.End.pow_apply]
      change liftBC A v false (delta^[Nb] (signedComm z B C)) = 0
      rw [hBC, map_zero]
  have twistCombined (s t : ℂ) (pair : PairSpace Fock) :
      twistPair s t (combined pair) = combined (twistPair s t pair) := by
    change twistPair s t (deltaXY pair + deltaYZ pair) = _
    rw [map_add, twistXY, twistYZ]
    rfl
  have twistedAC : (combined ^ Na) (twistPair z x (signedPairAC y A B C v)) = 0 := by
    rw [← intertwiningPowers combined combined (twistPair z x) (twistCombined z x),
      acKilled, map_zero]
  have twistedBC : (deltaYZ ^ Nb) (twistPair 1 (x * y) (signedPairBC z A B C v)) = 0 := by
    rw [← intertwiningPowers deltaYZ deltaYZ (twistPair 1 (x * y)) (twistYZ 1 (x * y)),
      bcKilled, map_zero]
  change ((combined ^ Na * deltaYZ ^ Nb : Module.End ℂ (PairSpace Fock))) _ = 0
  rw [signedTriple, Module.End.mul_apply, map_add, map_add]
  have commute : Commute combined deltaYZ := shiftsCommute.add_left (Commute.refl deltaYZ)
  rw [← Module.End.mul_apply, (commute.pow_pow Na Nb).eq, Module.End.mul_apply,
    twistedAC, map_zero, twistedBC, map_zero, add_zero]

private theorem signedPair_high (x y z : ℂ) (A B C : VertexOperator ℂ Fock) (v : Fock)
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
      AddHom.coe_mk, if_true, Bool.false_eq_true, if_false, signedComm,
      Module.End.mul_apply, map_sub, map_smul, smul_smul, Pi.sub_apply, Pi.smul_apply]
    module
  have liftingLaw (D : ℤ → ℤ → Module.End ℂ Fock) :
      lifting (deltaEnd D) = plainXY (lifting D) := by
    funext l m r
    dsimp [lifting, liftAB, deltaEnd, delta, plainXY, shiftXY]
    simp only [map_sub]
    module
  rw [intertwiningPowers (deltaXY (V := Fock)) plainXY discrepancy discrepancyXY,
    pairDifference, ← intertwiningPowers deltaEnd plainXY lifting liftingLaw]
  rw [Module.End.pow_apply]
  change lifting (delta^[N] (signedComm x A B)) = 0
  rw [hAB, map_zero]
private theorem signedTriple_residue (x y z : ℂ) (A B C : VertexOperator ℂ Fock) (v : Fock) :
    res (signedTriple x y z A B C v) = fun l r =>
      signedComm (y * z) (signedNormalMinusOne x A B).1 C l r v := by
  funext l r
  have hf (w : Fock) : Function.HasFiniteSupport
      (fun i : ℕ => (A [[-(i : ℤ) - 1]]) ((B [[l + i]]) w)) := by
    simpa only [show ∀ i : ℕ, (-1 : ℤ) - i = -(i : ℤ) - 1 by intro i; omega] using
      forward_finite A B (-1) l w
  have hr (w : Fock) : Function.HasFiniteSupport
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

private theorem signedNormal_locality (x y z : ℂ) (A B C : VertexOperator ℂ Fock)
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
  have evaluationLaw (D : ℤ → ℤ → Module.End ℂ Fock) :
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

private def Local (s : ℂ) (A B : VertexOperator ℂ Fock) : Prop :=
  ∃ N : ℕ, delta^[N] (signedComm s A B) = 0
private theorem signedDerivative_locality (s : ℂ) (first second : VertexOperator ℂ Fock) (order degree : ℕ)
    (killed : delta^[order] (signedComm s first second) = 0) :
    delta^[order + degree] (signedComm s (dividedDerivative degree first) second) = 0 := by
  have leftDerivativeLocal (first second : VertexOperator ℂ Fock) (order : ℕ)
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
    have linearDelta (first second : ℤ → ℤ → Module.End ℂ Fock) :
        delta (first - second) = delta first - delta second := by
      funext left right
      dsimp [delta]
      abel
    have scaledDelta (scalar : ℂ) (distribution : ℤ → ℤ → Module.End ℂ Fock) :
        delta (scalar • distribution) = scalar • delta distribution := by
      funext left right
      simp [delta, smul_sub]
    have leibniz (distribution : ℤ → ℤ → Module.End ℂ Fock) :
        delta (weighted distribution) = weighted (delta distribution) - distribution := by
      funext left right
      dsimp [delta, weighted]
      rw [show left + 1 - 1 = left by omega, show left - 1 + 1 = left by omega]
      push_cast
      module
    have iterated (distribution : ℤ → ℤ → Module.End ℂ Fock) : ∀ degree : ℕ,
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
  have evaluation (vector : Fock) : ∀ (count : ℕ) (operator : VertexOperator ℂ Fock),
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
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order + degree] _ =
      (degree.factorial : ℂ) • (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order + degree] _
    rw [← Module.End.pow_apply, ← Module.End.pow_apply, map_smul]
  rw [linearity] at result
  exact (smul_eq_zero.mp result).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero degree))

private theorem local_symm (s : ℂ) (hs : s * s = 1) (A B : VertexOperator ℂ Fock)
    (h : Local s A B) : Local s B A := by
  obtain ⟨N, hN⟩ := h
  have flipDelta (D : ℤ → ℤ → Module.End ℂ Fock) :
      delta (flipDistribution D) = -flipDistribution (delta D) := by
    funext l r
    dsimp [delta, flipDistribution]
    abel
  have scaledDelta (t : ℂ) (D : ℤ → ℤ → Module.End ℂ Fock) :
      delta (t • D) = t • delta D := by
    funext l r
    simp [delta, smul_sub]
  have flipIterate (D : ℤ → ℤ → Module.End ℂ Fock) (k : ℕ) :
      delta^[k] (flipDistribution D) = ((-1 : ℂ) ^ k) • flipDistribution (delta^[k] D) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, scaledDelta, flipDelta]
      rw [← Function.iterate_succ_apply' (f := delta) k D, pow_succ]
      funext l r
      simp only [Pi.smul_apply, Pi.neg_apply]
      module
  have reversed : signedComm s B A = (-s) • flipDistribution (signedComm s A B) := by
    funext l r
    simp only [signedComm, flipDistribution, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, Pi.smul_apply,
      smul_sub, smul_smul, neg_mul, hs, neg_one_smul]
    module
  refine ⟨N, ?_⟩
  rw [reversed]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[N]
    ((-s) • flipDistribution (signedComm s A B)) = 0
  rw [← Module.End.pow_apply, map_smul, Module.End.pow_apply]
  change (-s) • delta^[N] (flipDistribution (signedComm s A B)) = 0
  rw [flipIterate, hN, map_zero, smul_zero, smul_zero]

private theorem identity_local (A : VertexOperator ℂ Fock) : Local 1 identityField A := by
  refine ⟨0, ?_⟩
  funext l r
  have identityModes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
      if n = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -n - 1 = 0 ↔ n = -1 by omega]
  simp only [Function.iterate_zero_apply, signedComm, identityModes, one_smul]
  split_ifs <;> simp [Module.End.mul_eq_comp]

private theorem normal_local (x y z : ℂ) (A B C : VertexOperator ℂ Fock)
    (hAC : Local y A C) (hBC : Local z B C) (hAB : Local x A B) :
    Local (y * z) (signedNormalMinusOne x A B).1 C := by
  obtain ⟨Na, ha⟩ := hAC
  obtain ⟨Nb, hb⟩ := hBC
  obtain ⟨Nc, hc⟩ := hAB
  exact ⟨Na + Nb + Nc, signedNormal_locality x y z A B C Na Nb Nc ha hb hc⟩

private theorem generating_local (a b : Bool) : Local (-1) (generatingField a) (generatingField b) := by
  have mixed (l r : ℤ) : signedComm (-1) (generatingField false) (generatingField true) l r =
      if l + r + 1 = 0 then (1 : Module.End ℂ Fock) else 0 := by
    simp only [signedComm, generating_modes, generatingMode, Bool.false_eq_true, ite_false,
      ite_true, neg_one_smul, sub_neg_eq_add]
    rw [ghost_mixed_car, show (l - 1) + (r + 2) = l + r + 1 by omega]
  cases a <;> cases b
  · refine ⟨0, ?_⟩
    funext l r
    simpa only [Function.iterate_zero_apply, signedComm, generating_modes, generatingMode,
      Bool.false_eq_true, ite_false, neg_one_smul, sub_neg_eq_add, Pi.zero_apply] using
      ghost_b_car (l - 1) (r - 1)
  · refine ⟨1, ?_⟩
    funext l r
    simp only [Function.iterate_one, delta, mixed]
    rw [show l + 1 + r + 1 = l + (r + 1) + 1 by omega]
    simp
  · apply local_symm (-1) (by norm_num)
    refine ⟨1, ?_⟩
    funext l r
    simp only [Function.iterate_one, delta, mixed]
    rw [show l + 1 + r + 1 = l + (r + 1) + 1 by omega]
    simp
  · refine ⟨0, ?_⟩
    funext l r
    simpa only [Function.iterate_zero_apply, signedComm, generating_modes, generatingMode,
      ite_true, neg_one_smul, sub_neg_eq_add, Pi.zero_apply] using
      ghost_c_car (l + 2) (r + 2)

private theorem derivatives_local (a b : Bool) (k l : ℕ) :
    Local (-1) (dividedDerivative k (generatingField a)) (dividedDerivative l (generatingField b)) := by
  obtain ⟨N, hN⟩ := generating_local a b
  have hk := signedDerivative_locality (-1) (generatingField a) (generatingField b) N k hN
  have hrev := local_symm (-1) (by norm_num) _ _ ⟨N + k, hk⟩
  obtain ⟨M, hM⟩ := hrev
  have hl := signedDerivative_locality (-1) (generatingField b)
    (dividedDerivative k (generatingField a)) M l hM
  exact local_symm (-1) (by norm_num) _ _ ⟨M + l, hl⟩

private theorem word_local (w u : List ℕ) :
    Local ((-1 : ℂ) ^ (w.length * u.length)) (wordField w) (wordField u) := by
  have signSquare (p : ℕ) : ((-1 : ℂ) ^ p) * ((-1 : ℂ) ^ p) = 1 := by
    rw [← mul_pow]
    norm_num
  have generatorWord : ∀ (u : List ℕ) (j : ℕ),
      Local ((-1 : ℂ) ^ u.length)
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1))) (wordField u) := by
    intro u
    induction u with
    | nil =>
      intro j
      exact local_symm 1 (by norm_num) _ _ (identity_local _)
    | cons k tail ih =>
      intro j
      have h := normal_local ((-1 : ℂ) ^ tail.length) (-1) ((-1 : ℂ) ^ tail.length)
        (dividedDerivative (k / 2) (generatingField (k % 2 == 1))) (wordField tail)
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
        (derivatives_local _ _ _ _)
        (local_symm _ (signSquare tail.length) _ _ (ih j)) (ih k)
      have hout : (-1 : ℂ) * (-1 : ℂ) ^ tail.length = (-1 : ℂ) ^ (k :: tail).length := by
        simp only [List.length_cons, pow_succ']
      rw [hout] at h
      exact local_symm _ (signSquare (k :: tail).length) _ _ h
  induction w with
  | nil => simpa only [List.length_nil, zero_mul, pow_zero, wordField] using identity_local (wordField u)
  | cons j tail ih =>
    have h := normal_local ((-1 : ℂ) ^ tail.length) ((-1 : ℂ) ^ u.length)
      ((-1 : ℂ) ^ (tail.length * u.length))
      (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
      (wordField tail) (wordField u) (generatorWord u j) ih (generatorWord tail j)
    have hout : (-1 : ℂ) ^ u.length * (-1 : ℂ) ^ (tail.length * u.length) =
        (-1 : ℂ) ^ ((j :: tail).length * u.length) := by
      rw [← pow_add]
      congr 1
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    simpa only [wordField, hout] using h

/-- Every two actual occupation basis states have operator-uniform signed locality. -/
private theorem occupation_locality (S U : Finset ℕ) :
    ∃ N : ℕ, delta^[N] (fun m n =>
      ((Y (ket S)) [[m]]) * ((Y (ket U)) [[n]]) -
        ((-1 : ℂ) ^ (S.card * U.card)) •
          (((Y (ket U)) [[n]]) * ((Y (ket S)) [[m]]))) = 0 := by
  have h := word_local S.sort U.sort
  simp only [Finset.length_sort] at h
  change Local ((-1 : ℂ) ^ (S.card * U.card)) (Y (ket S)) (Y (ket U))
  rw [Y_ket, Y_ket]
  exact h

private theorem monotone (distribution : ℤ → ℤ → Module.End ℂ Fock) (small large : ℕ)
    (less : small ≤ large) (killed : delta^[small] distribution = 0) : delta^[large]
      distribution = 0 := by
  have original : (deltaEnd ^ small) distribution = 0 := by
    rw [Module.End.pow_apply]
    exact killed
  have result := Module.End.pow_map_zero_of_le less original
  rw [Module.End.pow_apply] at result
  exact result
private theorem localAdd (s : ℂ) (first second third : VertexOperator ℂ Fock)
    (firstLocal : Local s first third) (secondLocal : Local s second third) : Local s (first +
      second) third := by
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  let order := max firstOrder secondOrder
  have firstBound := monotone (signedComm s first third) firstOrder
    order (le_max_left _ _) firstKilled
  have secondBound := monotone (signedComm s second third)
    secondOrder order (le_max_right _ _) secondKilled
  refine ⟨order, ?_⟩
  have split : signedComm s (first + second) third =
    signedComm s first third + signedComm s
    second third := by
    funext left right
    simp only [signedComm, map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    module
  rw [split]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] _ = 0
  rw [← Module.End.pow_apply, map_add]
  simp only [Module.End.pow_apply]
  change delta^[order] (signedComm s first third) +
    delta^[order] (signedComm s second third) = 0
  rw [firstBound, secondBound, add_zero]
private theorem localSmul (s : ℂ) (scalar : ℂ) (first second : VertexOperator ℂ Fock)
    (locality : Local s first second) : Local s (scalar • first) second := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  have split : signedComm s (scalar • first) second = scalar •
    signedComm s first second := by
    funext left right
    simp only [signedComm, map_smul, Pi.smul_apply,
      Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  rw [split]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] _ = 0
  rw [← Module.End.pow_apply, map_smul]
  simp only [Module.End.pow_apply]
  change scalar • delta^[order] (signedComm s first second) = 0
  rw [killed, smul_zero]
private theorem localSum (s : ℂ) {Index : Type} (indices : Finset Index) (fields : Index → VertexOperator ℂ Fock)
    (operator : VertexOperator ℂ Fock) (locality : ∀ index ∈ indices, Local s (fields index)
      operator) :
    Local s (∑ index ∈ indices, fields index) operator := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    funext left right
    simp [signedComm]
  | @insert index indices absent inductionHypothesis =>
    rw [Finset.sum_insert absent]
    exact localAdd s _ _ _ (locality index (Finset.mem_insert_self _ _))
      (inductionHypothesis (fun other member => locality other (Finset.mem_insert_of_mem member)))
open D5.S3.Quantum.Fermionic.CountableOccupationFock (parity_ket)

private theorem parity_coefficient (a : Fock) (S : Finset ℕ) :
    parity a S = (-1 : ℂ) ^ S.card * a S := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb, mul_add]
  | single U z =>
    have hu : Finsupp.single U z = z • ket U := by simp [ket]
    rw [hu, map_smul, parity_ket]
    by_cases h : U = S
    · subst U
      simp [ket, mul_comm]
    · simp [ket, h]

/-- Homogeneous signed locality on every state of the original countable carrier. -/
theorem stateField_locality (a b : Fock) (p q : ℕ)
    (ha : parity a = ((-1 : ℂ) ^ p) • a)
    (hb : parity b = ((-1 : ℂ) ^ q) • b) :
    ∃ N : ℕ, delta^[N] (fun m n =>
      ((Y a) [[m]]) * ((Y b) [[n]]) - ((-1 : ℂ) ^ (p * q)) •
        (((Y b) [[n]]) * ((Y a) [[m]]))) = 0 := by
  classical
  let s := (-1 : ℂ) ^ (p * q)
  have hs : s * s = 1 := by dsimp [s]; rw [← mul_pow]; norm_num
  have supportSign (v : Fock) (k : ℕ) (h : parity v = ((-1 : ℂ) ^ k) • v)
      (S : Finset ℕ) (hS : S ∈ v.support) : (-1 : ℂ) ^ S.card = (-1 : ℂ) ^ k := by
    have he := congrArg (fun w : Fock => w S) h
    simp only [parity_coefficient, Finsupp.smul_apply, smul_eq_mul] at he
    exact mul_right_cancel₀ (Finsupp.mem_support_iff.mp hS) he
  have expansion (v : Fock) : Y v = ∑ S ∈ v.support, (v S) • Y (ket S) := by
    calc
      Y v = ∑ S ∈ v.support, (v S) • wordField S.sort := by
        simp only [Y, Finsupp.lsum_apply, LinearMap.smulRight_apply,
          LinearMap.id_apply, Finsupp.sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Y_ket]
  change Local s (Y a) (Y b)
  rw [expansion a]
  apply localSum s
  intro S hS
  apply localSmul s
  apply local_symm s hs
  rw [expansion b]
  apply localSum s
  intro U hU
  apply localSmul s
  apply local_symm s hs
  have he : (-1 : ℂ) ^ (S.card * U.card) = s := by
    rw [pow_mul, supportSign a p ha S hS]
    rw [← pow_mul, Nat.mul_comm p U.card, pow_mul, supportSign b q hb U hU]
    rw [← pow_mul, Nat.mul_comm q p]
  have h := occupation_locality S U
  change Local ((-1 : ℂ) ^ (S.card * U.card)) (Y (ket S)) (Y (ket U)) at h
  rw [he] at h
  exact h

end D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
