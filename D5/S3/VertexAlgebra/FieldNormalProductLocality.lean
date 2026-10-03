/- GID: D5/S3/VertexAlgebra/FieldNormalProductLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FieldNormalProductLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite residue cancellation preserves operator-uniform locality. -/

/-
proof_shape: normalMinusOne_locality: content; dividedDerivative_locality: content
escape_witness: The geometric residue boundary converts the high polynomial
shift powers to the killed three-field discrepancy. Binomial cancellation
uses the sum of the three input locality orders independently of every vector.
Divided-derivative covariance of the annihilating polynomial increases its
order through a nontrivial finite-difference Leibniz calculation.
admission_basis: escape-witness
Classical source: Matsuo–Nagatomo, Proposition 1.5.5 and Theorem 5.4.1.
The statements concern formal operator fields, not physical spacetime.
-/

import D5.S3.VertexAlgebra.FieldNormalProduct

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.FieldNormalProductLocality

open D5.S3.VertexAlgebra.FieldNormalProduct
open scoped VertexOperator

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

abbrev Triple (V : Type*) := ℤ → ℤ → ℤ → V

def shiftXY (distribution : Triple V) : Triple V :=
  fun first second third => distribution (first + 1) second third -
    distribution first (second + 1) third

def shiftYZ (distribution : Triple V) : Triple V :=
  fun first second third => distribution first (second + 1) third -
    distribution first second (third + 1)

def NegativeFinite (distribution : Triple V) : Prop :=
  ∀ first second third : ℤ,
    Function.HasFiniteSupport (fun offset : ℕ =>
      distribution (first - offset) (second + offset) third)

def PositiveFinite (distribution : Triple V) : Prop :=
  ∀ first second third : ℤ,
    Function.HasFiniteSupport (fun offset : ℕ =>
      distribution (first + offset) (second - offset) third)

noncomputable def residue (negative positive : Triple V) : ℤ → ℤ → V :=
  fun second third =>
    (∑ᶠ offset : ℕ, negative (-(offset : ℤ) - 1) (second + offset) third) +
    (∑ᶠ offset : ℕ, positive offset (second - offset - 1) third)

def pairSpace : Submodule ℂ (Triple V × Triple V) where
  carrier := {pair | NegativeFinite pair.1 ∧ PositiveFinite pair.2}
  zero_mem' := by constructor <;> intro first second third <;> simp [Function.HasFiniteSupport]
  add_mem' := by
    intro first second firstFinite secondFinite
    constructor
    · intro left middle right
      exact (firstFinite.1 left middle right).add (secondFinite.1 left middle right)
    · intro left middle right
      exact (firstFinite.2 left middle right).add (secondFinite.2 left middle right)
  smul_mem' := by
    intro scalar pair finite
    constructor
    · intro left middle right
      exact (finite.1 left middle right).smul_right (fun _ => scalar)
    · intro left middle right
      exact (finite.2 left middle right).smul_right (fun _ => scalar)

abbrev PairSpace (V : Type*) [AddCommGroup V] [Module ℂ V] := ↥(pairSpace (V := V))

noncomputable def deltaXY : Module.End ℂ (PairSpace V) where
  toFun pair := ⟨(shiftXY pair.val.1, shiftXY pair.val.2), by
    constructor
    · intro first second third
      simpa only [shiftXY, Pi.sub_def, add_sub_right_comm, add_assoc, add_left_comm, add_comm] using
        (pair.property.1 (first + 1) second third).sub
          (pair.property.1 first (second + 1) third)
    · intro first second third
      simpa only [shiftXY, Pi.sub_def, sub_add_eq_add_sub, add_assoc, add_left_comm, add_comm] using
        (pair.property.2 (first + 1) second third).sub
          (pair.property.2 first (second + 1) third)⟩
  map_add' first second := by
    apply Subtype.ext
    ext <;> simp [shiftXY] <;> abel
  map_smul' scalar pair := by
    apply Subtype.ext
    ext <;> simp [shiftXY, smul_sub]

noncomputable def deltaYZ : Module.End ℂ (PairSpace V) where
  toFun pair := ⟨(shiftYZ pair.val.1, shiftYZ pair.val.2), by
    constructor
    · intro first second third
      simpa only [shiftYZ, Pi.sub_def, sub_add_eq_add_sub, add_assoc, add_left_comm, add_comm] using
        (pair.property.1 first (second + 1) third).sub
          (pair.property.1 first second (third + 1))
    · intro first second third
      simpa only [shiftYZ, Pi.sub_def, sub_add_eq_add_sub, add_assoc, add_left_comm, add_comm] using
        (pair.property.2 first (second + 1) third).sub
          (pair.property.2 first second (third + 1))⟩
  map_add' first second := by
    apply Subtype.ext
    ext <;> simp [shiftYZ] <;> abel
  map_smul' scalar pair := by
    apply Subtype.ext
    ext <;> simp [shiftYZ, smul_sub]

noncomputable def res : PairSpace V →ₗ[ℂ] (ℤ → ℤ → V) where
  toFun pair := residue pair.val.1 pair.val.2
  map_add' first second := by
    funext left right
    dsimp [residue]
    have negativeFinite (pair : PairSpace V) : Function.HasFiniteSupport
        (fun offset : ℕ => pair.val.1 (-(offset : ℤ) - 1) (left + offset) right) := by
      simpa only [show ∀ offset : ℕ, (-1 : ℤ) - offset = -(offset : ℤ) - 1 by
        intro offset; omega] using pair.property.1 (-1) left right
    have positiveFinite (pair : PairSpace V) : Function.HasFiniteSupport
        (fun offset : ℕ => pair.val.2 offset (left - offset - 1) right) := by
      simpa only [zero_add, sub_right_comm] using pair.property.2 0 (left - 1) right
    rw [finsum_add_distrib (negativeFinite first) (negativeFinite second),
      finsum_add_distrib (positiveFinite first) (positiveFinite second)]
    abel
  map_smul' scalar pair := by
    funext left right
    dsimp [residue]
    have negativeFinite : Function.HasFiniteSupport
        (fun offset : ℕ => pair.val.1 (-(offset : ℤ) - 1) (left + offset) right) := by
      simpa only [show ∀ offset : ℕ, (-1 : ℤ) - offset = -(offset : ℤ) - 1 by
        intro offset; omega] using pair.property.1 (-1) left right
    have positiveFinite : Function.HasFiniteSupport
        (fun offset : ℕ => pair.val.2 offset (left - offset - 1) right) := by
      simpa only [zero_add, sub_right_comm] using pair.property.2 0 (left - 1) right
    rw [← smul_finsum' scalar negativeFinite, ← smul_finsum' scalar positiveFinite, smul_add]

def delta (distribution : ℤ → ℤ → V) : ℤ → ℤ → V :=
  fun first second => distribution (first + 1) second - distribution first (second + 1)

def plainXY : Module.End ℂ (Triple V) where
  toFun := shiftXY
  map_add' first second := by funext left middle right; simp [shiftXY]; abel
  map_smul' scalar value := by funext left middle right; simp [shiftXY, smul_sub]

def plainYZ : Module.End ℂ (Triple V) where
  toFun := shiftYZ
  map_add' first second := by funext left middle right; simp [shiftYZ]; abel
  map_smul' scalar value := by funext left middle right; simp [shiftYZ, smul_sub]

def discrepancy : PairSpace V →ₗ[ℂ] Triple V where
  toFun pair := pair.val.1 - pair.val.2
  map_add' first second := by funext left middle right; simp; abel
  map_smul' scalar value := by funext left middle right; simp [smul_sub]

def commutator (first second : VertexOperator ℂ V) : ℤ → ℤ → Module.End ℂ V :=
  fun left right => (first [[left]]) * (second [[right]]) -
    (second [[right]]) * (first [[left]])

noncomputable def pairAC (first second third : VertexOperator ℂ V) (vector : V) : PairSpace V := by
  have increasingFinite (operator : VertexOperator ℂ V) (start : ℤ) (vector : V) :
      Function.HasFiniteSupport (fun offset : ℕ => (operator [[start + offset]]) vector) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (operator vector)).order - start).toNat, ?_⟩
    intro offset member
    contrapose! member
    rw [Function.notMem_support]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  exact ⟨(fun left middle right => commutator first third left right ((second [[middle]]) vector),
    fun left middle right => (second [[middle]]) (commutator first third left right vector)), by
    constructor
    · intro left middle right
      refine (increasingFinite second middle vector).subset ?_
      intro offset member vanish
      change (second [[middle + offset]]) vector = 0 at vanish
      apply member
      change commutator first third (left - offset) right
        ((second [[middle + offset]]) vector) = 0
      rw [vanish, map_zero]
    · intro left middle right
      have firstFinite := increasingFinite first left ((third [[right]]) vector)
      have secondFinite := (increasingFinite first left vector).comp
        ((third [[right]]).map_zero)
      have finite := firstFinite.sub secondFinite
      refine finite.subset ?_
      intro offset member vanish
      apply member
      have zero : commutator first third (left + offset) right vector = 0 := vanish
      change (second [[middle - offset]]) (commutator first third (left + offset) right vector) = 0
      rw [zero, map_zero]⟩

noncomputable def pairBC (first second third : VertexOperator ℂ V) (vector : V) : PairSpace V := by
  have increasingFinite (operator : VertexOperator ℂ V) (start : ℤ) (vector : V) :
      Function.HasFiniteSupport (fun offset : ℕ => (operator [[start + offset]]) vector) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (operator vector)).order - start).toNat, ?_⟩
    intro offset member
    contrapose! member
    rw [Function.notMem_support]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  exact ⟨(fun left middle right => (first [[left]]) (commutator second third middle right vector),
    fun left middle right => commutator second third middle right ((first [[left]]) vector)), by
    constructor
    · intro left middle right
      have firstFinite := increasingFinite second middle ((third [[right]]) vector)
      have secondFinite := (increasingFinite second middle vector).comp
        ((third [[right]]).map_zero)
      have finite := firstFinite.sub secondFinite
      refine finite.subset ?_
      intro offset member vanish
      apply member
      have zero : commutator second third (middle + offset) right vector = 0 := vanish
      change (first [[left - offset]]) (commutator second third (middle + offset) right vector) = 0
      rw [zero, map_zero]
    · intro left middle right
      refine (increasingFinite first left vector).subset ?_
      intro offset member vanish
      change (first [[left + offset]]) vector = 0 at vanish
      apply member
      change commutator second third (middle - offset) right
        ((first [[left + offset]]) vector) = 0
      rw [vanish, map_zero]⟩

noncomputable def triplePair (first second third : VertexOperator ℂ V) (vector : V) : PairSpace V :=
  pairAC first second third vector + pairBC first second third vector

def projectionFirst : PairSpace V →ₗ[ℂ] Triple V where
  toFun pair := pair.val.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projectionSecond : PairSpace V →ₗ[ℂ] Triple V where
  toFun pair := pair.val.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) where
  toFun := delta
  map_add' first second := by funext left right; simp [delta]; abel
  map_smul' scalar value := by funext left right; simp [delta, smul_sub]

def liftAC (second : VertexOperator ℂ V) (vector : V) (leftFactor : Bool) :
    (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] Triple V where
  toFun distribution := fun left middle right =>
    if leftFactor then distribution left right ((second [[middle]]) vector)
    else (second [[middle]]) (distribution left right vector)
  map_add' _ _ := by funext left middle right; split <;> simp
  map_smul' _ _ := by funext left middle right; split <;> simp

def liftBC (first : VertexOperator ℂ V) (vector : V) (leftFactor : Bool) :
    (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] Triple V where
  toFun distribution := fun left middle right =>
    if leftFactor then (first [[left]]) (distribution middle right vector)
    else distribution middle right ((first [[left]]) vector)
  map_add' _ _ := by funext left middle right; split <;> simp
  map_smul' _ _ := by funext left middle right; split <;> simp

def liftAB (third : VertexOperator ℂ V) (vector : V) (leftFactor : Bool) :
    (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] Triple V where
  toFun distribution := fun left middle right =>
    if leftFactor then distribution left middle ((third [[right]]) vector)
    else (third [[right]]) (distribution left middle vector)
  map_add' _ _ := by funext left middle right; split <;> simp
  map_smul' _ _ := by funext left middle right; split <;> simp

def evaluate (vector : V) : (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] (ℤ → ℤ → V) where
  toFun distribution := fun first second => distribution first second vector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def plainDelta : Module.End ℂ (ℤ → ℤ → V) where
  toFun := delta
  map_add' first second := by funext left right; simp [delta]; abel
  map_smul' scalar value := by funext left right; simp [delta, smul_sub]

def weighted (distribution : ℤ → ℤ → Module.End ℂ V) : ℤ → ℤ → Module.End ℂ V :=
  fun first second => -(first : ℂ) • distribution (first - 1) second

def flipDistribution : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) where
  toFun distribution := fun first second => distribution second first
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem normalMinusOne_locality (first second third : VertexOperator ℂ V)
    (firstOrder secondOrder thirdOrder : ℕ)
    (firstKilled : delta^[firstOrder] (commutator first third) = 0)
    (secondKilled : delta^[secondOrder] (commutator second third) = 0)
    (thirdKilled : delta^[thirdOrder] (commutator first second) = 0) :
    delta^[firstOrder + secondOrder + thirdOrder]
      (commutator (normalMinusOne first second).val third) = 0 := by
  have residueXY (negative positive : Triple V)
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
    have splitSum (term : ℕ → V) (finite : Function.HasFiniteSupport term) :
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
  have shiftsCommute : Commute (deltaXY (V := V)) deltaYZ := by
    apply LinearMap.ext
    intro pair
    apply Subtype.ext
    ext <;> simp [deltaXY, deltaYZ, shiftXY, shiftYZ] <;> abel
  have residueYZ (pair : PairSpace V) : res (deltaYZ pair) = delta (res pair) := by
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
  have discrepancyXY (pair : PairSpace V) :
      discrepancy (deltaXY pair) = plainXY (discrepancy pair) := by
    funext left middle right
    dsimp [discrepancy, deltaXY, plainXY, shiftXY]
    abel
  have discrepancyYZ (pair : PairSpace V) :
      discrepancy (deltaYZ pair) = plainYZ (discrepancy pair) := by
    funext left middle right
    dsimp [discrepancy, deltaYZ, plainYZ, shiftYZ]
    abel
  have intertwiningPowers {M W : Type u} [AddCommGroup M] [Module ℂ M]
      [AddCommGroup W] [Module ℂ W] (first : Module.End ℂ M) (second : Module.End ℂ W)
      (linear : M →ₗ[ℂ] W) (law : ∀ vector, linear (first vector) = second (linear vector))
      (order : ℕ) (vector : M) : linear ((first ^ order) vector) =
        (second ^ order) (linear vector) := by
    induction order with
    | zero => simp
    | succ order inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  have cancellationBound (pair : PairSpace V) (firstOrder secondOrder thirdOrder : ℕ)
      (annihilated : ((((deltaXY : Module.End ℂ (PairSpace V)) + deltaYZ) ^ firstOrder *
        deltaYZ ^ secondOrder : Module.End ℂ (PairSpace V))) pair = 0)
      (discrepancyKilled : discrepancy ((deltaXY ^ thirdOrder) pair) = 0) :
      delta^[firstOrder + secondOrder + thirdOrder] (res pair) = 0 := by
    let first : Module.End ℂ (PairSpace V) := deltaXY
    let second : Module.End ℂ (PairSpace V) := deltaYZ
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
          have combinedLaw (value : PairSpace V) : discrepancy (combined value) =
              ((plainXY + plainYZ : Module.End ℂ (Triple V))) (discrepancy value) := by
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
        have law := congrArg (fun operator : Module.End ℂ (PairSpace V) => operator value)
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
    have residuePowers (order : ℕ) (value : PairSpace V) :
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
  have increasingFinite (operator : VertexOperator ℂ V) (start : ℤ) (vector : V) :
      Function.HasFiniteSupport (fun offset : ℕ => (operator [[start + offset]]) vector) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (operator vector)).order - start).toNat, ?_⟩
    intro offset member
    contrapose! member
    rw [Function.notMem_support]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  have triplePairCoefficients (first second third : VertexOperator ℂ V) (vector : V) (left
    middle right : ℤ) :
      (triplePair first second third vector).val.1 left middle right =
        (first [[left]]) ((second [[middle]]) ((third [[right]]) vector)) -
          (third [[right]]) ((first [[left]]) ((second [[middle]]) vector)) ∧
      (triplePair first second third vector).val.2 left middle right =
        (second [[middle]]) ((first [[left]]) ((third [[right]]) vector)) -
          (third [[right]]) ((second [[middle]]) ((first [[left]]) vector)) := by
    constructor <;>
      simp only [triplePair, pairAC, pairBC, Submodule.coe_add, Prod.fst_add,
        Prod.snd_add, Pi.add_apply, commutator, LinearMap.sub_apply, Module.End.mul_apply,
        map_sub] <;> abel
  have pairLow (first second third : VertexOperator ℂ V) (vector : V) (firstOrder secondOrder : ℕ)
      (firstKilled : delta^[firstOrder] (commutator first third) = 0)
      (secondKilled : delta^[secondOrder] (commutator second third) = 0) :
      ((((deltaXY + deltaYZ) ^ firstOrder * deltaYZ ^ secondOrder :
        Module.End ℂ (PairSpace V)))) (triplePair first second third vector) = 0 := by
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
    have acLaw (factor : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) :
        liftAC second vector factor (deltaEnd distribution) =
          combinedPlain (liftAC second vector factor distribution) := by
      funext left middle right
      dsimp [liftAC, deltaEnd, delta, combinedPlain, plainXY, plainYZ, shiftXY, shiftYZ]
      cases factor <;> simp only [Bool.false_eq_true, if_false, if_true,
        map_sub] <;> abel
    have bcLaw (factor : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) :
        liftBC first vector factor (deltaEnd distribution) =
          plainYZ (liftBC first vector factor distribution) := by
      funext left middle right
      dsimp [liftBC, deltaEnd, delta, plainYZ, shiftYZ]
      cases factor <;> simp only [Bool.false_eq_true, if_false, if_true,
        map_sub]
    have acKilled : (combined ^ firstOrder) (pairAC first second third vector) = 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change projectionFirst ((combined ^ firstOrder) (pairAC first second third vector)) = 0
        rw [intertwiningPowers combined combinedPlain projectionFirst firstProjection]
        change (combinedPlain ^ firstOrder)
          (liftAC second vector true (commutator first third)) = 0
        rw [← intertwiningPowers deltaEnd combinedPlain (liftAC second vector true) (acLaw true)]
        rw [Module.End.pow_apply]
        change liftAC second vector true (delta^[firstOrder] (commutator first third)) = 0
        rw [firstKilled, map_zero]
      · change projectionSecond ((combined ^ firstOrder) (pairAC first second third vector)) = 0
        rw [intertwiningPowers combined combinedPlain projectionSecond secondProjection]
        change (combinedPlain ^ firstOrder)
          (liftAC second vector false (commutator first third)) = 0
        rw [← intertwiningPowers deltaEnd combinedPlain (liftAC second vector false) (acLaw false)]
        rw [Module.End.pow_apply]
        change liftAC second vector false (delta^[firstOrder] (commutator first third)) = 0
        rw [firstKilled, map_zero]
    have bcKilled : (deltaYZ ^ secondOrder) (pairBC first second third vector) = 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change projectionFirst ((deltaYZ ^ secondOrder) (pairBC first second third vector)) = 0
        rw [intertwiningPowers (deltaYZ (V := V)) (plainYZ (V := V))
          (projectionFirst (V := V)) projectionYZFirst]
        change (plainYZ ^ secondOrder)
          (liftBC first vector true (commutator second third)) = 0
        rw [← intertwiningPowers deltaEnd plainYZ (liftBC first vector true) (bcLaw true)]
        rw [Module.End.pow_apply]
        change liftBC first vector true (delta^[secondOrder] (commutator second third)) = 0
        rw [secondKilled, map_zero]
      · change projectionSecond ((deltaYZ ^ secondOrder) (pairBC first second third vector)) = 0
        rw [intertwiningPowers (deltaYZ (V := V)) (plainYZ (V := V))
          (projectionSecond (V := V)) projectionYZSecond]
        change (plainYZ ^ secondOrder)
          (liftBC first vector false (commutator second third)) = 0
        rw [← intertwiningPowers deltaEnd plainYZ (liftBC first vector false) (bcLaw false)]
        rw [Module.End.pow_apply]
        change liftBC first vector false (delta^[secondOrder] (commutator second third)) = 0
        rw [secondKilled, map_zero]
    change ((combined ^ firstOrder * deltaYZ ^ secondOrder : Module.End ℂ (PairSpace V))) _ = 0
    rw [triplePair, Module.End.mul_apply, map_add, map_add]
    have commute : Commute combined deltaYZ :=
      shiftsCommute.add_left (Commute.refl deltaYZ)
    rw [← Module.End.mul_apply, (commute.pow_pow firstOrder secondOrder).eq,
      Module.End.mul_apply, acKilled, map_zero, bcKilled, map_zero, add_zero]
  have pairHigh (first second third : VertexOperator ℂ V) (vector : V) (order : ℕ)
      (killed : delta^[order] (commutator first second) = 0) :
      discrepancy ((deltaXY ^ order) (triplePair first second third vector)) = 0 := by
    have pairDifference : discrepancy (triplePair first second third vector) =
        (liftAB third vector true - liftAB third vector false) (commutator first second) := by
      funext left middle right
      rw [show discrepancy (triplePair first second third vector) left middle right =
        (triplePair first second third vector).val.1 left middle right -
        (triplePair first second third vector).val.2 left middle right by rfl,
        (triplePairCoefficients first second third vector left middle right).1,
        (triplePairCoefficients first second third vector left middle right).2]
      simp only [liftAB, LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk,
        if_true, Bool.false_eq_true, if_false, commutator, Module.End.mul_apply, map_sub,
        Pi.sub_apply]
      abel
    let lifting := liftAB third vector true - liftAB third vector false
    have liftingLaw (distribution : ℤ → ℤ → Module.End ℂ V) :
        lifting (deltaEnd distribution) = plainXY (lifting distribution) := by
      funext left middle right
      dsimp [lifting, liftAB, deltaEnd, delta, plainXY, shiftXY]
      simp only [map_sub]
      abel
    rw [intertwiningPowers (deltaXY (V := V)) (plainXY (V := V))
        (discrepancy (V := V)) discrepancyXY, pairDifference,
      ← intertwiningPowers deltaEnd plainXY lifting liftingLaw]
    rw [Module.End.pow_apply]
    change lifting (delta^[order] (commutator first second)) = 0
    rw [killed, map_zero]
  have residueTriplePair (first second third : VertexOperator ℂ V) (vector : V) :
      res (triplePair first second third vector) =
        fun left right => commutator (normalMinusOne first second).val third left right vector := by
    funext left right
    have forwardFinite (value : V) : Function.HasFiniteSupport
        (fun offset : ℕ => (first [[-(offset : ℤ) - 1]]) ((second [[left + offset]]) value)) := by
      refine (increasingFinite second left value).subset ?_
      intro offset member vanish
      apply member
      change (first [[-(offset : ℤ) - 1]]) ((second [[left + offset]]) value) = 0
      change (second [[left + offset]]) value = 0 at vanish
      rw [vanish, map_zero]
    have reverseFinite (value : V) : Function.HasFiniteSupport
        (fun offset : ℕ => (second [[left - offset - 1]]) ((first [[offset]]) value)) := by
      refine (increasingFinite first 0 value).subset ?_
      intro offset member vanish
      apply member
      change (second [[left - offset - 1]]) ((first [[offset]]) value) = 0
      change (first [[(0 : ℤ) + offset]]) value = 0 at vanish
      rw [zero_add] at vanish
      rw [vanish, map_zero]
    change residue (triplePair first second third vector).val.1
      (triplePair first second third vector).val.2 left right = _
    unfold residue
    simp_rw [(triplePairCoefficients first second third vector _ _ right).1,
      (triplePairCoefficients first second third vector _ _ right).2]
    have mappedForwardFinite : Function.HasFiniteSupport (fun offset : ℕ => (third [[right]])
        ((first [[-(offset : ℤ) - 1]]) ((second [[left + offset]]) vector))) := by
      simpa only [Function.comp_def] using (forwardFinite vector).comp (third [[right]]).map_zero
    have mappedReverseFinite : Function.HasFiniteSupport (fun offset : ℕ => (third [[right]])
        ((second [[left - offset - 1]]) ((first [[offset]]) vector))) := by
      simpa only [Function.comp_def] using (reverseFinite vector).comp (third [[right]]).map_zero
    rw [finsum_sub_distrib (forwardFinite ((third [[right]]) vector))
        mappedForwardFinite,
      finsum_sub_distrib (reverseFinite ((third [[right]]) vector))
        mappedReverseFinite]
    rw [← map_finsum (third [[right]]) (forwardFinite vector),
      ← map_finsum (third [[right]]) (reverseFinite vector)]
    rw [commutator, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      (normalMinusOne first second).property, (normalMinusOne first second).property, map_add]
    abel
  funext left right
  apply LinearMap.ext
  intro vector
  have cancelled := cancellationBound (triplePair first second third vector)
    firstOrder secondOrder thirdOrder (pairLow first second third vector firstOrder secondOrder
      firstKilled secondKilled) (pairHigh first second third vector thirdOrder thirdKilled)
  rw [residueTriplePair] at cancelled
  have evaluationLaw (distribution : ℤ → ℤ → Module.End ℂ V) :
      evaluate vector (deltaEnd distribution) = plainDelta (evaluate vector distribution) := rfl
  have transport := intertwiningPowers deltaEnd plainDelta (evaluate vector) evaluationLaw
    (firstOrder + secondOrder + thirdOrder) (commutator (normalMinusOne first second).val third)
  rw [Module.End.pow_apply, Module.End.pow_apply] at transport
  change evaluate vector (delta^[firstOrder + secondOrder + thirdOrder]
      (commutator (normalMinusOne first second).val third)) =
    delta^[firstOrder + secondOrder + thirdOrder]
      (fun left right => commutator (normalMinusOne first second).val third left right vector)
        at transport
  rw [cancelled] at transport
  exact congrFun (congrFun transport left) right

theorem dividedDerivative_locality (first second : VertexOperator ℂ V) (order degree : ℕ)
    (killed : delta^[order] (commutator first second) = 0) :
    delta^[order + degree] (commutator (dividedDerivative degree first) second) = 0 := by
  have leftDerivativeLocal (first second : VertexOperator ℂ V) (order : ℕ)
      (killed : delta^[order] (commutator first second) = 0) :
      delta^[order + 1] (commutator (dividedDerivative 1 first) second) = 0 := by
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
    have differentiated : commutator (dividedDerivative 1 first) second = weighted (commutator
      first second) := by
      funext left right
      rw [commutator, modes, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
      rfl
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
    have next : delta^[order + 1] (commutator first second) = 0 := by
      rw [Function.iterate_succ_apply', killed]
      funext left right
      simp [delta]
    rw [killed, next]
    funext left right
    simp [weighted]
  have successive : ∀ count : ℕ,
      delta^[order + count] (commutator ((dividedDerivative 1)^[count] first) second) = 0 := by
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
  have scaled : commutator ((degree.factorial : ℂ) • dividedDerivative degree first) second =
      (degree.factorial : ℂ) • commutator (dividedDerivative degree first) second := by
    funext left right
    simp only [commutator, map_smul, Pi.smul_apply, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, ← smul_sub]
  have result := successive degree
  rw [identity, scaled] at result
  have linearity : delta^[order + degree]
      ((degree.factorial : ℂ) • commutator (dividedDerivative degree first) second) =
      (degree.factorial : ℂ) • delta^[order + degree]
        (commutator (dividedDerivative degree first) second) := by
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order + degree] _ =
      (degree.factorial : ℂ) • (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order + degree] _
    rw [← Module.End.pow_apply, ← Module.End.pow_apply, map_smul]
  rw [linearity] at result
  exact (smul_eq_zero.mp result).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero degree))

end D5.S3.VertexAlgebra.FieldNormalProductLocality
