/- GID: D5/S3/VertexAlgebra/SuperStateFieldReconstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SuperStateFieldReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed relative-vacuum uniqueness from actual creation, covariance and parity-locality. -/

import D5.S3.VertexAlgebra.SuperFieldLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.SuperStateFieldReconstruction

open D5.S3.VertexAlgebra
open SuperFieldProducts SuperFieldLocality
open FieldNormalProduct
open scoped VertexOperator

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem delta_binomial (distribution : ℤ → ℤ → Module.End ℂ V)
    (order : ℕ) (first second : ℤ) :
    (SuperFieldProducts.delta^[order] distribution) first second =
      ∑ offset ∈ Finset.range (order + 1),
        ((-1 : ℂ) ^ offset * (order.choose offset : ℂ)) •
          distribution (first + (order : ℤ) - offset) (second + offset) := by
  let shiftLeft : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun left right => value (left + 1) right
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun left right => value left (right + 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have commute : Commute (-shiftRight) shiftLeft := by
    apply LinearMap.ext
    intro value
    funext left right
    simp [shiftLeft, shiftRight]
  have leftPower (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ V) :
      (shiftLeft ^ degree) value = fun left right => value (left + degree) right := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
      funext left right
      change value (left + 1 + degree) right = value (left + (degree + 1 : ℕ)) right
      congr 1
      push_cast
      omega
  have rightPower (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ V) :
      ((-shiftRight) ^ degree) value = fun left right =>
        (-1 : ℂ) ^ degree • value left (right + degree) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
      funext left right
      change -((-1 : ℂ) ^ degree • value left (right + 1 + degree)) =
        (-1 : ℂ) ^ (degree + 1) • value left (right + (degree + 1 : ℕ))
      rw [pow_succ', mul_smul, neg_one_smul]
      have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by
        push_cast
        omega
      rw [indices]
  have equation :
      (FieldNormalProductLocality.deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V)) =
        -shiftRight + shiftLeft := by
    apply LinearMap.ext
    intro value
    funext left right
    simp [FieldNormalProductLocality.deltaEnd, FieldNormalProductLocality.delta,
      shiftLeft, shiftRight]
    abel
  change (FieldNormalProductLocality.delta^[order] distribution) first second = _
  rw [delta_iterate_eq_pow]
  rw [equation, commute.add_pow, LinearMap.sum_apply]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro offset member
  have within : offset ≤ order := by simpa using Finset.mem_range.mp member
  simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
    rightPower, leftPower, Pi.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]
  congr 2
  push_cast [Int.natCast_sub within]
  omega

theorem relative_vacuum_uniqueness
    (Y : V →ₗ[ℂ] VertexOperator ℂ V) (vacuum : V) (translation : Module.End ℂ V)
    (parts : ℕ → Module.End ℂ V) (grades : ℕ → Submodule ℂ V)
    (decomposition : ∀ state, parts 0 state + parts 1 state = state)
    (parts_mem : ∀ parity state, parts parity state ∈ grades parity)
    (translation_vacuum : translation vacuum = 0)
    (state_creation : ∀ state, ((Y state)[[-1]]) vacuum = state)
    (state_creativity : ∀ state mode, 0 ≤ mode → ((Y state)[[mode]]) vacuum = 0)
    (parity : ℕ) (operator : VertexOperator ℂ V)
    (creative : ∀ mode : ℤ, 0 ≤ mode → (operator[[mode]]) vacuum = 0)
    (initial : (operator[[-1]]) vacuum = 0)
    (covariant : ∀ mode : ℤ, translation * (operator[[mode]]) - (operator[[mode]]) * translation =
      -(mode : ℂ) • (operator[[mode - 1]]))
    (relative : ∀ grade : ℕ, ∀ state ∈ grades grade,
      SuperLocal parity grade operator (Y state)) : operator = 0 := by
  have vacuumNegative (degree : ℕ) : (operator[[-(degree : ℤ) - 1]]) vacuum = 0 := by
    induction degree with
    | zero => simpa using initial
    | succ degree inductionHypothesis =>
      have law := congrArg (fun endomorphism : Module.End ℂ V =>
        endomorphism vacuum) (covariant (-(degree : ℤ) - 1))
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        inductionHypothesis, translation_vacuum, map_zero, sub_self] at law
      rw [show -(degree : ℤ) - 1 - 1 = -((degree + 1 : ℕ) : ℤ) - 1 by omega] at law
      have scalar : -((-(degree : ℤ) - 1 : ℤ) : ℂ) = (degree : ℂ) + 1 := by
        push_cast
        ring
      rw [scalar] at law
      have nonzero : (degree : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
      exact (smul_eq_zero.mp law.symm).resolve_left nonzero
  have vacuumZero (mode : ℤ) : (operator[[mode]]) vacuum = 0 := by
    by_cases nonnegative : 0 ≤ mode
    · exact creative mode nonnegative
    · let degree := (-mode - 1).toNat
      rw [show mode = -(degree : ℤ) - 1 by dsimp [degree]; omega]
      exact vacuumNegative degree
  have homogeneousModes (grade : ℕ) (state : V) (stateHomogeneous : state ∈ grades grade)
      (mode : ℤ) : (operator[[mode]]) state = 0 := by
    obtain ⟨order, killed⟩ := relative grade state stateHomogeneous
    have coefficient := congrArg (fun value : ℤ → ℤ → Module.End ℂ V =>
      value (mode - order) (-1) vacuum) killed
    rw [delta_binomial, LinearMap.sum_apply] at coefficient
    simp only [LinearMap.smul_apply] at coefficient
    have simplify : (∑ offset ∈ Finset.range (order + 1),
        ((-1 : ℂ) ^ offset * (order.choose offset : ℂ)) •
          superCommutator (koszul parity grade) operator (Y state)
            (mode - order + (order : ℤ) - offset) (-1 + offset) vacuum) =
        (operator[[mode]]) state := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul,
          Nat.cast_zero, sub_zero, add_zero, show mode - (order : ℤ) + order = mode by omega,
          superCommutator, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
          vacuumZero, map_zero, smul_zero, sub_zero, state_creation]
      · intro offset member distinct
        have vanish : ((Y state)[[-1 + (offset : ℤ)]]) vacuum = 0 :=
          state_creativity state _ (by omega)
        simp only [superCommutator, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.mul_apply, vanish, vacuumZero, map_zero, smul_zero, sub_self]
      · simp
    rw [simplify] at coefficient
    exact coefficient
  have allModes (mode : ℤ) (state : V) : (operator[[mode]]) state = 0 := by
    rw [← decomposition state, map_add,
      homogeneousModes 0 _ (parts_mem 0 state) mode,
      homogeneousModes 1 _ (parts_mem 1 state) mode, add_zero]
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro vector
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply] using allModes (-power - 1) vector

theorem positive_residue_modes (exchange : ℂ) (firstField secondField : VertexOperator ℂ V)
    (degree : ℕ) (mode : ℤ) (vector : V) :
    ((residue exchange (degree : ℤ) firstField secondField)[[mode]]) vector =
      ((FieldNormalProductLocality.deltaEnd ^ degree) (superCommutator exchange firstField secondField)) 0 mode vector := by
  have chooseNat (offset : ℕ) : weight (degree : ℤ) offset =
      (-1 : ℂ) ^ offset * (degree.choose offset : ℂ) := by
    simp [weight, integerBinomial, Ring.choose_natCast]
  have leftSum : residueLeft (degree : ℤ) mode firstField secondField vector =
      ∑ offset ∈ Finset.range (degree + 1),
        ((-1 : ℂ) ^ offset * (degree.choose offset : ℂ)) •
          (firstField[[(degree : ℤ) - offset]]) ((secondField[[mode + offset]]) vector) := by
    unfold residueLeft
    simp_rw [chooseNat]
    apply finsum_eq_sum_of_support_subset
    intro offset member
    by_contra outside
    have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    exact member (by simp [zeroChoose])
  have rightSum : residueRight (degree : ℤ) mode firstField secondField vector =
      ∑ offset ∈ Finset.range (degree + 1),
        ((-1 : ℂ) ^ offset * (degree.choose offset : ℂ)) •
          (secondField[[(degree : ℤ) + mode - offset]]) ((firstField[[offset]]) vector) := by
    unfold residueRight
    simp_rw [chooseNat]
    apply finsum_eq_sum_of_support_subset
    intro offset member
    by_contra outside
    have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    exact member (by simp [zeroChoose])
  rw [residue_modes]
  change residueLeft (degree : ℤ) mode firstField secondField vector -
    (epsilon (degree : ℤ) * exchange) • residueRight (degree : ℤ) mode firstField secondField vector = _
  have expansion := delta_binomial (superCommutator exchange firstField secondField) degree 0 mode
  change (FieldNormalProductLocality.delta^[degree]
    (superCommutator exchange firstField secondField)) 0 mode = _ at expansion
  rw [delta_iterate_eq_pow] at expansion
  rw [leftSum, rightSum, expansion, LinearMap.sum_apply]
  simp only [zero_add, LinearMap.smul_apply, superCommutator, Module.End.mul_apply,
    LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib]
  apply congrArg ((∑ offset ∈ Finset.range (degree + 1),
    ((-1 : ℂ) ^ offset * (degree.choose offset : ℂ)) •
      (firstField[[(degree : ℤ) - offset]]) ((secondField[[mode + offset]]) vector)) - ·)
  rw [Finset.smul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro offset member
  have within : offset ≤ degree := by simpa using Finset.mem_range.mp member
  simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, epsilon, zpow_natCast]
  have signs : (-1 : ℂ) ^ degree *
      ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) =
        (-1 : ℂ) ^ offset * (degree.choose offset : ℂ) := by
    have split : (-1 : ℂ) ^ degree = (-1 : ℂ) ^ offset * (-1 : ℂ) ^ (degree - offset) := by
      rw [← pow_add, Nat.add_sub_of_le within]
    rw [split]
    have squared : ((-1 : ℂ) ^ (degree - offset)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc
      _ = (-1 : ℂ) ^ offset * ((-1 : ℂ) ^ (degree - offset)) ^ 2 *
          (degree.choose offset : ℂ) := by ring
      _ = _ := by rw [squared]; ring
  have signed : ((-1 : ℂ) ^ degree * exchange) *
      ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) =
        ((-1 : ℂ) ^ offset * (degree.choose offset : ℂ)) * exchange := by
    calc
      _ = ((-1 : ℂ) ^ degree *
          ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ))) * exchange := by ring
      _ = _ := by rw [signs]
  rw [signed]
  push_cast [Int.natCast_sub within]
  rw [show (degree : ℤ) + mode - ((degree : ℤ) - offset) = mode + offset by omega]

theorem nonnegative_residue_locality (exchangeAB exchangeAC exchangeBC : ℂ)
    (firstField secondField thirdField : VertexOperator ℂ V) (residueDegree : ℕ)
    (firstOrder secondOrder thirdOrder : ℕ)
    (firstKilled : (FieldNormalProductLocality.deltaEnd ^ firstOrder) (superCommutator exchangeAC firstField thirdField) = 0)
    (secondKilled : (FieldNormalProductLocality.deltaEnd ^ secondOrder) (superCommutator exchangeBC secondField thirdField) = 0)
    (thirdKilled : (FieldNormalProductLocality.deltaEnd ^ thirdOrder) (superCommutator exchangeAB firstField secondField) = 0) :
    ∃ order : ℕ, SuperFieldProducts.delta^[order]
      (superCommutator (exchangeAC * exchangeBC)
        (residue exchangeAB (residueDegree : ℤ) firstField secondField) thirdField) = 0 := by
  classical
  have positiveModes := positive_residue_modes exchangeAB firstField secondField residueDegree
  let order := if thirdOrder ≤ residueDegree then 0 else firstOrder + thirdOrder - residueDegree - 1 + secondOrder
  have cancellation (vector : V) : ((FieldNormalProductLocality.plainYZ ^ order * FieldNormalProductLocality.plainXY ^ residueDegree : Module.End ℂ (FieldNormalProductLocality.Triple V)) (fun left middle right =>
          superCommutator exchangeAB firstField secondField left middle (((thirdField [[right]])) vector) - (exchangeAC * exchangeBC) • ((thirdField [[right]])) (superCommutator exchangeAB firstField secondField left
            middle vector))) = 0 := by
    dsimp only [order]
    let first : Module.End ℂ (FieldNormalProductLocality.Triple V) := FieldNormalProductLocality.plainXY
    let second : Module.End ℂ (FieldNormalProductLocality.Triple V) := FieldNormalProductLocality.plainYZ
    let combined := first + second
    have commuting : Commute first second := by
      apply LinearMap.ext; intro distribution; funext left middle right; dsimp [first, second, FieldNormalProductLocality.plainXY, FieldNormalProductLocality.plainYZ, FieldNormalProductLocality.shiftXY, FieldNormalProductLocality.shiftYZ]
      abel
    have combinedFirst : Commute combined first := (Commute.refl first).add_left commuting.symm
    have combinedSecond : Commute combined second := commuting.add_left (Commute.refl second)
    have intertwiningPowersOT
        (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))
        (target : Module.End ℂ (FieldNormalProductLocality.Triple V))
        (linear : (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] FieldNormalProductLocality.Triple V)
        (law : ∀ value, linear (source value) = target (linear value))
        (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ V) :
        linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        simp only [pow_succ', Module.End.mul_apply]
        rw [law, inductionHypothesis]
    have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : FieldNormalProductLocality.liftAB thirdField vector side (FieldNormalProductLocality.deltaEnd distribution) = first (FieldNormalProductLocality.liftAB thirdField vector side distribution) := by
      funext left middle right; dsimp [FieldNormalProductLocality.liftAB, FieldNormalProductLocality.deltaEnd, FieldNormalProductLocality.delta, first, FieldNormalProductLocality.plainXY, FieldNormalProductLocality.shiftXY]
      cases side <;> simp [map_sub]
    have lawAC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : FieldNormalProductLocality.liftAC secondField vector side (FieldNormalProductLocality.deltaEnd distribution) = combined (FieldNormalProductLocality.liftAC secondField vector side distribution) := by
      funext left middle right; dsimp [FieldNormalProductLocality.liftAC, FieldNormalProductLocality.deltaEnd, FieldNormalProductLocality.delta, combined, first, second, FieldNormalProductLocality.plainXY, FieldNormalProductLocality.plainYZ, FieldNormalProductLocality.shiftXY, FieldNormalProductLocality.shiftYZ]
      cases side <;> simp [map_sub]
    have lawBC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : FieldNormalProductLocality.liftBC firstField vector side (FieldNormalProductLocality.deltaEnd distribution) = second (FieldNormalProductLocality.liftBC firstField vector side distribution) := by
      funext left middle right; dsimp [FieldNormalProductLocality.liftBC, FieldNormalProductLocality.deltaEnd, FieldNormalProductLocality.delta, second, FieldNormalProductLocality.plainYZ, FieldNormalProductLocality.shiftYZ]
      cases side <;> simp [map_sub]
    let discrepancy := FieldNormalProductLocality.liftAB thirdField vector true (superCommutator exchangeAB firstField secondField) - (exchangeAC * exchangeBC) • FieldNormalProductLocality.liftAB thirdField vector false (superCommutator exchangeAB firstField secondField)
    let firstPart := exchangeBC • FieldNormalProductLocality.liftAC secondField vector true (superCommutator exchangeAC firstField thirdField) - exchangeAB • FieldNormalProductLocality.liftAC secondField vector false (superCommutator exchangeAC firstField thirdField)
    let secondPart := FieldNormalProductLocality.liftBC firstField vector true (superCommutator exchangeBC secondField thirdField) - (exchangeAB * exchangeAC) • FieldNormalProductLocality.liftBC firstField vector false (superCommutator exchangeBC secondField thirdField)
    have jacobi : discrepancy = firstPart + secondPart := by
      funext left middle right; dsimp [discrepancy, firstPart, secondPart, FieldNormalProductLocality.liftAB, FieldNormalProductLocality.liftAC, FieldNormalProductLocality.liftBC, superCommutator]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sub, map_smul]; module
    have discrepancyKilled : (first ^ thirdOrder) discrepancy = 0 := by
      dsimp [discrepancy]
      rw [map_sub, map_smul, ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd first (FieldNormalProductLocality.liftAB thirdField vector true) (lawAB true), ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd first (FieldNormalProductLocality.liftAB thirdField vector false) (lawAB false), thirdKilled]
      simp
    have firstPartKilled : (combined ^ firstOrder) firstPart = 0 := by
      dsimp [firstPart]
      rw [map_sub, map_smul, map_smul, ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd combined (FieldNormalProductLocality.liftAC secondField vector true) (lawAC true), ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd combined (FieldNormalProductLocality.liftAC secondField vector false) (lawAC false), firstKilled]
      simp
    have secondPartKilled : (second ^ secondOrder) secondPart = 0 := by
      dsimp [secondPart]
      rw [map_sub, map_smul, ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd second (FieldNormalProductLocality.liftBC firstField vector true) (lawBC true), ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd second (FieldNormalProductLocality.liftBC firstField vector false) (lawBC false), secondKilled]
      simp
    have annihilated : (combined ^ firstOrder * second ^ secondOrder) discrepancy = 0 := by
      rw [jacobi, map_add]
      have firstVanish : (combined ^ firstOrder * second ^ secondOrder) firstPart = 0 := by rw [(combinedSecond.pow_pow _ _).eq, Module.End.mul_apply, firstPartKilled, map_zero]
      have secondVanish : (combined ^ firstOrder * second ^ secondOrder) secondPart = 0 := by rw [Module.End.mul_apply, secondPartKilled, map_zero]
      rw [firstVanish, secondVanish, add_zero]
    have high (power : ℕ) (large : thirdOrder ≤ power) : (first ^ power) discrepancy = 0 := by
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le large
      rw [pow_add, (Commute.refl first).pow_pow _ _ |>.eq, Module.End.mul_apply, discrepancyKilled, map_zero]
    by_cases large : thirdOrder ≤ residueDegree
    · simp only [if_pos large]
      change (second ^ 0 * first ^ residueDegree) discrepancy = 0; simp [high residueDegree large]
    · let exponent := firstOrder + thirdOrder - residueDegree - 1
      simp only [if_neg large]; change (second ^ (exponent + secondOrder) * first ^ residueDegree) discrepancy = 0
      have low (degree : ℕ) (largeDegree : firstOrder ≤ degree) : (combined ^ degree * second ^ secondOrder) discrepancy = 0 := by
        obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le largeDegree
        rw [pow_add, (Commute.refl combined).pow_pow _ _ |>.eq, mul_assoc, Module.End.mul_apply, annihilated, map_zero]
      have minusCommute : Commute combined (-first) := by
        apply LinearMap.ext; intro value
        have law := congrArg (fun operator : Module.End ℂ (FieldNormalProductLocality.Triple V) => operator value) combinedFirst.eq
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
      · have vanish : (combined ^ degree) ((first ^ (exponent - degree)) ((second ^ secondOrder) ((first ^ residueDegree) discrepancy))) = 0 := by
          change (combined ^ degree * first ^ (exponent - degree) * second ^ secondOrder * first ^ residueDegree) discrepancy = 0
          rw [(combinedFirst.pow_pow degree (exponent - degree)).eq]
          have move := (combinedFirst.pow_pow degree residueDegree).mul_left (commuting.symm.pow_pow secondOrder residueDegree)
          have reorder : first ^ (exponent - degree) * combined ^ degree * second ^ secondOrder * first ^ residueDegree = first ^ (exponent - degree) * first ^ residueDegree * (combined ^ degree * second
            ^ secondOrder) := by
            calc
              _ = first ^ (exponent - degree) * ((combined ^ degree * second ^ secondOrder) * first ^ residueDegree) := by simp only [mul_assoc]
              _ = _ := by rw [move.eq]; simp only [mul_assoc]
          rw [reorder, Module.End.mul_apply, low degree largeDegree, map_zero]
        simp [vanish]
      · have bound : thirdOrder ≤ exponent - degree + residueDegree := by
          have within : degree ≤ exponent := by simpa using Finset.mem_range.mp member
          dsimp [exponent]; omega
        have vanish : (first ^ (exponent - degree)) ((second ^ secondOrder) ((first ^ residueDegree) discrepancy)) = 0 := by
          change (first ^ (exponent - degree) * second ^ secondOrder * first ^ residueDegree) discrepancy = 0
          rw [(commuting.pow_pow _ _).eq, mul_assoc, ← pow_add, Module.End.mul_apply, high _ bound, map_zero]
        simp [vanish]
  refine ⟨order, ?_⟩; funext left right; apply LinearMap.ext; intro vector
  let extract : FieldNormalProductLocality.Triple V →ₗ[ℂ] (ℤ → ℤ → V) := {
    toFun distribution := distribution 0
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have intertwiningPowersTV
      (source : Module.End ℂ (FieldNormalProductLocality.Triple V))
      (target : Module.End ℂ (ℤ → ℤ → V))
      (linear : FieldNormalProductLocality.Triple V →ₗ[ℂ] (ℤ → ℤ → V))
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : FieldNormalProductLocality.Triple V) :
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
  have extractLaw (distribution : FieldNormalProductLocality.Triple V) : extract (FieldNormalProductLocality.plainYZ distribution) = FieldNormalProductLocality.plainDelta (extract distribution) := by rfl
  have evaluateLaw (distribution : ℤ → ℤ → Module.End ℂ V) : FieldNormalProductLocality.evaluate vector (FieldNormalProductLocality.deltaEnd distribution) = FieldNormalProductLocality.plainDelta (FieldNormalProductLocality.evaluate vector distribution) := by rfl
  have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ V) : FieldNormalProductLocality.liftAB thirdField vector side (FieldNormalProductLocality.deltaEnd distribution) = FieldNormalProductLocality.plainXY (FieldNormalProductLocality.liftAB thirdField vector side distribution) := by
    funext first middle third; dsimp [FieldNormalProductLocality.liftAB, FieldNormalProductLocality.deltaEnd, FieldNormalProductLocality.delta, FieldNormalProductLocality.plainXY, FieldNormalProductLocality.shiftXY]
    cases side <;> simp [map_sub]
  have intertwiningPowersOT
      (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))
      (target : Module.End ℂ (FieldNormalProductLocality.Triple V))
      (linear : (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] FieldNormalProductLocality.Triple V)
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ V) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  let discrepancy := FieldNormalProductLocality.liftAB thirdField vector true (superCommutator exchangeAB firstField secondField) - (exchangeAC * exchangeBC) • FieldNormalProductLocality.liftAB thirdField vector false (superCommutator exchangeAB firstField secondField)
  have connection : extract ((FieldNormalProductLocality.plainXY ^ residueDegree) discrepancy) = FieldNormalProductLocality.evaluate vector (superCommutator (exchangeAC * exchangeBC) (residue exchangeAB (residueDegree : ℤ) firstField secondField) thirdField) := by
    dsimp only [discrepancy]
    rw [map_sub, map_smul, map_sub, map_smul, ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd FieldNormalProductLocality.plainXY (FieldNormalProductLocality.liftAB thirdField vector true) (lawAB true), ← intertwiningPowersOT FieldNormalProductLocality.deltaEnd FieldNormalProductLocality.plainXY (FieldNormalProductLocality.liftAB thirdField vector false) (lawAB
      false)]
    funext first second; dsimp [extract, FieldNormalProductLocality.liftAB, FieldNormalProductLocality.evaluate, superCommutator]
    rw [← positiveModes first (((thirdField [[second]])) vector), ← positiveModes first vector]
  have killed := congrArg (fun distribution : FieldNormalProductLocality.Triple V => extract distribution) (cancellation vector)
  change extract ((FieldNormalProductLocality.plainYZ ^ order) ((FieldNormalProductLocality.plainXY ^ residueDegree) discrepancy)) = extract 0 at killed
  rw [intertwiningPowersTV FieldNormalProductLocality.plainYZ FieldNormalProductLocality.plainDelta extract extractLaw, connection, ← intertwiningPowersEV FieldNormalProductLocality.deltaEnd FieldNormalProductLocality.plainDelta (FieldNormalProductLocality.evaluate vector) evaluateLaw, map_zero] at killed
  have coefficient := congrFun (congrFun killed left) right
  change ((FieldNormalProductLocality.deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] (superCommutator (exchangeAC * exchangeBC) (residue exchangeAB (residueDegree : ℤ) firstField secondField) thirdField)) left right vector = 0
  rw [← Module.End.pow_apply]; exact coefficient

theorem residue_superLocal (leftParity rightParity otherParity : ℕ)
    (left right other : VertexOperator ℂ V) (parameter : ℤ)
    (leftOther : SuperLocal leftParity otherParity left other)
    (rightOther : SuperLocal rightParity otherParity right other)
    (leftRight : SuperLocal leftParity rightParity left right) :
    SuperLocal (leftParity + rightParity) otherParity
      (residue (koszul leftParity rightParity) parameter left right) other := by
  by_cases nonnegative : 0 ≤ parameter
  · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
    obtain ⟨firstOrder, firstKilled⟩ := leftOther
    obtain ⟨secondOrder, secondKilled⟩ := rightOther
    obtain ⟨thirdOrder, thirdKilled⟩ := leftRight
    have firstKilledEnd : (FieldNormalProductLocality.deltaEnd ^ firstOrder)
        (superCommutator (koszul leftParity otherParity) left other) = 0 := by
      rw [Module.End.pow_apply]
      exact firstKilled
    have secondKilledEnd : (FieldNormalProductLocality.deltaEnd ^ secondOrder)
        (superCommutator (koszul rightParity otherParity) right other) = 0 := by
      rw [Module.End.pow_apply]
      exact secondKilled
    have thirdKilledEnd : (FieldNormalProductLocality.deltaEnd ^ thirdOrder)
        (superCommutator (koszul leftParity rightParity) left right) = 0 := by
      rw [Module.End.pow_apply]
      exact thirdKilled
    obtain ⟨order, killed⟩ := nonnegative_residue_locality (koszul leftParity rightParity)
      (koszul leftParity otherParity) (koszul rightParity otherParity) left right other
      degree firstOrder secondOrder thirdOrder firstKilledEnd secondKilledEnd thirdKilledEnd
    refine ⟨order, ?_⟩
    rw [koszul_add_left]
    exact killed
  · let degree := (-parameter - 1).toNat
    have index : parameter = -(degree : ℤ) - 1 := by dsimp [degree]; omega
    rw [index, negative_residue_normal]
    exact normal_superLocal leftParity rightParity otherParity
      (dividedDerivative degree left) right other
      (dividedDerivative_superLocal leftParity otherParity degree left other leftOther)
      rightOther (dividedDerivative_superLocal leftParity rightParity degree left right leftRight)

end D5.S3.VertexAlgebra.SuperStateFieldReconstruction
