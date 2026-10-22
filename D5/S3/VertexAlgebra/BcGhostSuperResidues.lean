/- GID: D5/S3/VertexAlgebra/BcGhostSuperResidues
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostSuperResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed nonnegative-residue Dong locality, arbitrary-integer homogeneous residue closure, and the four-component even/odd mixed residue expansion for arbitrary original states. Each branch keeps its own Koszul exchange sign and original mode product. -/

import D5.S3.VertexAlgebra.BcGhostSuperReconstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostSuperResidues

open BcGhostFockSupport BcGhostSuperGenerators BcGhostSuperStateField BcGhostSuperLocality
open BcGhostSuperReconstruction FieldNormalProduct SuperFieldProducts SuperFieldLocality
open FieldNormalProductLocality (deltaEnd Triple plainXY plainYZ shiftXY shiftYZ
  liftAB liftAC liftBC evaluate plainDelta)
open scoped VertexOperator

noncomputable section

theorem positive_residue_modes (exchange : ℂ) (firstField secondField : VertexOperator ℂ Carrier)
    (degree : ℕ) (mode : ℤ) (vector : Carrier) :
    ((residue exchange (degree : ℤ) firstField secondField)[[mode]]) vector =
      ((deltaEnd ^ degree) (superCommutator exchange firstField secondField)) 0 mode vector := by
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
    (firstField secondField thirdField : VertexOperator ℂ Carrier) (residueDegree : ℕ)
    (firstOrder secondOrder thirdOrder : ℕ)
    (firstKilled : (deltaEnd ^ firstOrder) (superCommutator exchangeAC firstField thirdField) = 0)
    (secondKilled : (deltaEnd ^ secondOrder) (superCommutator exchangeBC secondField thirdField) = 0)
    (thirdKilled : (deltaEnd ^ thirdOrder) (superCommutator exchangeAB firstField secondField) = 0) :
    ∃ order : ℕ, SuperFieldProducts.delta^[order]
      (superCommutator (exchangeAC * exchangeBC)
        (residue exchangeAB (residueDegree : ℤ) firstField secondField) thirdField) = 0 := by
  classical
  have positiveModes := positive_residue_modes exchangeAB firstField secondField residueDegree
  let order := if thirdOrder ≤ residueDegree then 0 else firstOrder + thirdOrder - residueDegree - 1 + secondOrder
  have cancellation (vector : Carrier) : ((plainYZ ^ order * plainXY ^ residueDegree : Module.End ℂ (Triple Carrier)) (fun left middle right =>
          superCommutator exchangeAB firstField secondField left middle (((thirdField [[right]])) vector) - (exchangeAC * exchangeBC) • ((thirdField [[right]])) (superCommutator exchangeAB firstField secondField left
            middle vector))) = 0 := by
    dsimp only [order]
    let first : Module.End ℂ (Triple Carrier) := plainXY
    let second : Module.End ℂ (Triple Carrier) := plainYZ
    let combined := first + second
    have commuting : Commute first second := by
      apply LinearMap.ext; intro distribution; funext left middle right; dsimp [first, second, plainXY, plainYZ, shiftXY, shiftYZ]
      abel
    have combinedFirst : Commute combined first := (Commute.refl first).add_left commuting.symm
    have combinedSecond : Commute combined second := commuting.add_left (Commute.refl second)
    have intertwiningPowersOT
        (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ Carrier))
        (target : Module.End ℂ (Triple Carrier))
        (linear : (ℤ → ℤ → Module.End ℂ Carrier) →ₗ[ℂ] Triple Carrier)
        (law : ∀ value, linear (source value) = target (linear value))
        (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Carrier) :
        linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        simp only [pow_succ', Module.End.mul_apply]
        rw [law, inductionHypothesis]
    have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Carrier) : liftAB thirdField vector side (deltaEnd distribution) = first (liftAB thirdField vector side distribution) := by
      funext left middle right; dsimp [liftAB, deltaEnd, FieldNormalProductLocality.delta, first, plainXY, shiftXY]
      cases side <;> simp [map_sub]
    have lawAC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Carrier) : liftAC secondField vector side (deltaEnd distribution) = combined (liftAC secondField vector side distribution) := by
      funext left middle right; dsimp [liftAC, deltaEnd, FieldNormalProductLocality.delta, combined, first, second, plainXY, plainYZ, shiftXY, shiftYZ]
      cases side <;> simp [map_sub]
    have lawBC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Carrier) : liftBC firstField vector side (deltaEnd distribution) = second (liftBC firstField vector side distribution) := by
      funext left middle right; dsimp [liftBC, deltaEnd, FieldNormalProductLocality.delta, second, plainYZ, shiftYZ]
      cases side <;> simp [map_sub]
    let discrepancy := liftAB thirdField vector true (superCommutator exchangeAB firstField secondField) - (exchangeAC * exchangeBC) • liftAB thirdField vector false (superCommutator exchangeAB firstField secondField)
    let firstPart := exchangeBC • liftAC secondField vector true (superCommutator exchangeAC firstField thirdField) - exchangeAB • liftAC secondField vector false (superCommutator exchangeAC firstField thirdField)
    let secondPart := liftBC firstField vector true (superCommutator exchangeBC secondField thirdField) - (exchangeAB * exchangeAC) • liftBC firstField vector false (superCommutator exchangeBC secondField thirdField)
    have jacobi : discrepancy = firstPart + secondPart := by
      funext left middle right; dsimp [discrepancy, firstPart, secondPart, liftAB, liftAC, liftBC, superCommutator]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sub, map_smul]; module
    have discrepancyKilled : (first ^ thirdOrder) discrepancy = 0 := by
      dsimp [discrepancy]
      rw [map_sub, map_smul, ← intertwiningPowersOT deltaEnd first (liftAB thirdField vector true) (lawAB true), ← intertwiningPowersOT deltaEnd first (liftAB thirdField vector false) (lawAB false), thirdKilled]
      simp
    have firstPartKilled : (combined ^ firstOrder) firstPart = 0 := by
      dsimp [firstPart]
      rw [map_sub, map_smul, map_smul, ← intertwiningPowersOT deltaEnd combined (liftAC secondField vector true) (lawAC true), ← intertwiningPowersOT deltaEnd combined (liftAC secondField vector false) (lawAC false), firstKilled]
      simp
    have secondPartKilled : (second ^ secondOrder) secondPart = 0 := by
      dsimp [secondPart]
      rw [map_sub, map_smul, ← intertwiningPowersOT deltaEnd second (liftBC firstField vector true) (lawBC true), ← intertwiningPowersOT deltaEnd second (liftBC firstField vector false) (lawBC false), secondKilled]
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
        have law := congrArg (fun operator : Module.End ℂ (Triple Carrier) => operator value) combinedFirst.eq
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
  let extract : Triple Carrier →ₗ[ℂ] (ℤ → ℤ → Carrier) := {
    toFun distribution := distribution 0
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have intertwiningPowersTV
      (source : Module.End ℂ (Triple Carrier))
      (target : Module.End ℂ (ℤ → ℤ → Carrier))
      (linear : Triple Carrier →ₗ[ℂ] (ℤ → ℤ → Carrier))
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : Triple Carrier) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  have intertwiningPowersEV
      (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ Carrier))
      (target : Module.End ℂ (ℤ → ℤ → Carrier))
      (linear : (ℤ → ℤ → Module.End ℂ Carrier) →ₗ[ℂ] (ℤ → ℤ → Carrier))
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Carrier) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  have extractLaw (distribution : Triple Carrier) : extract (plainYZ distribution) = plainDelta (extract distribution) := by rfl
  have evaluateLaw (distribution : ℤ → ℤ → Module.End ℂ Carrier) : evaluate vector (deltaEnd distribution) = plainDelta (evaluate vector distribution) := by rfl
  have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Carrier) : liftAB thirdField vector side (deltaEnd distribution) = plainXY (liftAB thirdField vector side distribution) := by
    funext first middle third; dsimp [liftAB, deltaEnd, FieldNormalProductLocality.delta, plainXY, shiftXY]
    cases side <;> simp [map_sub]
  have intertwiningPowersOT
      (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ Carrier))
      (target : Module.End ℂ (Triple Carrier))
      (linear : (ℤ → ℤ → Module.End ℂ Carrier) →ₗ[ℂ] Triple Carrier)
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Carrier) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  let discrepancy := liftAB thirdField vector true (superCommutator exchangeAB firstField secondField) - (exchangeAC * exchangeBC) • liftAB thirdField vector false (superCommutator exchangeAB firstField secondField)
  have connection : extract ((plainXY ^ residueDegree) discrepancy) = evaluate vector (superCommutator (exchangeAC * exchangeBC) (residue exchangeAB (residueDegree : ℤ) firstField secondField) thirdField) := by
    dsimp only [discrepancy]
    rw [map_sub, map_smul, map_sub, map_smul, ← intertwiningPowersOT deltaEnd plainXY (liftAB thirdField vector true) (lawAB true), ← intertwiningPowersOT deltaEnd plainXY (liftAB thirdField vector false) (lawAB
      false)]
    funext first second; dsimp [extract, liftAB, evaluate, superCommutator]
    rw [← positiveModes first (((thirdField [[second]])) vector), ← positiveModes first vector]
  have killed := congrArg (fun distribution : Triple Carrier => extract distribution) (cancellation vector)
  change extract ((plainYZ ^ order) ((plainXY ^ residueDegree) discrepancy)) = extract 0 at killed
  rw [intertwiningPowersTV plainYZ plainDelta extract extractLaw, connection, ← intertwiningPowersEV deltaEnd plainDelta (evaluate vector) evaluateLaw, map_zero] at killed
  have coefficient := congrFun (congrFun killed left) right
  change ((deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Carrier))^[order] (superCommutator (exchangeAC * exchangeBC) (residue exchangeAB (residueDegree : ℤ) firstField secondField) thirdField)) left right vector = 0
  rw [← Module.End.pow_apply]; exact coefficient

theorem stateField_residue_superLocal (leftParity rightParity otherParity : ℕ)
    (left right other : Carrier) (parameter : ℤ)
    (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity)
    (otherHomogeneous : other ∈ homogeneous otherParity) :
    SuperLocal (leftParity + rightParity) otherParity
      (residue (koszul leftParity rightParity) parameter (Y left) (Y right)) (Y other) := by
  by_cases nonnegative : 0 ≤ parameter
  · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
    obtain ⟨firstOrder, firstKilled⟩ := stateField_superLocal leftParity otherParity
      left other leftHomogeneous otherHomogeneous
    obtain ⟨secondOrder, secondKilled⟩ := stateField_superLocal rightParity otherParity
      right other rightHomogeneous otherHomogeneous
    obtain ⟨thirdOrder, thirdKilled⟩ := stateField_superLocal leftParity rightParity
      left right leftHomogeneous rightHomogeneous
    have firstKilledEnd : (deltaEnd ^ firstOrder)
        (superCommutator (koszul leftParity otherParity) (Y left) (Y other)) = 0 := by
      rw [Module.End.pow_apply]
      exact firstKilled
    have secondKilledEnd : (deltaEnd ^ secondOrder)
        (superCommutator (koszul rightParity otherParity) (Y right) (Y other)) = 0 := by
      rw [Module.End.pow_apply]
      exact secondKilled
    have thirdKilledEnd : (deltaEnd ^ thirdOrder)
        (superCommutator (koszul leftParity rightParity) (Y left) (Y right)) = 0 := by
      rw [Module.End.pow_apply]
      exact thirdKilled
    obtain ⟨order, killed⟩ := nonnegative_residue_locality (koszul leftParity rightParity)
      (koszul leftParity otherParity) (koszul rightParity otherParity) (Y left) (Y right)
      (Y other) degree firstOrder secondOrder thirdOrder firstKilledEnd secondKilledEnd thirdKilledEnd
    refine ⟨order, ?_⟩
    rw [koszul_add_left]
    exact killed
  · let degree := (-parameter - 1).toNat
    have index : parameter = -(degree : ℤ) - 1 := by dsimp [degree]; omega
    rw [index, negative_residue_normal]
    exact normal_superLocal leftParity rightParity otherParity
      (dividedDerivative degree (Y left)) (Y right) (Y other)
      (dividedDerivative_superLocal leftParity otherParity degree _ _
        (stateField_superLocal leftParity otherParity left other leftHomogeneous otherHomogeneous))
      (stateField_superLocal rightParity otherParity right other rightHomogeneous otherHomogeneous)
      (dividedDerivative_superLocal leftParity rightParity degree _ _
        (stateField_superLocal leftParity rightParity left right leftHomogeneous rightHomogeneous))

theorem stateField_residue_closure (leftParity rightParity : ℕ) (left right : Carrier)
    (parameter : ℤ) (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    Y (((Y left)[[parameter]]) right) =
      residue (koszul leftParity rightParity) parameter (Y left) (Y right) := by
  have vacuumLaw := residue_vacuum (koszul leftParity rightParity) parameter (Y left) (Y right)
    (vacuum : Carrier) (stateField_creativity left) (stateField_creativity right)
  apply Eq.symm
  apply creative_local_field_eq (leftParity + rightParity) _ (((Y left)[[parameter]]) right)
    (stateField_mem leftParity left leftHomogeneous parameter rightParity right rightHomogeneous)
  · exact vacuumLaw.2
  · simpa only [stateField_creation] using vacuumLaw.1
  · exact residue_translation (koszul leftParity rightParity) parameter translation (Y left) (Y right)
      (stateField_covariance left) (stateField_covariance right)
  · intro grade other otherHomogeneous
    exact stateField_residue_superLocal leftParity rightParity grade left right other parameter
      leftHomogeneous rightHomogeneous otherHomogeneous

theorem stateField_iterate (leftParity rightParity : ℕ) (left right vector : Carrier)
    (parameter mode : ℤ) (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    ((Y (((Y left)[[parameter]]) right))[[mode]]) vector =
      (∑ᶠ offset : ℕ, weight parameter offset •
        ((Y left)[[parameter - offset]]) (((Y right)[[mode + offset]]) vector)) -
      (epsilon parameter * koszul leftParity rightParity) •
        (∑ᶠ offset : ℕ, weight parameter offset •
          ((Y right)[[parameter + mode - offset]]) (((Y left)[[offset]]) vector)) := by
  rw [stateField_residue_closure leftParity rightParity left right parameter
    leftHomogeneous rightHomogeneous, residue_modes]
  rfl

def mixedResidue (parameter : ℤ) (left right : Carrier) : VertexOperator ℂ Carrier :=
  ∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
    residue (koszul leftParity rightParity) parameter
      (Y (parityPart leftParity left)) (Y (parityPart rightParity right))

theorem stateField_residue_mixed (parameter : ℤ) (left right : Carrier) :
    Y (((Y left)[[parameter]]) right) = mixedResidue parameter left right := by
  have closure (leftParity rightParity : ℕ) :
      Y (((Y (parityPart leftParity left))[[parameter]]) (parityPart rightParity right)) =
        residue (koszul leftParity rightParity) parameter
          (Y (parityPart leftParity left)) (Y (parityPart rightParity right)) :=
    stateField_residue_closure leftParity rightParity _ _ parameter
      (parityPart_mem leftParity left) (parityPart_mem rightParity right)
  calc
    Y (((Y left)[[parameter]]) right) =
        Y ((((Y (parityPart 0 left) + Y (parityPart 1 left))[[parameter]]))
          (parityPart 0 right + parityPart 1 right)) := by
      rw [← map_add, parity_decomposition, parity_decomposition]
    _ = (Y (((Y (parityPart 0 left))[[parameter]]) (parityPart 0 right)) +
          Y (((Y (parityPart 0 left))[[parameter]]) (parityPart 1 right))) +
        (Y (((Y (parityPart 1 left))[[parameter]]) (parityPart 0 right)) +
          Y (((Y (parityPart 1 left))[[parameter]]) (parityPart 1 right))) := by
      simp only [map_add, Pi.add_apply, LinearMap.add_apply]
      abel
    _ = mixedResidue parameter left right := by
      rw [closure, closure, closure, closure]
      simp only [mixedResidue, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

end
end D5.S3.VertexAlgebra.BcGhostSuperResidues
