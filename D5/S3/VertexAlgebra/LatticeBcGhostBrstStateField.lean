/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstStateField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original BRST candidate state, actual tensor field, and original charge. -/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstCurrent
import D5.S3.VertexAlgebra.LatticeBcGhostTensorJacobi
import D5.S3.VertexAlgebra.BcGhostSuperResidues

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstStateField

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge
open LatticeBcGhostBrstCurrent SuperFieldProducts SuperFieldLocality
open FieldNormalProductLocality (deltaEnd Triple plainXY plainYZ shiftXY shiftYZ
  liftAB liftAC liftBC evaluate plainDelta)
open scoped TensorProduct VertexOperator

private theorem cState_mem : cState ∈ BcGhostSuperGenerators.homogeneous 1 := by
  have creation := BcGhostSuperGenerators.current_creation_c
  rw [BcGhostSuperGenerators.currentField_modes] at creation
  change cState = Finsupp.single {1} 1 at creation
  rw [creation]
  exact BcGhostSuperGenerators.single_mem 1 {1} 1 (by
    simp [BcGhostSuperGenerators.subsetParity])

private theorem omegaGhost_mem :
    BcGhostActualConformalState.omegaState ∈ BcGhostSuperGenerators.homogeneous 0 := by
  apply (BcGhostSuperGenerators.homogeneous 0).sub_mem
  · exact BcGhostSuperGenerators.single_mem 0 {1, 2} 1 (by
      simp [BcGhostSuperGenerators.subsetParity])
  · apply (BcGhostSuperGenerators.homogeneous 0).smul_mem
    exact BcGhostSuperGenerators.single_mem 0 {0, 3} 1 (by
      simp [BcGhostSuperGenerators.subsetParity])

private theorem ghostCurrent_stateField :
    BcGhostSuperStateField.Y ((cField[[-1]]) BcGhostActualConformalState.omegaState) =
      ghostCurrent := by
  have closure := BcGhostSuperResidues.stateField_residue_closure 1 0 cState
    BcGhostActualConformalState.omegaState (-1) cState_mem omegaGhost_mem
  simpa only [koszul, Nat.mul_zero, pow_zero, cField, ghostStressField,
    ghostCurrent, normal] using closure

theorem candidate_field (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    LatticeBcGhostTensorStateField.stateField D (candidateState D H) = current D H := by
  rw [candidateState, map_add, map_smul,
    LatticeBcGhostTensorStateField.stateField_tmul,
    LatticeBcGhostTensorStateField.stateField_tmul,
    ghostCurrent_stateField, LatticeAllStateField.stateField_vacuum]
  rfl

theorem candidate_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    (LatticeBcGhostTensorStateField.stateField D (candidateState D H))[[0]] = Q D H := by
  rw [candidate_field, current_zero]

theorem candidate_mem (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    candidateState D H ∈ LatticeBcGhostTensorStateField.homogeneous 1 := by
  apply (LatticeBcGhostTensorStateField.homogeneous 1).add_mem
  · exact LatticeBcGhostTensorStateField.tmul_mem 1 _ _ cState_mem
  · apply (LatticeBcGhostTensorStateField.homogeneous 1).smul_mem
    apply LatticeBcGhostTensorStateField.tmul_mem
    exact BcGhostSuperStateField.stateField_mem 1 cState cState_mem (-1) 0
      BcGhostActualConformalState.omegaState omegaGhost_mem

theorem current_mem (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (parity : ℕ)
    (vector : State D) (member : vector ∈ LatticeBcGhostTensorStateField.homogeneous parity)
    (mode : ℤ) :
    ((current D H)[[mode]]) vector ∈ LatticeBcGhostTensorStateField.homogeneous (1 + parity) := by
  rw [← candidate_field]
  exact LatticeBcGhostTensorStateField.stateField_mem 1 parity _ vector
    (candidate_mem D H) member mode

theorem Q_mem (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (parity : ℕ)
    (vector : State D) (member : vector ∈ LatticeBcGhostTensorStateField.homogeneous parity) :
    Q D H vector ∈ LatticeBcGhostTensorStateField.homogeneous (1 + parity) := by
  rw [← current_zero]
  exact current_mem D H parity vector member 0

private theorem zero_residue_modes {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
    (exchange : ℂ) (first second : VertexOperator ℂ Space) (mode : ℤ) (vector : Space) :
    ((residue exchange 0 first second)[[mode]]) vector =
      (first[[0]]) ((second[[mode]]) vector) - exchange •
        (second[[mode]]) ((first[[0]]) vector) := by
  have weightZero (offset : ℕ) (different : offset ≠ 0) : weight 0 offset = 0 := by
    simp [weight, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
  rw [residue_modes]
  change residueLeft 0 mode first second vector -
    (epsilon 0 * exchange) • residueRight 0 mode first second vector = _
  have left : residueLeft 0 mode first second vector =
      (first[[0]]) ((second[[mode]]) vector) := by
    rw [residueLeft, finsum_eq_single _ 0]
    · simp [weight, integerBinomial]
    · intro offset different
      rw [weightZero offset different, zero_smul]
  have right : residueRight 0 mode first second vector =
      (second[[mode]]) ((first[[0]]) vector) := by
    rw [residueRight, finsum_eq_single _ 0]
    · simp [weight, integerBinomial]
    · intro offset different
      rw [weightZero offset different, zero_smul]
  rw [left, right]
  simp [SuperFieldProducts.epsilon]


set_option maxHeartbeats 1600000 in
private theorem zero_residue_locality {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
    (exchangeAB exchangeAC exchangeBC : ℂ)
    (firstField secondField thirdField : VertexOperator ℂ Space)
    (firstOrder secondOrder thirdOrder : ℕ)
    (firstKilled : (deltaEnd ^ firstOrder) (superCommutator exchangeAC firstField thirdField) = 0)
    (secondKilled : (deltaEnd ^ secondOrder) (superCommutator exchangeBC secondField thirdField) = 0)
    (thirdKilled : (deltaEnd ^ thirdOrder) (superCommutator exchangeAB firstField secondField) = 0) :
    ∃ order : ℕ, SuperFieldProducts.delta^[order]
      (superCommutator (exchangeAC * exchangeBC)
        (residue exchangeAB ((0 : ℕ) : ℤ) firstField secondField) thirdField) = 0 := by
  classical
  have positiveModes (mode : ℤ) (vector : Space) :
      ((residue exchangeAB 0 firstField secondField)[[mode]]) vector =
        ((deltaEnd ^ (0 : ℕ)) (superCommutator exchangeAB firstField secondField))
          0 mode vector := by
    rw [zero_residue_modes]
    rfl
  let order := if thirdOrder ≤ (0 : ℕ) then 0 else firstOrder + thirdOrder - (0 : ℕ) - 1 + secondOrder
  have cancellation (vector : Space) : ((plainYZ ^ order * plainXY ^ (0 : ℕ) : Module.End ℂ (Triple Space)) (fun left middle right =>
          superCommutator exchangeAB firstField secondField left middle (((thirdField [[right]])) vector) - (exchangeAC * exchangeBC) • ((thirdField [[right]])) (superCommutator exchangeAB firstField secondField left
            middle vector))) = 0 := by
    dsimp only [order]
    let first : Module.End ℂ (Triple Space) := plainXY
    let second : Module.End ℂ (Triple Space) := plainYZ
    let combined := first + second
    have commuting : Commute first second := by
      apply LinearMap.ext; intro distribution; funext left middle right; dsimp [first, second, plainXY, plainYZ, shiftXY, shiftYZ]
      abel
    have combinedFirst : Commute combined first := (Commute.refl first).add_left commuting.symm
    have combinedSecond : Commute combined second := commuting.add_left (Commute.refl second)
    have intertwiningPowersOT
        (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ Space))
        (target : Module.End ℂ (Triple Space))
        (linear : (ℤ → ℤ → Module.End ℂ Space) →ₗ[ℂ] Triple Space)
        (law : ∀ value, linear (source value) = target (linear value))
        (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Space) :
        linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        simp only [pow_succ', Module.End.mul_apply]
        rw [law, inductionHypothesis]
    have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Space) : liftAB thirdField vector side (deltaEnd distribution) = first (liftAB thirdField vector side distribution) := by
      funext left middle right; dsimp [liftAB, deltaEnd, FieldNormalProductLocality.delta, first, plainXY, shiftXY]
      cases side <;> simp [map_sub]
    have lawAC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Space) : liftAC secondField vector side (deltaEnd distribution) = combined (liftAC secondField vector side distribution) := by
      funext left middle right; dsimp [liftAC, deltaEnd, FieldNormalProductLocality.delta, combined, first, second, plainXY, plainYZ, shiftXY, shiftYZ]
      cases side <;> simp [map_sub]
    have lawBC (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Space) : liftBC firstField vector side (deltaEnd distribution) = second (liftBC firstField vector side distribution) := by
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
    by_cases large : thirdOrder ≤ (0 : ℕ)
    · simp only [if_pos large]
      change (second ^ 0 * first ^ (0 : ℕ)) discrepancy = 0
      simpa only [pow_zero, one_mul, Module.End.one_apply] using high 0 large
    · let exponent := firstOrder + thirdOrder - (0 : ℕ) - 1
      simp only [if_neg large]; change (second ^ (exponent + secondOrder) * first ^ (0 : ℕ)) discrepancy = 0
      have low (degree : ℕ) (largeDegree : firstOrder ≤ degree) : (combined ^ degree * second ^ secondOrder) discrepancy = 0 := by
        obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le largeDegree
        rw [pow_add, (Commute.refl combined).pow_pow _ _ |>.eq, mul_assoc, Module.End.mul_apply, annihilated, map_zero]
      have minusCommute : Commute combined (-first) := by
        apply LinearMap.ext; intro value
        have law := congrArg (fun operator : Module.End ℂ (Triple Space) => operator value) combinedFirst.eq
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
      · have vanish : (combined ^ degree) ((first ^ (exponent - degree)) ((second ^ secondOrder) ((first ^ (0 : ℕ)) discrepancy))) = 0 := by
          change (combined ^ degree * first ^ (exponent - degree) * second ^ secondOrder * first ^ (0 : ℕ)) discrepancy = 0
          rw [(combinedFirst.pow_pow degree (exponent - degree)).eq]
          have move := (combinedFirst.pow_pow degree (0 : ℕ)).mul_left (commuting.symm.pow_pow secondOrder (0 : ℕ))
          have reorder : first ^ (exponent - degree) * combined ^ degree * second ^ secondOrder * first ^ (0 : ℕ) = first ^ (exponent - degree) * first ^ (0 : ℕ) * (combined ^ degree * second
            ^ secondOrder) := by
            calc
              _ = first ^ (exponent - degree) * ((combined ^ degree * second ^ secondOrder) * first ^ (0 : ℕ)) := by simp only [mul_assoc]
              _ = _ := by rw [move.eq]; simp only [mul_assoc]
          rw [reorder, Module.End.mul_apply, low degree largeDegree, map_zero]
        simp only [pow_zero, Module.End.one_apply] at vanish
        simp [vanish]
      · have bound : thirdOrder ≤ exponent - degree + (0 : ℕ) := by
          have within : degree ≤ exponent := by simpa using Finset.mem_range.mp member
          dsimp [exponent]; omega
        have vanish : (first ^ (exponent - degree)) ((second ^ secondOrder) ((first ^ (0 : ℕ)) discrepancy)) = 0 := by
          change (first ^ (exponent - degree) * second ^ secondOrder * first ^ (0 : ℕ)) discrepancy = 0
          rw [(commuting.pow_pow _ _).eq, mul_assoc, ← pow_add, Module.End.mul_apply, high _ bound, map_zero]
        simp only [pow_zero, Module.End.one_apply] at vanish
        simp [vanish]
  refine ⟨order, ?_⟩; funext left right; apply LinearMap.ext; intro vector
  let extract : Triple Space →ₗ[ℂ] (ℤ → ℤ → Space) := {
    toFun distribution := distribution 0
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have intertwiningPowersTV
      (source : Module.End ℂ (Triple Space))
      (target : Module.End ℂ (ℤ → ℤ → Space))
      (linear : Triple Space →ₗ[ℂ] (ℤ → ℤ → Space))
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : Triple Space) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  have intertwiningPowersEV
      (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ Space))
      (target : Module.End ℂ (ℤ → ℤ → Space))
      (linear : (ℤ → ℤ → Module.End ℂ Space) →ₗ[ℂ] (ℤ → ℤ → Space))
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Space) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  have extractLaw (distribution : Triple Space) : extract (plainYZ distribution) = plainDelta (extract distribution) := by rfl
  have evaluateLaw (distribution : ℤ → ℤ → Module.End ℂ Space) : evaluate vector (deltaEnd distribution) = plainDelta (evaluate vector distribution) := by rfl
  have lawAB (side : Bool) (distribution : ℤ → ℤ → Module.End ℂ Space) : liftAB thirdField vector side (deltaEnd distribution) = plainXY (liftAB thirdField vector side distribution) := by
    funext first middle third; dsimp [liftAB, deltaEnd, FieldNormalProductLocality.delta, plainXY, shiftXY]
    cases side <;> simp [map_sub]
  have intertwiningPowersOT
      (source : Module.End ℂ (ℤ → ℤ → Module.End ℂ Space))
      (target : Module.End ℂ (Triple Space))
      (linear : (ℤ → ℤ → Module.End ℂ Space) →ₗ[ℂ] Triple Space)
      (law : ∀ value, linear (source value) = target (linear value))
      (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Space) :
      linear ((source ^ degree) value) = (target ^ degree) (linear value) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [law, inductionHypothesis]
  let discrepancy := liftAB thirdField vector true (superCommutator exchangeAB firstField secondField) - (exchangeAC * exchangeBC) • liftAB thirdField vector false (superCommutator exchangeAB firstField secondField)
  have connection : extract ((plainXY ^ (0 : ℕ)) discrepancy) = evaluate vector (superCommutator (exchangeAC * exchangeBC) (residue exchangeAB ((0 : ℕ) : ℤ) firstField secondField) thirdField) := by
    dsimp only [discrepancy]
    rw [map_sub, map_smul, map_sub, map_smul, ← intertwiningPowersOT deltaEnd plainXY (liftAB thirdField vector true) (lawAB true), ← intertwiningPowersOT deltaEnd plainXY (liftAB thirdField vector false) (lawAB
      false)]
    funext first second; dsimp [extract, liftAB, evaluate, superCommutator]
    rw [← positiveModes first (((thirdField [[second]])) vector), ← positiveModes first vector]
  have killed := congrArg (fun distribution : Triple Space => extract distribution) (cancellation vector)
  change extract ((plainYZ ^ order) ((plainXY ^ (0 : ℕ)) discrepancy)) = extract 0 at killed
  rw [intertwiningPowersTV plainYZ plainDelta extract extractLaw, connection, ← intertwiningPowersEV deltaEnd plainDelta (evaluate vector) evaluateLaw, map_zero] at killed
  have coefficient := congrFun (congrFun killed left) right
  change ((deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Space))^[order] (superCommutator (exchangeAC * exchangeBC) (residue exchangeAB ((0 : ℕ) : ℤ) firstField secondField) thirdField)) left right vector = 0
  rw [← Module.End.pow_apply]; exact coefficient

private theorem current_zero_residue_superLocal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (parity grade : ℕ)
    (state other : State D)
    (member : state ∈ LatticeBcGhostTensorStateField.homogeneous parity)
    (otherMember : other ∈ LatticeBcGhostTensorStateField.homogeneous grade) :
    SuperLocal (1 + parity) grade
      (residue (koszul 1 parity) 0 (current D H)
        (LatticeBcGhostTensorStateField.stateField D state))
      (LatticeBcGhostTensorStateField.stateField D other) := by
  have firstLocal := LatticeBcGhostTensorLocality.homogeneous_superFieldLocal D 1 grade
    (candidateState D H) other (candidate_mem D H) otherMember
  have secondLocal := LatticeBcGhostTensorLocality.homogeneous_superFieldLocal D parity grade
    state other member otherMember
  have thirdLocal := LatticeBcGhostTensorLocality.homogeneous_superFieldLocal D 1 parity
    (candidateState D H) state (candidate_mem D H) member
  rw [candidate_field] at firstLocal thirdLocal
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  obtain ⟨thirdOrder, thirdKilled⟩ := thirdLocal
  have firstKilledEnd : (deltaEnd ^ firstOrder)
      (superCommutator (koszul 1 grade) (current D H)
        (LatticeBcGhostTensorStateField.stateField D other)) = 0 := by
    rw [Module.End.pow_apply]
    exact firstKilled
  have secondKilledEnd : (deltaEnd ^ secondOrder)
      (superCommutator (koszul parity grade)
        (LatticeBcGhostTensorStateField.stateField D state)
        (LatticeBcGhostTensorStateField.stateField D other)) = 0 := by
    rw [Module.End.pow_apply]
    exact secondKilled
  have thirdKilledEnd : (deltaEnd ^ thirdOrder)
      (superCommutator (koszul 1 parity) (current D H)
        (LatticeBcGhostTensorStateField.stateField D state)) = 0 := by
    rw [Module.End.pow_apply]
    exact thirdKilled
  obtain ⟨order, killed⟩ := zero_residue_locality
    (koszul 1 parity) (koszul 1 grade) (koszul parity grade)
    (current D H) (LatticeBcGhostTensorStateField.stateField D state)
    (LatticeBcGhostTensorStateField.stateField D other)
    firstOrder secondOrder thirdOrder firstKilledEnd secondKilledEnd thirdKilledEnd
  refine ⟨order, ?_⟩
  rw [koszul_add_left]
  exact killed

private theorem current_zero_residue_stateField (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (parity : ℕ) (state : State D)
    (member : state ∈ LatticeBcGhostTensorStateField.homogeneous parity) :
    LatticeBcGhostTensorStateField.stateField D (Q D H state) =
      residue (koszul 1 parity) 0 (current D H)
        (LatticeBcGhostTensorStateField.stateField D state) := by
  let residual := residue (koszul 1 parity) 0 (current D H)
    (LatticeBcGhostTensorStateField.stateField D state)
  let target := LatticeBcGhostTensorStateField.stateField D (Q D H state)
  have currentCreative (mode : ℤ) (nonnegative : 0 ≤ mode) :
      ((current D H)[[mode]]) (LatticeBcGhostTensorStateField.vacuum D) = 0 := by
    rw [← candidate_field]
    exact LatticeBcGhostTensorStateField.stateField_creativity D _ mode nonnegative
  have currentCovariant (mode : ℤ) :
      LatticeBcGhostTensorStateField.translation D * ((current D H)[[mode]]) -
        ((current D H)[[mode]]) * LatticeBcGhostTensorStateField.translation D =
        -(mode : ℂ) • ((current D H)[[mode - 1]]) := by
    rw [← candidate_field]
    exact LatticeBcGhostTensorStateField.stateField_covariance D _ mode
  have vacuumLaw := residue_vacuum (koszul 1 parity) 0 (current D H)
    (LatticeBcGhostTensorStateField.stateField D state)
    (LatticeBcGhostTensorStateField.vacuum D) currentCreative
    (LatticeBcGhostTensorStateField.stateField_creativity D state)
  have residualInitial : (residual[[-1]]) (LatticeBcGhostTensorStateField.vacuum D) =
      Q D H state := by
    simpa only [residual, LatticeBcGhostTensorStateField.stateField_creation,
      current_zero] using vacuumLaw.1
  have residualCovariant := residue_translation (koszul 1 parity) 0
    (LatticeBcGhostTensorStateField.translation D) (current D H)
    (LatticeBcGhostTensorStateField.stateField D state) currentCovariant
    (LatticeBcGhostTensorStateField.stateField_covariance D state)
  have targetCovariant := LatticeBcGhostTensorStateField.stateField_covariance D (Q D H state)
  have vanish : residual - target = 0 := by
    apply SuperStateFieldReconstruction.relative_vacuum_uniqueness
      (LatticeBcGhostTensorStateField.stateField D)
      (LatticeBcGhostTensorStateField.vacuum D) (LatticeBcGhostTensorStateField.translation D)
      LatticeBcGhostTensorStateField.parityPart LatticeBcGhostTensorStateField.homogeneous
      LatticeBcGhostTensorStateField.parity_decomposition
      LatticeBcGhostTensorStateField.parityPart_mem
      (LatticeBcGhostTensorStateField.translation_vacuum D)
      (LatticeBcGhostTensorStateField.stateField_creation D)
      (LatticeBcGhostTensorStateField.stateField_creativity D) (1 + parity)
    · intro mode nonnegative
      simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply,
        residual, vacuumLaw.2 mode nonnegative,
        target, LatticeBcGhostTensorStateField.stateField_creativity D
          (Q D H state) mode nonnegative, sub_self]
    · simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply, residualInitial,
        target, LatticeBcGhostTensorStateField.stateField_creation, sub_self]
    · intro mode
      simp only [map_sub, Pi.sub_apply, mul_sub, sub_mul, smul_sub]
      calc
        _ = (LatticeBcGhostTensorStateField.translation D * (residual[[mode]]) -
            (residual[[mode]]) * LatticeBcGhostTensorStateField.translation D) -
          (LatticeBcGhostTensorStateField.translation D * (target[[mode]]) -
            (target[[mode]]) * LatticeBcGhostTensorStateField.translation D) := by abel
        _ = _ := by rw [residualCovariant, targetCovariant]
    · intro grade other otherMember
      rw [sub_eq_add_neg, ← neg_one_smul ℂ target]
      apply superLocal_add_left
      · exact current_zero_residue_superLocal D H parity grade state other member otherMember
      · exact superLocal_smul_left (1 + parity) grade (-1) target _
          (LatticeBcGhostTensorLocality.homogeneous_superFieldLocal D (1 + parity) grade
            (Q D H state) other (Q_mem D H parity state member) otherMember)
  exact (sub_eq_zero.mp vanish).symm

theorem Q_derivation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (parity : ℕ) (state vector : State D)
    (member : state ∈ LatticeBcGhostTensorStateField.homogeneous parity) (mode : ℤ) :
    Q D H (((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) vector) =
      ((LatticeBcGhostTensorStateField.stateField D (Q D H state))[[mode]]) vector +
        koszul 1 parity •
          ((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) (Q D H vector) := by
  have law := congrArg (fun field : VertexOperator ℂ (State D) => (field[[mode]]) vector)
    (current_zero_residue_stateField D H parity state member)
  rw [zero_residue_modes, ← candidate_field, candidate_zero] at law
  rw [law]
  abel

theorem Q_derivation_mixed (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (state vector : State D) (mode : ℤ) :
    Q D H (((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) vector) =
      ((LatticeBcGhostTensorStateField.stateField D (Q D H state))[[mode]]) vector +
        ((LatticeBcGhostTensorStateField.stateField D
          (LatticeBcGhostTensorStateField.parityPart 0 state))[[mode]]) (Q D H vector) -
        ((LatticeBcGhostTensorStateField.stateField D
          (LatticeBcGhostTensorStateField.parityPart 1 state))[[mode]]) (Q D H vector) := by
  have even := Q_derivation D H 0 (LatticeBcGhostTensorStateField.parityPart 0 state)
    vector (LatticeBcGhostTensorStateField.parityPart_mem 0 state) mode
  have odd := Q_derivation D H 1 (LatticeBcGhostTensorStateField.parityPart 1 state)
    vector (LatticeBcGhostTensorStateField.parityPart_mem 1 state) mode
  simp only [koszul, Nat.mul_zero, Nat.mul_one, pow_zero, pow_one,
    one_smul, neg_one_smul] at even odd
  have fields : LatticeBcGhostTensorStateField.stateField D state =
      LatticeBcGhostTensorStateField.stateField D
        (LatticeBcGhostTensorStateField.parityPart 0 state) +
      LatticeBcGhostTensorStateField.stateField D
        (LatticeBcGhostTensorStateField.parityPart 1 state) := by
    rw [← map_add, LatticeBcGhostTensorStateField.parity_decomposition]
  have chargedFields : LatticeBcGhostTensorStateField.stateField D (Q D H state) =
      LatticeBcGhostTensorStateField.stateField D
        (Q D H (LatticeBcGhostTensorStateField.parityPart 0 state)) +
      LatticeBcGhostTensorStateField.stateField D
        (Q D H (LatticeBcGhostTensorStateField.parityPart 1 state)) := by
    rw [← map_add, ← map_add, LatticeBcGhostTensorStateField.parity_decomposition]
  simp only [fields, chargedFields, map_add, Pi.add_apply, LinearMap.add_apply]
  rw [even, odd]
  abel

end D5.S3.VertexAlgebra.LatticeBcGhostBrstStateField
