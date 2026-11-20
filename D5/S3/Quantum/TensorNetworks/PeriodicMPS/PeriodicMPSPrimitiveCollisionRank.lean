/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionRank
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionRank
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionRankData]
   utility: none
   digest: Rank eight at both primitive collision cores. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionRankData

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

open Matrix
open scoped Matrix Kronecker
open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal)
open PeriodicMPSUniformAntisymmetricTransfer
  (TransferMatrix mixedTransfer mixedRaw conjugateCore)
open PeriodicMPSUniformHardCoreTransferRecurrence (binaryTransfer binaryInsertion)

private abbrev Pair := Fin 2 × Fin 2
private abbrev G := GaussianInt
private abbrev GM := TransferMatrix G
private abbrev B2 := Fin 2 → Matrix (Fin 2) (Fin 2) G
private abbrev Direction := Fin 2 × Fin 2 × Fin 2 × Fin 2

private noncomputable def integerObservedReal (b : Bool) : Matrix (Fin 9) (Fin 16) ℝ :=
  (observedInteger b).map (Int.castRingHom ℝ)

private theorem observed_integer_rank (b : Bool) : (integerObservedReal b).rank = 8 := by
  let J := integerObservedReal b
  let J0 := J.submatrix minorRows minorCols
  have hinv : J0 * (Int.castRingHom ℝ).mapMatrix (minorInverse b) =
      (minorScale b : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    have h := congrArg (Int.castRingHom ℝ).mapMatrix (integer_minor_inverse b)
    rw [map_mul] at h
    ext i j
    have h' := congrFun (congrFun h i) j
    rw [show J0 = (Int.castRingHom ℝ).mapMatrix ((observedInteger b).submatrix minorRows minorCols) from rfl]
    refine h'.trans ?_
    change (((minorScale b • (1 : Matrix (Fin 8) (Fin 8) ℤ)) i j : ℤ) : ℝ) =
      ((minorScale b : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) i j
    rw [Matrix.smul_apply, Matrix.smul_apply]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hs : (minorScale b : ℝ) ≠ 0 := by cases b <;> norm_num [minorScale]
  have hsurj : Function.Surjective J0.mulVec := by
    apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    refine ⟨(minorScale b : ℝ)⁻¹ • (Int.castRingHom ℝ).mapMatrix (minorInverse b), ?_⟩
    rw [Matrix.mul_smul, hinv, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hlo : 8 ≤ J.rank := by
    have h := Matrix.rank_submatrix_le J minorRows minorCols
    change J0.rank ≤ J.rank at h
    rwa [Matrix.mulVec_surjective_iff_rank_eq_card.mp hsurj, Fintype.card_fin] at h
  let J1 := J.submatrix minorRows (id : Fin 16 → Fin 16)
  let L : Matrix (Fin 9) (Fin 8) ℝ := fun i j =>
    if i = 7 then if j = 0 then 3 / 4 else if j = 3 then -(25 / 24) else 0
    else if i = minorRows j then 1 else 0
  have he : J = L * J1 := by
    ext i j
    have h : 24 * J 7 j = 18 * J 0 j - 25 * J 3 j := by
      change 24 * (observedInteger b 7 j : ℝ) =
        18 * (observedInteger b 0 j : ℝ) - 25 * (observedInteger b 3 j : ℝ)
      exact_mod_cast integer_row_relation b j
    rw [Matrix.mul_apply]
    fin_cases i <;>
      norm_num [L, J1, Fin.sum_univ_succ, minorRows]; linarith only [h]
  apply le_antisymm ?_ hlo
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width L)

noncomputable section

private abbrev f := GaussianInt.toComplex
private abbrev TwoCore := Fin 2 → Bond
private def mapCores (A : B2) : TwoCore := fun k => f.mapMatrix (A k)
private def directionC (d : Fin 16) : TwoCore := mapCores (basisDirection (directionOf d))

private theorem mapStarCore (A : B2) :
    mapCores (fun k => (A k).map star) = conjugateCore (mapCores A) := by
  funext k i j
  exact GaussianInt.toComplex_star _

private theorem mapKron (M N : Matrix (Fin 2) (Fin 2) G) :
    f.mapMatrix (M ⊗ₖ N) = f.mapMatrix M ⊗ₖ f.mapMatrix N := by
  ext i j
  exact map_mul f _ _

private theorem mapScale (x : G) (M : GM) :
    f.mapMatrix (x • M) = f x • f.mapMatrix M := by
  ext i j
  exact map_mul f _ _

private theorem mapTransfer (A B : B2) :
    f.mapMatrix (mixedTransfer A B) = mixedTransfer (mapCores A) (mapCores B) := by
  simp only [mixedTransfer, binaryTransfer, mapCores, map_add, mapKron]

private theorem mapMark (A B : B2) (p q : Pair) :
    f.mapMatrix (binaryInsertion B A q p) = binaryInsertion (mapCores B) (mapCores A) q p := by
  simp only [binaryInsertion, mapCores, mapKron, map_mul]

private theorem mapDTransfer (A B U V : B2) :
    f.mapMatrix (transferVariation A B U V) =
      transferVariation (mapCores A) (mapCores B) (mapCores U) (mapCores V) := by
  simp only [transferVariation, map_add, mapTransfer]

private theorem mapDMarked (A B U V : B2) (p q : Pair) :
    f.mapMatrix (markedVariation A B U V p q) =
      markedVariation (mapCores A) (mapCores B) (mapCores U) (mapCores V) p q := by
  simp only [markedVariation, mapCores, map_add, mapKron, map_mul]

private theorem scale_ne (b : Bool) : (collisionScale b : ℂ) ≠ 0 := by
  cases b <;> norm_num [collisionScale]

private theorem first_eq (b : Bool) (d : Fin 16) :
    firstVariationNumerator b (directionC d) =
      ((collisionScale b : ℂ) ^ 4)⁻¹ • f.mapMatrix (scaledFirstG b d) := by
  let s : ℂ := collisionScale b
  let A := cores b
  let B := conjugateCore A
  let U := directionC d
  let V := conjugateCore U
  let T := mixedTransfer A B
  let X := transferVariation A B U V
  let W := T ^ 2
  have hb : mapCores (braG b) = B := mapStarCore (coresG b)
  have hT : stabilizedTransfer b = s⁻¹ • T := rfl
  have hP : stabilizedTransfer b ^ 2 = (s ^ 2)⁻¹ • W := by rw [hT, smul_pow, inv_pow]
  have hD : (collisionScale b : ℝ)⁻¹ • X = s⁻¹ • X := by
    ext p q
    simp [s, Complex.real_smul, smul_eq_mul]
  have hL : 1 + stabilizedTransfer b = s⁻¹ • (s • (1 : TransferMatrix ℂ) + T) := by
    rw [hT, smul_add, smul_smul, inv_mul_cancel₀ (scale_ne b), one_smul]
  ext p q
  change Matrix.trace (_ : TransferMatrix ℂ) =
    ((s ^ 4)⁻¹ • f.mapMatrix (scaledFirstG b d)) p q
  rw [Matrix.smul_apply, smul_eq_mul]
  change _ = (s ^ 4)⁻¹ * f ((scaledFirstG b d) p q)
  rw [scaledFirstG, AddMonoidHom.map_trace f]
  change _ = (s ^ 4)⁻¹ * (f.mapMatrix (_ : GM)).trace
  simp only [tG, insG, map_mul, map_add, map_pow, map_one, mapScale, map_natCast,
    mapMark, mapTransfer, mapDTransfer, mapDMarked, hb, mapStarCore, show mapCores (coresG b) = A from rfl,
    show mapCores (basisDirection (directionOf d)) = U from rfl]
  change (markedVariation A B U V p q * stabilizedTransfer b ^ 2 +
      binaryInsertion B A q p * ((1 + stabilizedTransfer b) *
        ((collisionScale b : ℝ)⁻¹ • X) * stabilizedTransfer b ^ 2 +
        stabilizedTransfer b ^ 2 * ((collisionScale b : ℝ)⁻¹ • X) *
          (1 + stabilizedTransfer b))).trace = _
  rw [hD, hL, hP]
  simp only [s, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_add]
  field_simp [scale_ne b]
  ring

private theorem obs_value (j : Fin 9) :
    (f.mapMatrix (observableG j) * collisionMarginal).trace = f (measure25 j) / 25 := by
  have hraw := normalized_collision_marginal false 0
  -- Clear the common scale using the four-site trace contraction.
  have hg : (observableG j * mixedRaw (coresG false) (braG false) 2).trace =
      400 * measure25 j := by
    fin_cases j <;> decide +kernel
  have h := congrArg f hg
  rw [map_mul, map_ofNat, AddMonoidHom.map_trace f] at h
  change (f.mapMatrix (_ * _)).trace = _ at h
  rw [map_mul] at h
  have hr : f.mapMatrix (mixedRaw (coresG false) (braG false) 2) =
      PeriodicMPSTwoSiteAmbiguity.rawTwo (cores false) 0 := by
    rw [PeriodicMPSUniformAntisymmetricTransfer.rawTwo_eq_mixedRaw]
    ext p q
    change f (Matrix.trace (binaryInsertion (braG false) (coresG false) q p *
      tG false ^ 2)) = _
    rw [AddMonoidHom.map_trace f]
    change (f.mapMatrix (_ * _ ^ 2)).trace = _
    simp only [map_pow, map_mul, tG, mapMark, mapTransfer, show mapCores (coresG false) = cores false from rfl,
      show mapCores (braG false) = conjugateCore (cores false) from mapStarCore (coresG false)]
    rfl
  rw [hr] at h
  rw [PeriodicMPSUniformHardCoreLocalization.normalizedMarginal_eq_rawTwo,
    rawTwo_trace_initial, collisionScale] at hraw
  rw [← hraw, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, h]
  norm_num
  ring

private def readout (j : Fin 9) (R : TransferMatrix ℂ) : ℝ :=
  (f.mapMatrix (observableG j) * R).trace.re

private theorem first_readout (b : Bool) (j : Fin 9) (d : Fin 16) :
    readout j (normalizedFirstVariation b (directionC d)) =
      ((collisionScale b : ℝ) ^ 4)⁻¹ * (observedInteger b j d : ℝ) := by
  have hg := congrArg f (gaussian_observed_integer b j d)
  simp only [numeratorRankG, map_sub, map_mul, map_ofNat, map_pow, map_natCast, map_intCast] at hg
  unfold readout
  rw [normalizedFirstVariation_sub, first_eq]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sub, Matrix.trace_sub,
    smul_sub, smul_smul, obs_value]
  simp only [AddMonoidHom.map_trace f] at hg
  change 25 * (f.mapMatrix (_ * _)).trace - _ = _ at hg
  rw [map_mul] at hg
  change 25 * (f.mapMatrix (observableG j) * f.mapMatrix (scaledFirstG b d)).trace -
    (f.mapMatrix (scaledFirstG b d)).trace * f (measure25 j) =
      25 * (collisionScale b : ℂ) ^ 2 * (observedInteger b j d : ℂ) at hg
  have hs := scale_ne b
  have he : ((collisionScale b : ℂ) ^ 2)⁻¹ *
      (((collisionScale b : ℂ) ^ 4)⁻¹ * (f.mapMatrix (observableG j) *
        f.mapMatrix (scaledFirstG b d)).trace -
      (((collisionScale b : ℂ) ^ 4)⁻¹ *
        (f.mapMatrix (scaledFirstG b d)).trace) * (f (measure25 j) / 25)) =
        ((collisionScale b : ℂ) ^ 4)⁻¹ * (observedInteger b j d : ℂ) := by
    field_simp [hs]
    linear_combination hg
  rw [mul_sub, ← mul_assoc, ← mul_assoc] at he
  have hk := congrArg Complex.re he
  have hcast : ((((collisionScale b : ℝ) ^ 4)⁻¹ *
      (observedInteger b j d : ℝ) : ℝ) : ℂ) =
        ((collisionScale b : ℂ) ^ 4)⁻¹ * (observedInteger b j d : ℂ) := by push_cast; rfl
  rw [← hcast, Complex.ofReal_re] at hk
  exact hk

/-- The real Jacobian in the sixteen real core coordinates and nine Pauli readouts. -/
def isingObservationJacobian (b : Bool) (r : ℕ) : Matrix (Fin 9) (Fin 16) ℝ :=
  fun j d => deriv (fun t => readout j (normalizedMarginal (r + 2)
    (coreLine b (directionC d) t))) 0

private theorem observation_deriv (b : Bool) (r : ℕ) (hr : 3 ≤ r)
    (j : Fin 9) (d : Fin 16) :
    isingObservationJacobian b r j d = readout j (normalizedFirstVariation b (directionC d)) := by
  change deriv (fun t => (f.mapMatrix (observableG j) *
    normalizedMarginal (r + 2) (coreLine b (directionC d) t)).trace.re) 0 = _
  let O := f.mapMatrix (observableG j)
  have h (p q : Pair) : HasDerivAt (fun t => normalizedMarginal (r + 2)
      (coreLine b (directionC d) t) p q) (normalizedFirstVariation b (directionC d) p q) 0 :=
    normalizedMarginal_hasDerivAt b (directionC d) r hr p q
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun p _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun q _ => (h q p).const_mul (O p q)
  have ht := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hs
  simpa only [O, readout, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Complex.reCLM_apply, Function.comp_def] using ht.deriv

/-- At both branches of the collision the physical observation has rank eight. -/
theorem isingObservationJacobian_rank (b : Bool) (r : ℕ) (hr : 3 ≤ r) :
    (isingObservationJacobian b r).rank = 8 := by
  have he : isingObservationJacobian b r =
      ((collisionScale b : ℝ) ^ 4)⁻¹ • integerObservedReal b := by
    ext j d
    rw [observation_deriv b r hr, first_readout]
    rfl
  rw [he, Matrix.rank_smul_of_mem_nonZeroDivisors, observed_integer_rank]
  apply mem_nonZeroDivisors_of_ne_zero
  cases b <;> norm_num [collisionScale]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.isingObservationJacobian_rank
