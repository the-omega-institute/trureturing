/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveRecordLeadingCoefficient]
   utility: none
   digest: The exact finite-ring cross commutator and its vanishing criterion. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveRecordLeadingCoefficient

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PrimitiveFiniteCrossCommutator

open Matrix Complex Polynomial
open scoped Matrix
open PeriodicMPSPrimitiveCollision
open ComplementaryRecordRate (collisionFlattening collisionFlattening_cross)
open PeriodicMPSUniformAntisymmetricTransfer
  (TransferMatrix characteristicRecurrence transferReadout_isSolution)

-- Reuse the literal contraction and normalization proofs in the owning modules.
open private numeratorG numerator from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionTransfer
open private collisionMixedTransferG map_collisionMixedTransfer collisionInsertion
  mixedRaw_eq_word_cross collision_raw_ketFirst collision_normalizing_factor from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionOverlap
open private insertionG map_insertion from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveRecordLeadingCoefficient

noncomputable section

private abbrev Pair := Fin 2 × Fin 2

private def pattern {R : Type*} [Zero R] [One R] [Neg R] : TransferMatrix R :=
  Matrix.reindex (finProdFinEquiv : Pair ≃ Fin 4).symm finProdFinEquiv.symm
    !![1, 0, 0, 1; 0, -1, -1, 0; 0, -1, -1, 0; 1, 0, 0, 1]

/-- The fixed matrix of the finite commutator in the paired visible index order
`(0,0), (0,1), (1,0), (1,1)`. -/
def collisionCommutatorMatrix : TransferMatrix ℂ := pattern

private theorem map_pattern :
    GaussianInt.toComplex.mapMatrix (pattern : TransferMatrix GaussianInt) =
      collisionCommutatorMatrix := by
  funext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [collisionCommutatorMatrix, pattern, Matrix.reindex_apply, Matrix.submatrix_apply,
      finProdFinEquiv, RingHom.mapMatrix_apply, Matrix.map_apply]

private def rawCross (m : ℕ) : TransferMatrix ℂ :=
  fun p q => (collisionInsertion p q * collisionMixedTransfer ^ m).trace

private def rawCrossG (m : ℕ) : TransferMatrix GaussianInt :=
  fun p q => (insertionG p q * collisionMixedTransferG ^ m).trace

private theorem map_rawCrossG (m : ℕ) :
    GaussianInt.toComplex.mapMatrix (rawCrossG m) = rawCross m := by
  funext p q
  have hi : GaussianInt.toComplex.mapMatrix (insertionG p q) = collisionInsertion p q :=
    map_insertion p q
  change GaussianInt.toComplex (insertionG p q * collisionMixedTransferG ^ m).trace =
    (collisionInsertion p q * collisionMixedTransfer ^ m).trace
  rw [AddMonoidHom.map_trace GaussianInt.toComplex]
  change (GaussianInt.toComplex.mapMatrix (insertionG p q * collisionMixedTransferG ^ m)).trace = _
  rw [map_mul, map_pow, hi, map_collisionMixedTransfer]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem gaussian_initial (r : Fin 4) :
    numeratorG * rawCrossG r.val - rawCrossG r.val * numeratorG =
      ((120000 : GaussianInt) * ((-(8 : GaussianInt)) ^ r.val +
        (⟨0, 8⟩ : GaussianInt) ^ r.val)) • pattern := by
  funext ⟨i, j⟩ ⟨k, l⟩
  fin_cases r <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

private theorem initial (r : Fin 4) :
    numerator * rawCross r.val - rawCross r.val * numerator =
      ((120000 : ℂ) * ((-(8 : ℂ)) ^ r.val + (8 * I) ^ r.val)) • collisionCommutatorMatrix := by
  have hI : GaussianInt.toComplex (⟨0, 8⟩ : GaussianInt) = 8 * I := by
    change ((⟨0, 8⟩ : GaussianInt) : ℂ) = _
    norm_num [GaussianInt.toComplex_def']
  have h := congrArg GaussianInt.toComplex.mapMatrix (gaussian_initial r)
  have hsmul (a : GaussianInt) :
      GaussianInt.toComplex.mapMatrix (a • (pattern : TransferMatrix GaussianInt)) =
        GaussianInt.toComplex a • collisionCommutatorMatrix := by
    funext p q
    change GaussianInt.toComplex (a * (pattern : TransferMatrix GaussianInt) p q) =
      GaussianInt.toComplex a * collisionCommutatorMatrix p q
    rw [map_mul]
    exact congrArg (fun M : TransferMatrix ℂ => GaussianInt.toComplex a * M p q) map_pattern
  simpa only [map_sub, map_mul, map_pow, map_add, map_neg, map_ofNat, map_rawCrossG,
    numerator, hsmul, hI] using h

private def insertionReadout (p q : Pair) : TransferMatrix ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap _ ℂ ℂ).comp (LinearMap.mulLeft ℂ (collisionInsertion p q))

private def commutatorReadout (p q : Pair) : TransferMatrix ℂ →ₗ[ℂ] ℂ :=
  (∑ k : Pair, numerator p k • insertionReadout k q) -
    ∑ k : Pair, numerator k q • insertionReadout p k

private theorem commutator_readout (p q : Pair) (m : ℕ) :
    commutatorReadout p q (collisionMixedTransfer ^ m) =
      (numerator * rawCross m - rawCross m * numerator) p q := by
  change _ = (∑ k : Pair, numerator p k * rawCross m k q) -
    ∑ k : Pair, rawCross m p k * numerator k q
  simp only [commutatorReadout, insertionReadout, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Matrix.traceLinearMap_apply, smul_eq_mul, rawCross, mul_comm]

private theorem recurrence_charPoly :
    (characteristicRecurrence collisionMixedTransfer).charPoly = collisionMixedTransfer.charpoly := by
  let P := collisionMixedTransfer.charpoly
  have hdegree : P.natDegree = 4 := by
    change collisionMixedTransfer.charpoly.natDegree = 4
    rw [Matrix.charpoly_natDegree_eq_dim]
    decide
  have hlead : P.coeff 4 = 1 :=
    hdegree ▸ (Matrix.charpoly_monic collisionMixedTransfer).coeff_natDegree
  calc
    _ = ∑ i ∈ Finset.range (4 + 1), monomial i (P.coeff i) := by
      rw [LinearRecurrence.charPoly]
      change monomial 4 1 - (∑ i : Fin 4, monomial (i : ℕ) (-P.coeff i)) = _
      rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (-P.coeff i)) 4,
        Finset.sum_range_succ (fun i => monomial i (P.coeff i)) 4, hlead]
      simp only [monomial_neg, Finset.sum_neg_distrib, sub_neg_eq_add, add_comm]
    _ = P := by simpa only [hdegree] using P.as_sum_range.symm

private theorem odd_mode_isSolution (z : ℂ) (hz : z = -8 ∨ z = 8 * I) :
    (characteristicRecurrence collisionMixedTransfer).IsSolution (fun m => z ^ m) := by
  apply ((characteristicRecurrence collisionMixedTransfer).geom_sol_iff_root_charPoly z).2
  rw [recurrence_charPoly, Polynomial.IsRoot.def, collision_mixed_charpoly]
  rcases hz with h | h <;> rw [h] <;>
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub]

private theorem raw_commutator (m : ℕ) :
    numerator * rawCross m - rawCross m * numerator =
      ((120000 : ℂ) * ((-(8 : ℂ)) ^ m + (8 * I) ^ m)) • collisionCommutatorMatrix := by
  funext p q
  let E := characteristicRecurrence collisionMixedTransfer
  let u := fun j => (numerator * rawCross j - rawCross j * numerator) p q
  let c := (120000 : ℂ) * collisionCommutatorMatrix p q
  let v := fun j : ℕ => c * ((-(8 : ℂ)) ^ j + (8 * I) ^ j)
  have hu : E.IsSolution u := by
    simpa only [E, u, commutator_readout] using
      transferReadout_isSolution collisionMixedTransfer (commutatorReadout p q)
  have hneg : (fun j : ℕ => (-(8 : ℂ)) ^ j) ∈ E.solSpace := odd_mode_isSolution (-8) (Or.inl rfl)
  have hi : (fun j : ℕ => (8 * I) ^ j) ∈ E.solSpace := odd_mode_isSolution (8 * I) (Or.inr rfl)
  have hv : E.IsSolution v := by
    apply (E.is_sol_iff_mem_solSpace v).mpr
    exact E.solSpace.smul_mem c (E.solSpace.add_mem hneg hi)
  have hentry (j : ℕ) : v j =
      (((120000 : ℂ) * ((-(8 : ℂ)) ^ j + (8 * I) ^ j)) • collisionCommutatorMatrix) p q := by
    simp only [v, c, Matrix.smul_apply, smul_eq_mul]
    ring
  have huv : u = v := (E.eq_iff_eqOn_range_order u v hu hv).mpr (by
    intro j hj
    have hj' : j < 4 := Finset.mem_range.mp hj
    let r : Fin 4 := ⟨j, hj'⟩
    rw [hentry]
    exact congrArg (fun M : TransferMatrix ℂ => M p q) (initial r))
  exact (congrFun huv m).trans (hentry m)

private theorem normalized_cross_eq (m : ℕ) :
    collisionNormalizedCross m = ((Real.sqrt 200 : ℂ) ^ (m + 2))⁻¹ • rawCross m := by
  funext p q
  change collisionNormalizedCross m p q =
    ((Real.sqrt 200 : ℂ) ^ (m + 2))⁻¹ * (collisionInsertion p q * collisionMixedTransfer ^ m).trace
  rw [collisionNormalizedCross, ← mixedRaw_eq_word_cross, collision_raw_ketFirst,
    collision_normalizing_factor _ (by omega), Complex.ofReal_pow, show 2 + m = m + 2 by omega,
    div_eq_mul_inv, mul_comm]

/-- Exact finite commutator of the normalized ket-first cross reduction and the
common observer marginal. The ring has `m + 2` sites. -/
theorem collision_flattening_cross_commutator (m : ℕ) :
    collisionMarginal * (collisionFlattening false m * (collisionFlattening true m)ᴴ) -
      (collisionFlattening false m * (collisionFlattening true m)ᴴ) * collisionMarginal =
        (12 * ((-(8 : ℂ)) ^ m + (8 * I) ^ m) / (Real.sqrt 200 : ℂ) ^ (m + 2)) •
          collisionCommutatorMatrix := by
  have hR : collisionMarginal = (10000 : ℂ)⁻¹ • numerator := by
    funext p q
    change ((10000 : ℝ)⁻¹) • numerator p q = (10000 : ℂ)⁻¹ * numerator p q
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [collisionFlattening_cross, normalized_cross_eq, hR]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (((Real.sqrt 200 : ℂ) ^ (m + 2))⁻¹) ((10000 : ℂ)⁻¹),
    ← smul_sub, raw_commutator, smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

private theorem odd_sum_eq_zero_iff (m : ℕ) :
    (-(8 : ℂ)) ^ m + (8 * I) ^ m = 0 ↔ m % 4 = 2 := by
  have hi : I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.I_sq]
    norm_num
  have hc : I ^ 3 = -I := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, Complex.I_sq, neg_one_mul]
  have reduce (z : ℂ) (hz : z ^ 4 = 1) : z ^ m = z ^ (m % 4) := by
    calc
      _ = z ^ (m % 4 + 4 * (m / 4)) :=
        congrArg (fun k : ℕ => z ^ k) (Nat.mod_add_div m 4).symm
      _ = _ := by rw [pow_add, pow_mul, hz, one_pow, mul_one]
  have hneg : (-1 : ℂ) ^ 4 = 1 := by norm_num
  rw [show -(8 : ℂ) = 8 * (-1) by ring, mul_pow (8 : ℂ) (-1) m, mul_pow (8 : ℂ) I m,
    ← mul_add, reduce (-1) hneg, reduce I hi,
    mul_eq_zero, or_iff_right (pow_ne_zero _ (by norm_num : (8 : ℂ) ≠ 0))]
  rcases (show m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 by omega) with h | h | h | h <;>
    norm_num [h, Complex.ext_iff, Complex.I_sq, hc, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im]

/-- The finite cross reduction commutes with the common observer marginal
exactly when the full ring length is divisible by four. -/
theorem collision_flattening_cross_commute_iff (m : ℕ) :
    Commute collisionMarginal (collisionFlattening false m * (collisionFlattening true m)ᴴ) ↔
      (m + 2) % 4 = 0 := by
  have hK : collisionCommutatorMatrix (0, 0) (0, 0) = 1 := rfl
  have hscale (c : ℂ) : c • collisionCommutatorMatrix = 0 ↔ c = 0 := by
    constructor
    · intro h
      simpa only [Matrix.smul_apply, smul_eq_mul, hK, mul_one, Matrix.zero_apply] using
        congrArg (fun M : TransferMatrix ℂ => M (0, 0) (0, 0)) h
    · rintro rfl
      exact zero_smul _ _
  have hsqrt : (Real.sqrt 200 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num)).ne'
  change (_ * _ = _ * _) ↔ _
  rw [← sub_eq_zero, collision_flattening_cross_commutator, hscale, div_eq_zero_iff,
    or_iff_left (pow_ne_zero _ hsqrt), mul_eq_zero, or_iff_right (by norm_num : (12 : ℂ) ≠ 0),
    odd_sum_eq_zero_iff]
  omega

end

end D5.S3.Quantum.TensorNetworks.PrimitiveFiniteCrossCommutator

#print axioms D5.S3.Quantum.TensorNetworks.PrimitiveFiniteCrossCommutator.collision_flattening_cross_commutator
#print axioms D5.S3.Quantum.TensorNetworks.PrimitiveFiniteCrossCommutator.collision_flattening_cross_commute_iff
