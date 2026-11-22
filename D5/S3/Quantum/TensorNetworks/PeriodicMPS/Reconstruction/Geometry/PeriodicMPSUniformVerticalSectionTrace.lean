/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSectionTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSectionTrace
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Trace and transverse identities on the paired vertical section. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalPrimeExclusion
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformAntisymmetricTransfer
import Mathlib.LinearAlgebra.Matrix.DualNumber

/-! Literal transfer calculations on the paired vertical section. -/

open Matrix MvPolynomial
open scoped Matrix Kronecker

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSectionRank

noncomputable section

open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits binaryInsertion binaryTransfer)
open PeriodicMPSUniformAntisymmetricTransfer (mixedTransfer mixedRaw)
open PeriodicMPSUniformVerticalMiddle
  (BondMatrix sectionB0 sectionB1 sectionTransfer sectionTransfer_pow literalCross literalCross_eq
    completeSeries
    tripletFeature traceFeatures middleTraceBlock middleFactor)

variable {R : Type*} [CommRing R]

private def ketBlock : (Fin 2 ⊕ Fin 2) ≃ TwoBits where
  toFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  invFun := fun (i, j) => if j = 0 then Sum.inl i else Sum.inr i
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro ⟨i, j⟩; fin_cases j <;> rfl

private def inKetOrder :
    Matrix TwoBits TwoBits R ≃+* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.reindexRingEquiv R ketBlock.symm

private theorem trace_inKetOrder (M : Matrix TwoBits TwoBits R) :
    (inKetOrder M).trace = M.trace := by
  exact ketBlock.sum_comp (fun i => M i i)

private theorem trace_blocks (A B C D : BondMatrix R) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

private theorem kronecker_inKetOrder (B A : BondMatrix R) :
    inKetOrder (B ⊗ₖ A) =
      Matrix.fromBlocks (A 0 0 • B) (A 0 1 • B) (A 1 0 • B) (A 1 1 • B) := by
  ext (i | i) (j | j)
  · exact mul_comm (B i j) (A 0 0)
  · exact mul_comm (B i j) (A 0 1)
  · exact mul_comm (B i j) (A 1 0)
  · exact mul_comm (B i j) (A 1 1)

/-- The transverse ket has commutator determinant equal to its lower-left coordinate. -/
def transverseKet (x : R) : Fin 2 → BondMatrix R :=
  ![!![1, 0; 0, 0], !![0, 1; x, 1]]

private def pairedBra (B0 B1 : BondMatrix R) : Fin 2 → BondMatrix R := ![B0, B1]

private theorem transfer_inKetOrder (x : R) (B0 B1 : BondMatrix R) :
    inKetOrder (mixedTransfer (transverseKet x) (pairedBra B0 B1)) =
      Matrix.fromBlocks B0 B1 (x • B1) B1 := by
  rw [mixedTransfer, binaryTransfer, map_add, kronecker_inKetOrder, kronecker_inKetOrder]
  ext (i | i) (j | j) <;> simp [transverseKet, pairedBra]

private theorem trace_kronecker_transfer (B A : BondMatrix R) (B0 B1 : BondMatrix R) (m : ℕ) :
    ((B ⊗ₖ A) * mixedTransfer (transverseKet 0) (pairedBra B0 B1) ^ m).trace =
      A 0 0 * (B * B0 ^ m).trace + A 1 0 * (B * literalCross B0 B1 m).trace +
        A 1 1 * (B * B1 ^ m).trace := by
  rw [← trace_inKetOrder, map_mul, map_pow, kronecker_inKetOrder, transfer_inKetOrder, zero_smul,
    ← sectionTransfer, sectionTransfer_pow, Matrix.fromBlocks_multiply, trace_blocks]
  simp only [mul_zero, add_zero, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_add, add_assoc]

/-- Triplet rows, with the symmetrized mixed word in the middle on both sides. -/
def tripletReadout (half : R) (ket bra : Fin 2 → BondMatrix R) (m : ℕ) :
    Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j =>
    ((tripletFeature half (bra 0) (bra 1) j ⊗ₖ tripletFeature half (ket 0) (ket 1) i) *
      mixedTransfer ket bra ^ m).trace

/-- The values at the triangular representative coincide with the diagonal
representative on the triplet rows. The middle row vanishes identically. -/
theorem tripletReadout_section (half : R) (B0 B1 : BondMatrix R) (m : ℕ) (i j : Fin 3) :
    tripletReadout half (transverseKet 0) (pairedBra B0 B1) m i j =
      ![(tripletFeature half B0 B1 j * B0 ^ m).trace, 0,
        (tripletFeature half B0 B1 j * B1 ^ m).trace] i := by
  rw [tripletReadout, Matrix.of_apply]
  change ((_ ⊗ₖ _) * mixedTransfer (transverseKet 0) (pairedBra B0 B1) ^ m).trace = _
  rw [trace_kronecker_transfer]
  fin_cases i <;> simp [pairedBra, transverseKet, tripletFeature, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two]


/-- The triplet rows are literal linear combinations of the native
adjacent-pair entries, with the same coefficients for the value and jet. -/
def tripletRow (half : R) (i : Fin 3) (p : TwoBits) : R :=
  ![if p = (0, 0) then 1 else 0,
    if p = (0, 1) ∨ p = (1, 0) then half else 0,
    if p = (1, 1) then 1 else 0] i

private theorem feature_eq_sum (half : R) (A : Fin 2 → BondMatrix R) (i : Fin 3) :
    tripletFeature half (A 0) (A 1) i =
      ∑ p : TwoBits, tripletRow half i p • (A p.1 * A p.2) := by
  fin_cases i <;> simp [tripletRow, tripletFeature, Fintype.sum_prod_type,
    Fin.sum_univ_two, pow_two, smul_add]

theorem tripletReadout_eq_native (half : R) (ket bra : Fin 2 → BondMatrix R)
    (m : ℕ) (i j : Fin 3) :
    tripletReadout half ket bra m i j =
      ∑ q : TwoBits, ∑ p : TwoBits, tripletRow half j q *
        (tripletRow half i p * mixedRaw ket bra m p q) := by
  rw [tripletReadout, Matrix.of_apply, feature_eq_sum, feature_eq_sum]
  have hk (A B : BondMatrix R) :
      A ⊗ₖ B = Matrix.kroneckerBilinear (R := R) A B := rfl
  simp only [hk, map_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.map_smul, Matrix.sum_mul, Matrix.trace_sum, smul_mul_assoc,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  rfl


private theorem sectionB1_trace_det (t u p : R) :
    (sectionB1 t u p).trace = t + u ∧ (sectionB1 t u p).det = t * u := by
  constructor
  · simp [sectionB1]
  · simp [sectionB1]; ring

private theorem split_power (M : BondMatrix R) (t u : R) (h : M ^ 2 =
    (t + u) • M - (t * u) • (1 : BondMatrix R)) (m : ℕ) :
    (t - u) • M ^ m = t ^ m • (M - u • 1) + u ^ m • (t • 1 - M) := by
  induction m with
  | zero => simp only [pow_zero, one_smul, sub_smul]; abel
  | succ m ih =>
    have ht : (M - u • 1) * M = t • (M - u • 1) := by
      rw [sub_mul, smul_mul_assoc, one_mul, ← pow_two, h, add_smul, smul_sub, smul_smul]
      abel
    have hu : (t • 1 - M) * M = u • (t • 1 - M) := by
      rw [sub_mul, smul_mul_assoc, one_mul, ← pow_two, h, add_smul, smul_sub, smul_smul,
        mul_comm u t]
      abel
    rw [pow_succ, ← smul_mul_assoc, ih, add_mul, smul_mul_assoc, smul_mul_assoc, ht, hu,
      smul_smul, smul_smul, pow_succ t, pow_succ u]

private theorem sectionB1_quadratic (t u p : R) :
    sectionB1 t u p ^ 2 = (t + u) • sectionB1 t u p - (t * u) • (1 : BondMatrix R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectionB1, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem sectionB0_pow (r s : R) (m : ℕ) :
    sectionB0 r s ^ m = !![r ^ m, 0; 0, s ^ m] := by
  induction m with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sectionB0, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]


open PeriodicMPSUniformVerticalSection (outerRows outerDividedMatrix outerDividedDet)

private def outerEntry (F : Matrix (Fin 3) (Fin 3) R) (i : Fin 6) : R :=
  F (if i.val < 3 then 0 else 2) (Fin.ofNat 3 i.val)

private def upperFeatures (m : ℕ) (r s t u p : R) : Fin 3 → R :=
  ![r ^ m * r ^ 2 + s ^ m * s ^ 2,
    r ^ m * (r * p) + s ^ m * (s * (t + u - p)),
    r ^ m * ((t + u) * p - t * u) + s ^ m * ((t + u) * (t + u - p) - t * u)]

private def lowerFeatures (m : ℕ) (r s t u q : R) : Fin 3 → R :=
  let thetaT := r * q + s * (1 - q)
  let thetaU := r * (1 - q) + s * q
  ![t ^ m * ((r + s) * thetaT - r * s) + u ^ m * ((r + s) * thetaU - r * s),
    t ^ m * (t * thetaT) + u ^ m * (u * thetaU),
    t ^ m * t ^ 2 + u ^ m * u ^ 2]

private theorem featurePowers {S : Type*} [CommRing S] [IsDomain S]
    (half r s t u q : S) (hh : half + half = 1) (he : t - u ≠ 0) (m : ℕ) :
    let p := u + (t - u) * q
    let B0 := sectionB0 r s
    let B1 := sectionB1 t u p
    (∀ j, (tripletFeature half B0 B1 j * B0 ^ m).trace = upperFeatures m r s t u p j) ∧
      (∀ j, (tripletFeature half B0 B1 j * B1 ^ m).trace = lowerFeatures m r s t u q j) := by
  let p := u + (t - u) * q
  let thetaT := r * q + s * (1 - q)
  let thetaU := r * (1 - q) + s * q
  let B0 := sectionB0 r s
  let B1 := sectionB1 t u p
  have hpow := split_power B1 t u (sectionB1_quadratic t u p) m
  have hread (N : BondMatrix S) :
      (t - u) * (N * B1 ^ m).trace =
        t ^ m * (N * (B1 - u • 1)).trace + u ^ m * (N * (t • 1 - B1)).trace := by
    have h := congrArg (fun M : BondMatrix S => (N * M).trace) hpow
    simpa only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_add, Matrix.trace_add]
      using h
  have hhalf : 2 * half = 1 := by simpa only [two_mul] using hh
  have hupper (j : Fin 3) :
      (tripletFeature half B0 B1 j * B0 ^ m).trace =
        ![r ^ m * r ^ 2 + s ^ m * s ^ 2,
          r ^ m * (r * p) + s ^ m * (s * (t + u - p)),
          r ^ m * ((t + u) * p - t * u) +
            s ^ m * ((t + u) * (t + u - p) - t * u)] j := by
    rw [show B0 ^ m = !![r ^ m, 0; 0, s ^ m] from sectionB0_pow r s m]
    fin_cases j <;>
      simp [B0, B1, sectionB0, sectionB1, tripletFeature, Matrix.trace_fin_two,
        pow_two, Matrix.vecMul, Matrix.mul_apply, dotProduct, Fin.sum_univ_two, p]
    · ring
    · linear_combination (r ^ m * (r * p) + s ^ m * (s * (t + u - p))) * hhalf
    · ring
  have hlower (j : Fin 3) :
      (tripletFeature half B0 B1 j * B1 ^ m).trace =
        ![t ^ m * ((r + s) * thetaT - r * s) + u ^ m * ((r + s) * thetaU - r * s),
          t ^ m * (t * thetaT) + u ^ m * (u * thetaU),
          t ^ m * t ^ 2 + u ^ m * u ^ 2] j := by
    apply mul_left_cancel₀ he
    rw [hread]
    fin_cases j <;>
      simp [B0, B1, sectionB0, sectionB1, tripletFeature, Matrix.trace_fin_two,
        Matrix.vecMul, Matrix.mul_apply, dotProduct, Matrix.one_apply, Fin.sum_univ_two,
        thetaT, thetaU, pow_two, p]
    · ring
    · linear_combination ((t - u) * (t ^ m * (t * thetaT) + u ^ m * (u * thetaU))) * hhalf
    · ring
  exact ⟨hupper, hlower⟩

section Outer

variable {K : Type*} [CommRing K] [IsDomain K]

local notation "P" => MvPolynomial (Fin 5) K
local notation "r" => (X (0 : Fin 5) : P)
local notation "s" => (X (1 : Fin 5) : P)
local notation "t" => (X (2 : Fin 5) : P)
local notation "u" => (X (3 : Fin 5) : P)
local notation "q" => (X (4 : Fin 5) : P)
local notation "p" => (u + (t - u) * q)

/-- The six literal outer observations on the polynomial section coincide with
the rows used in the divided outer determinant. The identity is before
differentiation, so the five ordinary partials coincide as polynomials. -/
theorem literalOuter_eq (half : P) (hh : half + half = 1) (m : ℕ) (i : Fin 6) :
    outerEntry (tripletReadout half (transverseKet 0)
      (pairedBra (sectionB0 r s) (sectionB1 t u p)) m) i = outerRows m i := by
  let B0 := sectionB0 r s
  let B1 := sectionB1 t u p
  have he : t - u ≠ 0 := sub_ne_zero.mpr (X_injective (R := K).ne (by decide))
  have hpow := split_power B1 t u (sectionB1_quadratic t u p) m
  have hread (N : BondMatrix P) :
      (t - u) * (N * B1 ^ m).trace =
        t ^ m * (N * (B1 - u • 1)).trace + u ^ m * (N * (t • 1 - B1)).trace := by
    have h := congrArg (fun M : BondMatrix P => (N * M).trace) hpow
    simpa only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_add, Matrix.trace_add]
      using h
  have hhalf : 2 * half = 1 := by simpa only [two_mul] using hh
  have hupper (j : Fin 3) :
      (tripletFeature half B0 B1 j * B0 ^ m).trace =
        ![r ^ m * r ^ 2 + s ^ m * s ^ 2,
          r ^ m * (r * p) + s ^ m * (s * (t + u - p)),
          r ^ m * ((t + u) * p - t * u) +
            s ^ m * ((t + u) * (t + u - p) - t * u)] j := by
    rw [show B0 ^ m = !![r ^ m, 0; 0, s ^ m] from sectionB0_pow r s m]
    fin_cases j <;>
      simp [B0, B1, sectionB0, sectionB1, tripletFeature, Matrix.trace_fin_two,
        pow_two, Matrix.vecMul, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]
    · ring
    · linear_combination (r ^ m * (r * p) + s ^ m * (s * (t + u - p))) * hhalf
    · ring
  let thetaT := r * q + s * (1 - q)
  let thetaU := r * (1 - q) + s * q
  have hlower (j : Fin 3) :
      (tripletFeature half B0 B1 j * B1 ^ m).trace =
        ![t ^ m * ((r + s) * thetaT - r * s) + u ^ m * ((r + s) * thetaU - r * s),
          t ^ m * (t * thetaT) + u ^ m * (u * thetaU),
          t ^ m * t ^ 2 + u ^ m * u ^ 2] j := by
    apply mul_left_cancel₀ he
    rw [hread]
    fin_cases j <;>
      simp [B0, B1, sectionB0, sectionB1, tripletFeature, Matrix.trace_fin_two,
        Matrix.vecMul, Matrix.mul_apply, dotProduct, Matrix.one_apply, Fin.sum_univ_two,
        thetaT, thetaU, pow_two]
    · ring
    · linear_combination ((t - u) * (t ^ m * (t * thetaT) + u ^ m * (u * thetaU))) * hhalf
    · ring
  unfold outerEntry
  rw [tripletReadout_section]
  fin_cases i
  · exact hupper 0
  · exact hupper 1
  · exact hupper 2
  · exact hlower 0
  · exact hlower 1
  · exact hlower 2


open private rootWeight rowDegree outerRows_isWeightedHomogeneous
  from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSection

/-- At fixed dimensionless section parameter, the four node derivatives
recover the radial column by Euler homogeneity. -/
theorem outer_radial (m : ℕ) (i : Fin 6) :
    r * pderiv 0 (outerRows m i) + s * pderiv 1 (outerRows m i) +
      t * pderiv 2 (outerRows m i) + u * pderiv 3 (outerRows m i) =
      (m + 2) • (outerRows (R := K) m i) := by
  have hd : rowDegree 1 1 m i = m + 2 := by
    fin_cases i <;> simp [rowDegree]
  have h := (outerRows_isWeightedHomogeneous (R := K) 1 1 m i).sum_weight_X_mul_pderiv
  rw [hd] at h
  simpa [rootWeight, Fin.sum_univ_five, add_assoc] using h

end Outer


section Transverse

open TrivSqZeroExt
open PeriodicMPSUniformAntisymmetricTransfer (coreCommutator commutatorDet)

private def liftCore (B : BondMatrix R) : BondMatrix (DualNumber R) :=
  B.map (inlHom R R)

private def jetBase {ι κ : Type*} (M : Matrix ι κ (DualNumber R)) : Matrix ι κ R :=
  M.map (fstHom R R R)

private def jetTangent {ι κ : Type*} (M : Matrix ι κ (DualNumber R)) : Matrix ι κ R :=
  M.map snd

private theorem jetTangent_mul {ι κ τ : Type*} [Fintype κ]
    (M : Matrix ι κ (DualNumber R)) (N : Matrix κ τ (DualNumber R)) :
    jetTangent (M * N) = jetBase M * jetTangent N + jetTangent M * jetBase N := by
  ext i j
  simp only [jetBase, jetTangent, Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply,
    snd_sum, snd_mul, fstHom_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, Finset.sum_add_distrib]

private theorem snd_trace {ι : Type*} [Fintype ι] (M : Matrix ι ι (DualNumber R)) :
    snd M.trace = (jetTangent M).trace := by
  simp [Matrix.trace, jetTangent, snd_sum]

private theorem jetBase_blocks (A B C D : BondMatrix (DualNumber R)) :
    jetBase (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (jetBase A) (jetBase B) (jetBase C) (jetBase D) := by
  ext (i | i) (j | j) <;> rfl

private theorem jetTangent_blocks (A B C D : BondMatrix (DualNumber R)) :
    jetTangent (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (jetTangent A) (jetTangent B) (jetTangent C) (jetTangent D) := by
  ext (i | i) (j | j) <;> rfl

private def transverseTransfer (B0 B1 : BondMatrix R) :=
  Matrix.fromBlocks (liftCore B0) (liftCore B1)
    ((inr (1 : R) : DualNumber R) • liftCore B1) (liftCore B1)

private theorem transverseTransfer_base (B0 B1 : BondMatrix R) :
    jetBase (transverseTransfer B0 B1) = sectionTransfer B0 B1 := by
  rw [transverseTransfer, jetBase_blocks, sectionTransfer]
  congr 1
  all_goals ext i j <;> simp [jetBase, liftCore, fst_mul, fstHom_apply, inlHom_apply]

private theorem transverseTransfer_tangent (B0 B1 : BondMatrix R) :
    jetTangent (transverseTransfer B0 B1) = Matrix.fromBlocks 0 0 B1 0 := by
  rw [transverseTransfer, jetTangent_blocks]
  congr 1
  all_goals ext i j <;> simp [jetTangent, liftCore, snd_mul, inlHom_apply]

private theorem transverseTransfer_pow_base (B0 B1 : BondMatrix R) (m : ℕ) :
    jetBase (transverseTransfer B0 B1 ^ m) =
      Matrix.fromBlocks (B0 ^ m) (literalCross B0 B1 m) 0 (B1 ^ m) := by
  change (transverseTransfer B0 B1 ^ m).map (fstHom R R R).toRingHom = _
  rw [Matrix.map_pow (transverseTransfer B0 B1) (fstHom R R R).toRingHom]
  change jetBase (transverseTransfer B0 B1) ^ m = _
  rw [transverseTransfer_base, sectionTransfer_pow]

private def reverseCross (B0 B1 : BondMatrix R) (m : ℕ) :=
  (literalCross B0.transpose B1.transpose m).transpose

private theorem reverseCross_succ (B0 B1 : BondMatrix R) (m : ℕ) :
    reverseCross B0 B1 (m + 1) = B1 ^ (m + 1) + reverseCross B0 B1 m * B0 := by
  have h := congrArg Matrix.toBlocks₁₂ (sectionTransfer_pow B0.transpose B1.transpose (m + 1))
  rw [pow_succ', sectionTransfer_pow, sectionTransfer, Matrix.fromBlocks_multiply] at h
  simp only [Matrix.toBlocks_fromBlocks₁₂] at h
  unfold reverseCross
  rw [← h, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    ← Matrix.transpose_pow, Matrix.transpose_transpose, Matrix.transpose_transpose, add_comm]
  simp only [Matrix.transpose_transpose, pow_succ]

private theorem transverseTransfer_pow_lower (B0 B1 : BondMatrix R) (m : ℕ) :
    (jetTangent (transverseTransfer B0 B1 ^ m)).toBlocks₂₁ = reverseCross B0 B1 m := by
  induction m with
  | zero =>
    change (jetTangent (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (DualNumber R))).toBlocks₂₁ = _
    ext i j
    simp [jetTangent, Matrix.toBlocks₂₁, Matrix.one_apply, reverseCross, literalCross]
  | succ m ih =>
    rw [pow_succ, jetTangent_mul, transverseTransfer_pow_base, transverseTransfer_base,
      transverseTransfer_tangent, sectionTransfer, reverseCross_succ]
    let M := jetTangent (transverseTransfer B0 B1 ^ m)
    change (Matrix.fromBlocks (B0 ^ m) (literalCross B0 B1 m) 0 (B1 ^ m) *
        Matrix.fromBlocks 0 0 B1 0 + M * Matrix.fromBlocks B0 B1 0 B1).toBlocks₂₁ = _
    rw [show M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
        from (Matrix.fromBlocks_toBlocks M).symm, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    rw [show Matrix.toBlocks₂₁
        (Matrix.fromBlocks (B0 ^ m * 0 + literalCross B0 B1 m * B1)
          (B0 ^ m * 0 + literalCross B0 B1 m * 0)
          (0 * 0 + B1 ^ m * B1) (0 * 0 + B1 ^ m * 0) +
        Matrix.fromBlocks (M.toBlocks₁₁ * B0 + M.toBlocks₁₂ * 0)
          (M.toBlocks₁₁ * B1 + M.toBlocks₁₂ * B1)
          (M.toBlocks₂₁ * B0 + M.toBlocks₂₂ * 0)
          (M.toBlocks₂₁ * B1 + M.toBlocks₂₂ * B1)) =
        (0 * 0 + B1 ^ m * B1) + (M.toBlocks₂₁ * B0 + M.toBlocks₂₂ * 0) from rfl]
    simp only [zero_mul, zero_add, mul_zero, add_zero, show M.toBlocks₂₁ = _ from ih, pow_succ]

private theorem reverseCross_difference (B0 B1 : BondMatrix R) (n : ℕ) :
    literalCross B0 B1 (n + 2) - reverseCross B0 B1 (n + 2) =
      PowerSeries.coeff n (completeSeries B0 B1) • (B0 * B1 - B1 * B0) := by
  unfold reverseCross
  rw [literalCross_eq, literalCross_eq]
  have hs : completeSeries B0.transpose B1.transpose = completeSeries B0 B1 := by
    simp only [completeSeries, Matrix.trace_transpose, Matrix.det_transpose]
  simp only [hs, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_one, ← Matrix.transpose_pow,
    Matrix.transpose_transpose, Matrix.det_transpose, smul_sub]
  abel

private theorem trace_transverse_insertion (N B0 B1 : BondMatrix R) (m : ℕ) (a b : R) :
    snd (((liftCore N ⊗ₖ
      (!![0, inl a; inr b, 0] : BondMatrix (DualNumber R))) *
      mixedTransfer (transverseKet (inr 1)) (pairedBra (liftCore B0) (liftCore B1)) ^ m).trace) =
      a * (N * reverseCross B0 B1 m).trace + b * (N * literalCross B0 B1 m).trace := by
  rw [← trace_inKetOrder, map_mul, map_pow, kronecker_inKetOrder, transfer_inKetOrder]
  let A : BondMatrix (DualNumber R) := !![0, inl a; inr b, 0]
  have h00 : A 0 0 = 0 := rfl
  have h01 : A 0 1 = inl a := rfl
  have h10 : A 1 0 = inr b := rfl
  have h11 : A 1 1 = 0 := rfl
  change snd ((Matrix.fromBlocks (A 0 0 • liftCore N) (A 0 1 • liftCore N)
    (A 1 0 • liftCore N) (A 1 1 • liftCore N) * transverseTransfer B0 B1 ^ m).trace) = _
  rw [h00, h01, h10, h11]
  rw [snd_trace, jetTangent_mul, transverseTransfer_pow_base]
  have hb : jetBase (Matrix.fromBlocks ((0 : DualNumber R) • liftCore N) ((inl a : DualNumber R) • liftCore N)
      ((inr b : DualNumber R) • liftCore N) ((0 : DualNumber R) • liftCore N)) = Matrix.fromBlocks (0 : BondMatrix R) (a • N) 0 0 := by
    rw [jetBase_blocks]
    congr 1
    all_goals ext i j : 1 <;> simp [jetBase, liftCore, fst_mul, fstHom_apply, inlHom_apply]
  have hd : jetTangent (Matrix.fromBlocks ((0 : DualNumber R) • liftCore N) ((inl a : DualNumber R) • liftCore N)
      ((inr b : DualNumber R) • liftCore N) ((0 : DualNumber R) • liftCore N)) = Matrix.fromBlocks (0 : BondMatrix R) 0 (b • N) 0 := by
    rw [jetTangent_blocks]
    congr 1
    all_goals ext i j : 1 <;> simp [jetTangent, liftCore, snd_mul, inlHom_apply]
  rw [hb, hd, Matrix.trace_add, Matrix.fromBlocks_multiply, trace_blocks]
  conv_lhs =>
    enter [1]
    rw [show jetTangent (transverseTransfer B0 B1 ^ m) =
        Matrix.fromBlocks (jetTangent (transverseTransfer B0 B1 ^ m)).toBlocks₁₁
          (jetTangent (transverseTransfer B0 B1 ^ m)).toBlocks₁₂
          (jetTangent (transverseTransfer B0 B1 ^ m)).toBlocks₂₁
          (jetTangent (transverseTransfer B0 B1 ^ m)).toBlocks₂₂ from
        (Matrix.fromBlocks_toBlocks _).symm,
      Matrix.fromBlocks_multiply, trace_blocks]
  simp only [transverseTransfer_pow_lower, zero_mul, zero_add, add_zero, smul_mul_assoc,
    Matrix.trace_smul, smul_eq_mul, Matrix.trace_zero]


private theorem liftCore_mul (M N : BondMatrix R) : liftCore (M * N) = liftCore M * liftCore N :=
  Matrix.map_mul (f := inlHom R R)

private theorem liftCore_feature (half : R) (B0 B1 : BondMatrix R) (j : Fin 3) :
    liftCore (tripletFeature half B0 B1 j) =
      tripletFeature (inl half) (liftCore B0) (liftCore B1) j := by
  fin_cases j
  · exact Matrix.map_pow B0 (inlHom R R) 2
  · change liftCore (half • (B0 * B1 + B1 * B0)) =
      inl half • (liftCore B0 * liftCore B1 + liftCore B1 * liftCore B0)
    rw [← liftCore_mul, ← liftCore_mul]
    ext i k : 1
    change (inlHom R R) (half * ((B0 * B1) i k + (B1 * B0) i k)) = _
    rw [map_mul, map_add]
    rfl
  · exact Matrix.map_pow B1 (inlHom R R) 2

private theorem middleKetFeature (half : R) :
    tripletFeature (inl half) (transverseKet (inr 1) 0) (transverseKet (inr 1) 1) 1 =
      !![0, inl half; inr half, 0] := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [transverseKet, tripletFeature, Matrix.mul_apply, Fin.sum_univ_two, snd_mul,
      smul_eq_mul, inl_mul_inr, inl_mul_eq_smul]

private theorem trace_feature_commutator (half : R) (B0 B1 : BondMatrix R) (j : Fin 3) :
    (tripletFeature half B0 B1 j * (B0 * B1 - B1 * B0)).trace = 0 := by
  fin_cases j <;>
    simp [tripletFeature, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;>
      ring

/-- The transverse derivative of the literal middle triplet row is the
ordered convolution column of the checked middle block. -/
theorem transverse_middle_eq (half : R) (hh : half + half = 1)
    (B0 B1 : BondMatrix R) (n : ℕ) (j : Fin 3) :
    snd (tripletReadout (inl half) (transverseKet (inr 1))
      (pairedBra (liftCore B0) (liftCore B1)) (n + 2) 1 j) =
        middleTraceBlock half B0 B1 (n + 2) j 2 := by
  simp only [tripletReadout, Matrix.of_apply, pairedBra, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  rw [middleKetFeature, ← liftCore_feature]
  let N := tripletFeature half B0 B1 j
  change snd (((liftCore N ⊗ₖ (!![0, inl half; inr half, 0] : BondMatrix (DualNumber R))) *
    mixedTransfer (transverseKet (inr 1)) (pairedBra (liftCore B0) (liftCore B1)) ^ (n + 2)).trace) = _
  rw [trace_transverse_insertion N B0 B1 (n + 2) half half]
  have ht : (N * literalCross B0 B1 (n + 2)).trace =
      (N * reverseCross B0 B1 (n + 2)).trace := by
    apply sub_eq_zero.mp
    rw [← Matrix.trace_sub, ← mul_sub, reverseCross_difference, Matrix.mul_smul,
      Matrix.trace_smul, trace_feature_commutator, smul_zero]
  change half * (N * reverseCross B0 B1 (n + 2)).trace +
    half * (N * literalCross B0 B1 (n + 2)).trace = (N * literalCross B0 B1 (n + 2)).trace
  rw [← ht, ← add_mul, hh, one_mul]

/-- The singlet readout over a coefficient ring with a specified half scalar.
It is the four-entry contraction of the native mixed transfer. -/
def singletTrace (half : R) (ket bra : Fin 2 → BondMatrix R) (m : ℕ) : R :=
  half * ((coreCommutator bra ⊗ₖ coreCommutator ket) * mixedTransfer ket bra ^ m).trace

/-- The same trace over any coefficient ring gives the four native singlet
entries with the standard signs. -/
theorem singletTrace_eq_native (half : R) (ket bra : Fin 2 → BondMatrix R) (m : ℕ) :
    singletTrace half ket bra m =
      half * (mixedRaw ket bra m (0, 1) (0, 1) - mixedRaw ket bra m (1, 0) (0, 1) -
        mixedRaw ket bra m (0, 1) (1, 0) + mixedRaw ket bra m (1, 0) (1, 0)) := by
  rw [singletTrace, PeriodicMPSUniformAntisymmetricTransfer.coreCommutator,
    PeriodicMPSUniformAntisymmetricTransfer.coreCommutator]
  have hneg₁ (A B : BondMatrix R) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
    ext i j
    simp [Matrix.kroneckerMap_apply]
  have hneg₂ (A B : BondMatrix R) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
    ext i j
    simp [Matrix.kroneckerMap_apply]
  simp only [sub_eq_add_neg, Matrix.add_kronecker, Matrix.kronecker_add, hneg₁,
    hneg₂, add_mul, neg_mul, Matrix.trace_add, Matrix.trace_neg,
    mixedRaw, binaryInsertion]
  ring

private theorem liftCore_commutator (B0 B1 : BondMatrix R) :
    liftCore (coreCommutator (pairedBra B0 B1)) =
      coreCommutator (pairedBra (liftCore B0) (liftCore B1)) := by
  simp only [pairedBra, coreCommutator, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  rw [← liftCore_mul, ← liftCore_mul]
  ext i j : 1
  exact map_sub (inlHom R R) _ _

private theorem transverse_commutator :
    coreCommutator (transverseKet (inr (1 : R) : DualNumber R)) =
      !![0, inl (1 : R); inr (-1 : R), 0] := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [coreCommutator, transverseKet, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_commutator_sq (B0 B1 : BondMatrix R) :
    let N := coreCommutator (pairedBra B0 B1)
    (N * N).trace = -(2 * N.det) := by
  simp [coreCommutator, pairedBra, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The transverse derivative of the normalized singlet contraction, at the
same literal transfer jet used in the middle triplet comparison. -/
theorem transverse_singlet_eq (half : R) (hh : half + half = 1)
    (B0 B1 : BondMatrix R) (n : ℕ) :
    snd (singletTrace (inl half) (transverseKet (inr 1))
      (pairedBra (liftCore B0) (liftCore B1)) (n + 2)) =
      commutatorDet (pairedBra B0 B1) * PowerSeries.coeff n (completeSeries B0 B1) := by
  unfold singletTrace
  rw [transverse_commutator, ← liftCore_commutator]
  simp only [snd_mul, fst_inl, snd_inl, zero_smul, smul_zero, add_zero, smul_eq_mul]
  rw [trace_transverse_insertion]
  let N := coreCommutator (pairedBra B0 B1)
  change half * (1 * (N * reverseCross B0 B1 (n + 2)).trace +
    (-1) * (N * literalCross B0 B1 (n + 2)).trace) =
      N.det * PowerSeries.coeff n (completeSeries B0 B1)
  rw [one_mul, neg_one_mul, ← sub_eq_add_neg, ← neg_sub, ← Matrix.trace_sub,
    ← mul_sub, reverseCross_difference, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  change half * -(PowerSeries.coeff n (completeSeries B0 B1) * (N * N).trace) = _
  rw [trace_commutator_sq]
  linear_combination
    (N.det * PowerSeries.coeff n (completeSeries B0 B1)) * hh

end Transverse

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSectionRank
