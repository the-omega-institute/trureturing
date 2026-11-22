/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful three-qubit states with shared pair marginals and exact trace distance. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.Pauli.PauliMatrix

/-! Three-qubit density supplier for preregistration #32416, following the question
of Capel and Costa Rico, arXiv:2608.15833v1, Open questions 6. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicDensity

open Matrix
open scoped BigOperators ComplexOrder CStarAlgebra Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceDistance)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight partialTraceRight_add partialTraceRight_kronecker)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)

noncomputable section

abbrev Bit := Fin 2
abbrev Pair := Bit × Bit
abbrev Triple := Pair × Bit

/-- The basis is ordered as `((a,b),c)`. -/
def ZZ : Matrix Triple Triple ℂ :=
  (pauliMatrix .Z ⊗ₖ pauliMatrix .Z) ⊗ₖ pauliMatrix .I

def XZZ : Matrix Triple Triple ℂ :=
  (pauliMatrix .X ⊗ₖ pauliMatrix .Z) ⊗ₖ pauliMatrix .Z

def amplitude (u eta : ℝ) : ℝ := (1 - eta) * Real.sqrt (u * (1 - u))

/-- `w` is the off-diagonal coefficient before the block weight of one quarter. -/
def familyMatrix (u w : ℝ) : Matrix Triple Triple ℂ :=
  (1 / 8 : ℝ) • (1 + (1 - 2 * u) • ZZ) + (w / 4) • XZZ

def SMatrix (u : ℝ) : Matrix Triple Triple ℂ := familyMatrix u 0

def RMatrix (u eta : ℝ) : Matrix Triple Triple ℂ := familyMatrix u (amplitude u eta)

private theorem x_mul_x : qubitX * qubitX = 1 := by
  simpa only [pow_two] using qubit_weyl_star.2.2.2.1

private theorem z_mul_z : qubitZ * qubitZ = 1 := by
  simpa only [pow_two] using qubit_weyl_star.2.2.2.2

private theorem x_conjTranspose : qubitXᴴ = qubitX :=
  qubit_weyl_star.2.1

private theorem z_conjTranspose : qubitZᴴ = qubitZ :=
  qubit_weyl_star.2.2.1

private theorem zz_hermitian : ZZ.IsHermitian := by
  change (((qubitZ ⊗ₖ qubitZ) ⊗ₖ (1 : Matrix Bit Bit ℂ))ᴴ) = _
  simp only [conjTranspose_kronecker, z_conjTranspose, conjTranspose_one, ZZ, pauliMatrix]

theorem xzz_hermitian : XZZ.IsHermitian := by
  change (((qubitX ⊗ₖ qubitZ) ⊗ₖ qubitZ)ᴴ) = _
  simp only [conjTranspose_kronecker, x_conjTranspose, z_conjTranspose, XZZ, pauliMatrix]

private theorem zz_mul_zz : ZZ * ZZ = 1 := by
  simp only [ZZ, pauliMatrix, ← mul_kronecker_mul, z_mul_z, mul_one, one_kronecker_one]

theorem xzz_mul_xzz : XZZ * XZZ = 1 := by
  simp only [XZZ, pauliMatrix, ← mul_kronecker_mul, x_mul_x, z_mul_z, one_kronecker_one]

private theorem zz_mul_xzz : ZZ * XZZ = -(XZZ * ZZ) := by
  simp only [ZZ, XZZ, pauliMatrix, ← mul_kronecker_mul, z_mul_z, one_mul, mul_one,
    qubit_weyl_star.1]
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  simp only [kronecker_apply, Matrix.neg_apply, neg_mul]

private theorem one_add_posSemidef_of_involution {H : Matrix Triple Triple ℂ}
    (hH : H.IsHermitian) (hSq : H * H = 1) : (1 + H).PosSemidef := by
  have hGram : (1 + H)ᴴ * (1 + H) = (2 : ℝ) • (1 + H) := by
    rw [conjTranspose_add, conjTranspose_one, hH.eq]
    simp only [add_mul, mul_add, one_mul, mul_one, hSq, two_smul] <;> abel
  have h := (posSemidef_conjTranspose_mul_self (1 + H)).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rwa [hGram, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

/-- The Pauli involution determining the unsmoothed state. -/
def endpointInvolution (u : ℝ) : Matrix Triple Triple ℂ :=
  (1 - 2 * u) • ZZ + (2 * Real.sqrt (u * (1 - u))) • XZZ

theorem endpoint_involution {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) :
    (endpointInvolution u).IsHermitian ∧ endpointInvolution u * endpointInvolution u = 1 := by
  let w : ℝ := Real.sqrt (u * (1 - u))
  have hw : w * w = u * (1 - u) :=
    Real.mul_self_sqrt (mul_nonneg hu.le (by linarith))
  have hcoef : (1 - 2 * u) * (1 - 2 * u) + (2 * w) * (2 * w) = 1 := by
    calc
      _ = 1 + 4 * (w * w - u * (1 - u)) := by ring
      _ = 1 := by rw [hw, sub_self, mul_zero, add_zero]
  constructor
  · exact (zz_hermitian.smul (IsSelfAdjoint.all _)).add
      (xzz_hermitian.smul (IsSelfAdjoint.all _))
  · calc
      endpointInvolution u * endpointInvolution u =
          ((1 - 2 * u) * (1 - 2 * u) + (2 * w) * (2 * w)) • (1 : Matrix Triple Triple ℂ) := by
        change ((1 - 2 * u) • ZZ + (2 * w) • XZZ) * ((1 - 2 * u) • ZZ + (2 * w) • XZZ) = _
        simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          zz_mul_zz, xzz_mul_xzz, zz_mul_xzz, smul_neg]
        module
      _ = 1 := by rw [hcoef, one_smul]

theorem familyMatrix_endpoint_eq (u : ℝ) :
    familyMatrix u (Real.sqrt (u * (1 - u))) = (1 / 8 : ℝ) • (1 + endpointInvolution u) := by
  unfold familyMatrix endpointInvolution
  module

/-- The unsmoothed state is positive semidefinite, by the Pauli involution. -/
theorem familyMatrix_endpoint_posSemidef {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) :
    (familyMatrix u (Real.sqrt (u * (1 - u)))).PosSemidef := by
  obtain ⟨hH, hSq⟩ := endpoint_involution hu hhalf
  rw [familyMatrix_endpoint_eq]
  exact (one_add_posSemidef_of_involution hH hSq).smul (by norm_num : (0 : ℝ) ≤ 1 / 8)

/-- For the reference the diagonal is bounded below by `u/4`. -/
theorem SMatrix_posDef {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) :
    (SMatrix u).PosDef := by
  have heq : SMatrix u =
      (1 - 2 * u) • ((1 / 8 : ℝ) • (1 + ZZ)) + (u / 4) • (1 : Matrix Triple Triple ℂ) := by
    unfold SMatrix familyMatrix
    module
  rw [heq]
  exact Matrix.PosDef.posSemidef_add
    (((one_add_posSemidef_of_involution zz_hermitian zz_mul_zz).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 8)).smul (by linarith : 0 ≤ 1 - 2 * u))
    (Matrix.PosDef.one.smul (div_pos hu (by norm_num)))

/-- The regularization is the convex mixture from the preregistration. -/
theorem RMatrix_eq_mix (u eta : ℝ) :
    RMatrix u eta = (1 - eta) • familyMatrix u (Real.sqrt (u * (1 - u))) + eta • SMatrix u := by
  unfold RMatrix SMatrix familyMatrix amplitude
  module

theorem RMatrix_posDef {u eta : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2)
    (heta : 0 < eta) (hetaOne : eta < 1) : (RMatrix u eta).PosDef := by
  rw [RMatrix_eq_mix]
  exact Matrix.PosDef.posSemidef_add
    ((familyMatrix_endpoint_posSemidef hu hhalf).smul (sub_nonneg.mpr hetaOne.le))
    ((SMatrix_posDef hu hhalf).smul heta)

private theorem trace_x : qubitX.trace = 0 := by norm_num [trace_fin_two, qubitX]
private theorem trace_z : qubitZ.trace = 0 := by norm_num [trace_fin_two, qubitZ]

theorem familyMatrix_trace (u w : ℝ) : (familyMatrix u w).trace = 1 := by
  norm_num [familyMatrix, ZZ, XZZ, pauliMatrix, trace_kronecker, trace_x, trace_z,
    trace_one, Triple, Pair, Bit, Fintype.card_prod, Fintype.card_fin,
    RCLike.real_smul_eq_coe_mul (K := ℂ)] <;> push_cast <;> ring

private def densityOfMatrix (M : Matrix Triple Triple ℂ) (hM : M.PosSemidef)
    (htr : M.trace = 1) : DensityState Triple :=
  ⟨CStarMatrix.ofMatrix M, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg, htr⟩

/-- The faithful reference density state. -/
def S (u : ℝ) (hu : 0 < u) (hhalf : u < 1 / 2) : DensityState Triple :=
  densityOfMatrix (SMatrix u) (SMatrix_posDef hu hhalf).posSemidef (familyMatrix_trace u 0)

/-- The faithful regularized density state. -/
def R (u eta : ℝ) (hu : 0 < u) (hhalf : u < 1 / 2)
    (heta : 0 < eta) (hetaOne : eta < 1) : DensityState Triple :=
  densityOfMatrix (RMatrix u eta) (RMatrix_posDef hu hhalf heta hetaOne).posSemidef
    (familyMatrix_trace u (amplitude u eta))

/-- Reorder `((a,b),c)` as `(a,(b,c))` to expose the classical flags. -/
abbrev flagsReorder : Triple ≃ Bit × Pair := Equiv.prodAssoc Bit Bit Bit

private def forAC (i : Pair × Bit) : Triple := ((i.1.1, i.2), i.1.2)

def marginalAB (M : Matrix Triple Triple ℂ) : Matrix Pair Pair ℂ :=
  partialTraceRight M

def marginalAC (M : Matrix Triple Triple ℂ) : Matrix Pair Pair ℂ :=
  partialTraceRight (M.submatrix forAC forAC)

def marginalBC (M : Matrix Triple Triple ℂ) : Matrix Pair Pair ℂ :=
  partialTraceLeft (M.submatrix flagsReorder.symm flagsReorder.symm)

def abMatrix (u : ℝ) : Matrix Pair Pair ℂ :=
  (1 / 4 : ℝ) • (1 + (1 - 2 * u) • (pauliMatrix .Z ⊗ₖ pauliMatrix .Z))

def mixedBit : Matrix Bit Bit ℂ := (1 / 2 : ℝ) • 1
def mixedPair : Matrix Pair Pair ℂ := (1 / 4 : ℝ) • 1

private theorem partialTraceRight_smul {A B : Type*} [Fintype B] (r : ℝ)
    (M : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (r • M) = r • partialTraceRight M := by
  ext i j
  simp [partialTraceRight, Finset.smul_sum]

theorem familyMatrix_marginalAB (u w : ℝ) : marginalAB (familyMatrix u w) = abMatrix u := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
    norm_num [marginalAB, partialTraceRight, Fin.sum_univ_two, familyMatrix, abMatrix,
      ZZ, XZZ, pauliMatrix, qubitX, qubitZ, kronecker_apply, Matrix.one_apply,
      Prod.mk_inj, RCLike.real_smul_eq_coe_mul (K := ℂ)] <;> push_cast <;> ring

theorem familyMatrix_marginalAC (u w : ℝ) : marginalAC (familyMatrix u w) = mixedPair := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  fin_cases a <;> fin_cases a' <;> fin_cases c <;> fin_cases c' <;>
    norm_num [marginalAC, partialTraceRight, forAC, Matrix.submatrix_apply, Fin.sum_univ_two,
      familyMatrix, mixedPair, ZZ, XZZ, pauliMatrix, qubitX, qubitZ, kronecker_apply,
      Matrix.one_apply, Prod.mk_inj, RCLike.real_smul_eq_coe_mul (K := ℂ)] <;>
    push_cast <;> ring

theorem familyMatrix_marginalBC (u w : ℝ) : marginalBC (familyMatrix u w) = mixedPair := by
  ext ⟨b, c⟩ ⟨b', c'⟩
  fin_cases b <;> fin_cases b' <;> fin_cases c <;> fin_cases c' <;>
    norm_num [marginalBC, partialTraceLeft, flagsReorder, Equiv.prodAssoc_symm_apply,
      Matrix.submatrix_apply, Fin.sum_univ_two, familyMatrix, mixedPair, ZZ, XZZ,
      pauliMatrix, qubitX, qubitZ, kronecker_apply,
      Matrix.one_apply, Prod.mk_inj, RCLike.real_smul_eq_coe_mul (K := ℂ)] <;>
    push_cast <;> ring

/-- All three pair marginals coincide within a pair. The last two are independent of both parameters. -/
theorem pair_marginals {u eta : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2)
    (heta : 0 < eta) (hetaOne : eta < 1) :
    let r := CStarMatrix.ofMatrix.symm (R u eta hu hhalf heta hetaOne).val
    let s := CStarMatrix.ofMatrix.symm (S u hu hhalf).val
    marginalAB r = abMatrix u ∧ marginalAB s = abMatrix u ∧
    marginalAC r = mixedPair ∧ marginalAC s = mixedPair ∧
    marginalBC r = mixedPair ∧ marginalBC s = mixedPair :=
  ⟨familyMatrix_marginalAB u _, familyMatrix_marginalAB u _,
    familyMatrix_marginalAC u _, familyMatrix_marginalAC u _,
    familyMatrix_marginalBC u _, familyMatrix_marginalBC u _⟩

/-- The reference is the common `AB` marginal tensored with the uniform `C` state. -/
theorem SMatrix_eq_product (u : ℝ) : SMatrix u = abMatrix u ⊗ₖ mixedBit := by
  simp only [SMatrix, familyMatrix, abMatrix, mixedBit, ZZ, pauliMatrix,
    zero_div, zero_smul, add_zero, kronecker_smul, smul_kronecker, add_kronecker,
    one_kronecker_one]
  module

/-- The normalized qubit block at flags `(b,c)`. -/
def block (u w : ℝ) (b c : Bit) : Matrix Bit Bit ℂ :=
  let d0 : ℝ := if b = 0 then 1 - u else u
  let d1 : ℝ := if b = 0 then u else 1 - u
  let off : ℝ := if b = c then w else -w
  !![↑d0, ↑off; ↑off, ↑d1]

set_option maxHeartbeats 1000000 in
/-- The four classical flags have weight one quarter. Each block acts on qubit `A`. -/
theorem familyMatrix_blocks (u w : ℝ) :
    (familyMatrix u w).submatrix flagsReorder.symm flagsReorder.symm =
      (1 / 4 : ℝ) • Matrix.blockDiagonal (fun bc : Pair => block u w bc.1 bc.2) := by
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  change familyMatrix u w ((a, b), c) ((a', b'), c') =
    ((1 / 4 : ℝ) • Matrix.blockDiagonal (fun bc : Pair => block u w bc.1 bc.2))
      (a, (b, c)) (a', (b', c'))
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;> fin_cases c <;> fin_cases c' <;>
    norm_num [familyMatrix, ZZ, XZZ, pauliMatrix, qubitX, qubitZ, kronecker_apply,
      blockDiagonal_apply, block, Matrix.one_apply, Prod.mk_inj,
      RCLike.real_smul_eq_coe_mul (K := ℂ)] <;>
    push_cast <;> ring

theorem block_trace (u w : ℝ) (b c : Bit) : (block u w b c).trace = 1 := by
  simp only [block, trace_fin_two_of]
  split_ifs <;> push_cast <;> ring

theorem block_det (u w : ℝ) (b c : Bit) :
    (block u w b c).det = ((u * (1 - u) - w ^ 2 : ℝ) : ℂ) := by
  simp only [block, det_fin_two_of]
  split_ifs <;> push_cast <;> ring

/-- The trace distance is half the trace of a scalar identity: the perturbing
Pauli string is a self-adjoint unitary. -/
theorem traceDistance_R_S {u eta : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2)
    (heta : 0 < eta) (hetaOne : eta < 1) :
    traceDistance (R u eta hu hhalf heta hetaOne) (S u hu hhalf) = amplitude u eta := by
  let t : ℝ := amplitude u eta / 4
  have ht : 0 ≤ t := div_nonneg
    (mul_nonneg (sub_nonneg.mpr hetaOne.le) (Real.sqrt_nonneg _)) (by norm_num)
  have hdiff : RMatrix u eta - SMatrix u = t • XZZ := by
    unfold RMatrix SMatrix familyMatrix t
    module
  change traceNorm (RMatrix u eta - SMatrix u) / 2 = amplitude u eta
  rw [hdiff, traceNorm]
  have hHerm : (t • XZZ).IsHermitian := xzz_hermitian.smul (IsSelfAdjoint.all _)
  have hGram : (t • (1 : Matrix Triple Triple ℂ)) * (t • 1) = (t • XZZ)ᴴ * (t • XZZ) := by
    rw [hHerm.eq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, xzz_mul_xzz, mul_one]
  have hpos : 0 ≤ t • (1 : Matrix Triple Triple ℂ) := (Matrix.PosSemidef.one.smul ht).nonneg
  rw [CFC.sqrt_unique hGram hpos, trace_smul, trace_one]
  change ((t • (Fintype.card Triple : ℂ)) : ℂ).re / 2 = amplitude u eta
  simp only [Complex.smul_re, Complex.natCast_re]
  norm_num [Triple, Pair, Bit, Fintype.card_prod, Fintype.card_fin, t] <;> ring

end

end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicDensity
