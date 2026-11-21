/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact geodesic relative entropy at the unsmoothed forward three-qubit witness. -/

import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicDensity
import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoGeodesicModular
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity
import Mathlib.LinearAlgebra.Matrix.Vec

/-! The unsmoothed forward witness for preregistration #32416, using equations
(52), (59) and (63) of Capel and Costa Rico, arXiv:2608.15833v1. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicBoundary

open Matrix
open scoped BigOperators ComplexOrder CStarAlgebra Kronecker Matrix MatrixOrder
  Matrix.Norms.L2Operator
open CapelCostaRicoForwardGeodesicDensity
open CapelCostaRicoReverseGeodesicCMI
  (geodesicRelativeEntropy geodesicModular geodesicModular_eq_kronecker)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open StabilizerPairLocalUnitaryInequivalence (pauliMatrix)

noncomputable section

private theorem cfc_diagonal (f : ℝ → ℝ) {n : Type*} [Fintype n] [DecidableEq n]
    (w : n → ℝ) :
    cfc f (diagonal fun i => (w i : ℂ)) = diagonal fun i => (f (w i) : ℂ) := by
  simpa [Function.comp_def] using Matrix.cfc_diagonal_real (𝕜 := ℂ) w f

private theorem spectrum_scaled_projection {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (k : ℝ) (hH : H * H = k • H)
    {x : ℝ} (hx : x ∈ spectrum ℝ H) : x = 0 ∨ x = k := by
  by_contra! hn
  let a : ℝ := x⁻¹
  let b : ℝ := (x * (x-k))⁻¹
  let B : Matrix n n ℂ := a • 1 + b • H
  have ha : x * a = 1 := mul_inv_cancel₀ hn.1
  have hb : x * b = a + b * k := by
    dsimp only [a,b]
    have hne : x - k ≠ 0 := sub_ne_zero.mpr hn.2
    field_simp
    ring
  have hleft : (x • (1 : Matrix n n ℂ) - H) * B = 1 := by
    dsimp only [B]
    simp only [sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, smul_smul, hH]
    rw [mul_comm a x, ha, one_smul, mul_comm b x, hb]
    simp only [add_smul]
    abel
  have hright : B * (x • (1 : Matrix n n ℂ) - H) = 1 := by
    dsimp only [B]
    simp only [mul_sub, add_mul, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, smul_smul, hH]
    rw [ha, one_smul, hb]
    simp only [add_smul]
    abel
  apply hx
  change IsUnit (algebraMap ℝ (Matrix n n ℂ) x - H)
  rw [Algebra.algebraMap_eq_smul_one]
  exact ⟨⟨_, B, hleft, hright⟩, rfl⟩

private theorem cfc_scaled_projection {n : Type} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ) (hE : E.IsHermitian) (hEE : E * E = E)
    (f : ℝ → ℝ) (hf : f 0 = 0) (k : ℝ) :
    cfc f (k • E) = f k • E := by
  by_cases hk : k = 0
  · simp [hk, hf]
  have hH : IsSelfAdjoint (k • E) := hE.smul (by simp [IsSelfAdjoint])
  have hHH : (k • E) * (k • E) = k • (k • E) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hEE]
  have hspec : ∀ x ∈ spectrum ℝ (k • E), x = 0 ∨ x = k :=
    fun _ hx => spectrum_scaled_projection (k • E) k hHH hx
  calc
    cfc f (k • E) = cfc ((f k / k) * ·) (k • E) := by
      apply cfc_congr
      intro x hx
      rcases hspec x hx with h | h
      · rw [h]; simp [hf]
      · rw [h]; exact (div_mul_cancel₀ (f k) hk).symm
    _ = f k • E := by
      rw [cfc_const_mul_id _ _ hH, smul_smul, div_mul_cancel₀ _ hk]

/-- If the state is a scalar multiple of a projection and the whitened state
is twice a projection, the geodesic form is the reference weight of the
whitened projection times the scalar value of x log x at two. -/
theorem geodesicRelativeEntropy_of_whitened_projection {n : Type} [Fintype n] [DecidableEq n]
    (r s P Q : Matrix n n ℂ) {k t : ℝ} (hk : 0 < k) (ht₀ : 0 < t) (ht₁ : t ≤ 1)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) (hr : r = k • P)
    (hsq : cfc Real.sqrt s * cfc Real.sqrt s = s)
    (hinv : cfc Real.sqrt s * cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s = 1)
    (hwhite : cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s * r *
      cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s = (2 : ℝ) • Q) :
    geodesicRelativeEntropy t r s = (2 * Real.log 2) * (s * Q).trace.re := by
  let D : Matrix n n ℂ := cfc Real.sqrt s
  let T : Matrix n n ℂ := cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s
  let L : Matrix n n ℂ := if t = 1 then 1 else P
  change D * D = s at hsq
  change D * T = 1 at hinv
  change T * r * T = (2 : ℝ) • Q at hwhite
  have hrHerm : r.IsHermitian := by
    rw [hr]
    exact hP.smul (IsSelfAdjoint.all _)
  have hDHerm : D.IsHermitian := by
    exact (IsSelfAdjoint.cfc (a := s) (f := Real.sqrt)).isHermitian
  have hTP : T * P * T = (k⁻¹ * 2) • Q := by
    calc
      _ = k⁻¹ • (T * r * T) := by
        rw [hr, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
      _ = _ := by rw [hwhite, smul_smul]
  have hDQ : D * Q = (k / 2) • (P * T) := by
    have htwice : (2 : ℝ) • (D * Q) = k • (P * T) := by
      calc
        _ = D * (T * r * T) := by rw [hwhite, Matrix.mul_smul]
        _ = _ := by
          rw [← mul_assoc D (T * r) T, ← mul_assoc D T r, hinv, one_mul, hr, Matrix.smul_mul]
    calc
      _ = (1 / 2 : ℝ) • ((2 : ℝ) • (D * Q)) := by
        rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
      _ = _ := by
        rw [htwice, smul_smul, show (1 / 2 : ℝ) * k = k / 2 by ring]
  have hL : L * (D * Q) = D * Q := by
    by_cases ht : t = 1
    · simp only [L, if_pos ht, one_mul]
    · rw [show L = P by simp only [L, if_neg ht], hDQ, Matrix.mul_smul,
        ← mul_assoc P P T, hPP]
  have hpow (p : ℝ) (hp : 0 < p) :
      cfc (fun z : ℝ => z ^ p) r = (k ^ p) • P := by
    rw [hr]
    exact cfc_scaled_projection P hP hPP (fun z => z ^ p) (Real.zero_rpow hp.ne') k
  have hMod : geodesicModular t r s = (2 : ℝ) • (L ⊗ₖ Qᵀ) := by
    rw [geodesicModular_eq_kronecker]
    change cfc (fun z : ℝ => z ^ (1 - t)) r ⊗ₖ
      (T * cfc (fun z : ℝ => z ^ t) r * T)ᵀ = _
    by_cases ht : t = 1
    · simp only [ht, sub_self, Real.rpow_zero, Real.rpow_one,
        cfc_const_one ℝ r hrHerm.isSelfAdjoint, cfc_id' ℝ r hrHerm.isSelfAdjoint,
        hwhite, transpose_smul, kronecker_smul, L, if_true]
    · have hscale : k ^ (1 - t) * (k ^ t * (k⁻¹ * 2)) = 2 := by
        rw [← mul_assoc (k ^ (1 - t)) (k ^ t), ← Real.rpow_add hk, sub_add_cancel,
          Real.rpow_one, ← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
      rw [hpow (1 - t) (sub_pos.mpr (lt_of_le_of_ne ht₁ ht)), hpow t ht₀,
        Matrix.mul_smul, Matrix.smul_mul, hTP, smul_smul, transpose_smul,
        smul_kronecker, kronecker_smul, smul_smul, hscale, show L = P by simp only [L, if_neg ht]]
  have hLHerm : L.IsHermitian := by
    by_cases ht : t = 1
    · simpa only [L, if_pos ht] using (Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian)
    · simpa only [L, if_neg ht] using hP
  have hLL : L * L = L := by
    by_cases ht : t = 1
    · simp only [L, if_pos ht, one_mul]
    · simpa only [L, if_neg ht] using hPP
  have hE : (L ⊗ₖ Qᵀ).IsHermitian := by
    change (L ⊗ₖ Qᵀ)ᴴ = _
    rw [conjTranspose_kronecker, hLHerm.eq, hQ.transpose.eq]
  have hEE : (L ⊗ₖ Qᵀ) * (L ⊗ₖ Qᵀ) = L ⊗ₖ Qᵀ := by
    rw [← mul_kronecker_mul, hLL, ← transpose_mul Q Q, hQQ]
  have hAct : (L ⊗ₖ Qᵀ) *ᵥ Dᵀ.vec = (D * Q)ᵀ.vec := by
    rw [kronecker_mulVec_vec, ← transpose_mul D Q, ← transpose_mul L (D * Q), hL]
  have hInner : star Dᵀ.vec ⬝ᵥ (D * Q)ᵀ.vec = (s * Q).trace := by
    rw [star_vec_dotProduct_vec, conjTranspose_transpose_eq_transpose_conjTranspose,
      hDHerm.eq, ← transpose_mul (D * Q) D, trace_transpose, trace_mul_comm (D * Q) D,
      ← mul_assoc D D Q, hsq]
  unfold geodesicRelativeEntropy
  change (star Dᵀ.vec ⬝ᵥ
    (cfc (fun z : ℝ => z * Real.log z) (geodesicModular t r s) *ᵥ Dᵀ.vec)).re = _
  rw [hMod, cfc_scaled_projection _ hE hEE (fun z => z * Real.log z) (zero_mul _) 2,
      Matrix.smul_mulVec, hAct, dotProduct_smul, hInner] <;>
    simp only [Complex.smul_re, smul_eq_mul]

/-- The spectral projection of the unsmoothed density. -/
def endpointProjection (u : ℝ) : Matrix Triple Triple ℂ :=
  (1 / 2 : ℝ) • (1 + endpointInvolution u)

/-- The spectral projection of the whitened unsmoothed density. -/
def whitenedProjection : Matrix Triple Triple ℂ :=
  (1 / 2 : ℝ) • (1 + XZZ)

private theorem half_one_add_projection {H : Matrix Triple Triple ℂ}
    (hH : H.IsHermitian) (hHH : H * H = 1) :
    let P := (1 / 2 : ℝ) • (1 + H)
    P.IsHermitian ∧ P * P = P := by
  dsimp only
  refine ⟨(Matrix.isHermitian_one.add hH).smul (IsSelfAdjoint.all _), ?_⟩
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add, mul_one, one_mul, hHH]
  module

/-- The endpoint is one quarter of the projection from its Pauli involution. -/
theorem RMatrix_zero_eq_projection (u : ℝ) :
    RMatrix u 0 = (1 / 4 : ℝ) • endpointProjection u := by
  rw [RMatrix, amplitude, sub_zero, one_mul, familyMatrix_endpoint_eq, endpointProjection,
    smul_smul] <;> norm_num

/-- Each diagonal entry has the weight determined by the parity of the first two qubits. -/
def referenceDiagonal (u : ℝ) (i : Triple) : ℝ :=
  (if i.1.1 = i.1.2 then 1 - u else u) / 4

set_option maxHeartbeats 1000000 in
theorem SMatrix_eq_diagonal (u : ℝ) :
    SMatrix u = Matrix.diagonal (fun i => (referenceDiagonal u i : ℂ)) := by
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;> fin_cases c <;> fin_cases c' <;>
    norm_num [SMatrix, familyMatrix, referenceDiagonal, ZZ, pauliMatrix, qubitZ,
      kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply, Prod.mk_inj,
      RCLike.real_smul_eq_coe_mul (K := ℂ)] <;>
    push_cast <;> ring

private theorem referenceDiagonal_pos {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) (i : Triple) :
    0 < referenceDiagonal u i := by
  unfold referenceDiagonal
  split_ifs <;> linarith

private theorem reference_sqrt_sq {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) :
    cfc Real.sqrt (SMatrix u) * cfc Real.sqrt (SMatrix u) = SMatrix u := by
  have h (i : Triple) :
      Real.sqrt (referenceDiagonal u i) * Real.sqrt (referenceDiagonal u i) =
        referenceDiagonal u i := Real.mul_self_sqrt (referenceDiagonal_pos hu hhalf i).le
  simp only [SMatrix_eq_diagonal, cfc_diagonal, diagonal_mul_diagonal, ← Complex.ofReal_mul, h]

private theorem reference_sqrt_mul_inv {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) :
    cfc Real.sqrt (SMatrix u) * cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u) = 1 := by
  have h (i : Triple) :
      Real.sqrt (referenceDiagonal u i) * (Real.sqrt (referenceDiagonal u i))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (referenceDiagonal_pos hu hhalf i)).ne'
  simp only [SMatrix_eq_diagonal, cfc_diagonal, diagonal_mul_diagonal, ← Complex.ofReal_mul, h,
    Complex.ofReal_one, diagonal_one]

set_option maxHeartbeats 1000000 in
private theorem reference_sqrt_conjugates_XZZ {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) :
    cfc Real.sqrt (SMatrix u) * XZZ * cfc Real.sqrt (SMatrix u) =
      (Real.sqrt (u * (1 - u)) / 4) • XZZ := by
  have hproduct : Real.sqrt (u / 4) * Real.sqrt ((1 - u) / 4) =
      Real.sqrt (u * (1 - u)) / 4 := by
    rw [← Real.sqrt_mul (show 0 ≤ u / 4 by positivity),
      show u / 4 * ((1 - u) / 4) = (u * (1 - u)) * ((1 / 4 : ℝ) ^ 2) by ring,
      Real.sqrt_mul (mul_nonneg hu.le (by linarith)),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)] <;> ring
  have hproduct' : Real.sqrt ((1 - u) / 4) * Real.sqrt (u / 4) =
      Real.sqrt (u * (1 - u)) / 4 := by rw [mul_comm, hproduct]
  have hroot : Real.sqrt u * Real.sqrt (1 - u) = Real.sqrt (u * (1 - u)) :=
    (Real.sqrt_mul hu.le _).symm
  have hroot' : Real.sqrt (1 - u) * Real.sqrt u = Real.sqrt (u * (1 - u)) := by
    rw [mul_comm, hroot]
  simp only [SMatrix_eq_diagonal, cfc_diagonal]
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul (K := ℂ),
    mul_right_comm, ← Complex.ofReal_mul]
  rcases i with ⟨⟨a, b⟩, c⟩
  rcases j with ⟨⟨a', b'⟩, c'⟩
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;> fin_cases c <;> fin_cases c' <;>
    norm_num [referenceDiagonal, XZZ, pauliMatrix, qubitX, qubitZ, kronecker_apply,
      hproduct, hproduct']
  all_goals
    rw [div_mul_div_comm, ← Complex.ofReal_mul]
    first | rw [hroot] | rw [hroot']
    norm_num

/-- Whitening the actual unsmoothed density gives the identity plus the Pauli string. -/
theorem RMatrix_zero_whitening {u : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) :
    cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u) * RMatrix u 0 *
      cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u) = 1 + XZZ := by
  let D := cfc Real.sqrt (SMatrix u)
  let T := cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u)
  have hDT : D * T = 1 := reference_sqrt_mul_inv hu hhalf
  have hTD : T * D = 1 :=
    (cfc_commute_cfc Real.sqrt (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u)).eq.symm.trans hDT
  have hR : RMatrix u 0 = D * (1 + XZZ) * D := by
    rw [mul_add, mul_one, add_mul]
    change RMatrix u 0 = cfc Real.sqrt (SMatrix u) * cfc Real.sqrt (SMatrix u) +
      cfc Real.sqrt (SMatrix u) * XZZ * cfc Real.sqrt (SMatrix u)
    rw [reference_sqrt_sq hu hhalf, reference_sqrt_conjugates_XZZ hu hhalf]
    simp only [RMatrix, amplitude, sub_zero, one_mul, SMatrix, familyMatrix, zero_div,
      zero_smul, add_zero]
  change T * RMatrix u 0 * T = _
  rw [hR, ← mul_assoc T (D * (1 + XZZ)) D, ← mul_assoc T D (1 + XZZ), hTD, one_mul,
    mul_assoc (1 + XZZ) D T, hDT, mul_one]

private theorem XZZ_diag_zero (i : Triple) : XZZ i i = 0 := by
  rcases i with ⟨⟨a, b⟩, c⟩
  fin_cases a <;> simp [XZZ, pauliMatrix, qubitX, kronecker_apply]

private theorem trace_reference_mul_whitenedProjection (u : ℝ) :
    (SMatrix u * whitenedProjection).trace = (1 / 2 : ℂ) := by
  have hzero : (SMatrix u * XZZ).trace = 0 := by
    rw [SMatrix_eq_diagonal]
    simp only [Matrix.trace, Matrix.diag, diagonal_mul, XZZ_diag_zero, mul_zero,
      Finset.sum_const_zero]
  have htr : (SMatrix u).trace = 1 := familyMatrix_trace u 0
  rw [whitenedProjection, Matrix.mul_smul, mul_add, mul_one, trace_smul, trace_add, htr, hzero,
    add_zero]
  norm_num [RCLike.real_smul_eq_coe_mul (K := ℂ)]

/-- For every 0 < t ≤ 1, the unsmoothed forward witness has geodesic
relative entropy log 2 with respect to its faithful reference. -/
theorem geodesicRelativeEntropy_RMatrix_zero {u t : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2)
    (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    geodesicRelativeEntropy t (RMatrix u 0) (SMatrix u) = Real.log 2 := by
  obtain ⟨hH, hHH⟩ := endpoint_involution hu hhalf
  obtain ⟨hP, hPP⟩ := half_one_add_projection hH hHH
  obtain ⟨hQ, hQQ⟩ := half_one_add_projection xzz_hermitian xzz_mul_xzz
  have hwhite : cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u) * RMatrix u 0 *
      cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u) = (2 : ℝ) • whitenedProjection := by
    rw [RMatrix_zero_whitening hu hhalf, whitenedProjection, smul_smul] <;> norm_num
  rw [geodesicRelativeEntropy_of_whitened_projection (RMatrix u 0) (SMatrix u)
    (endpointProjection u) whitenedProjection (by norm_num : (0 : ℝ) < 1 / 4)
    ht₀ ht₁ hP hPP hQ hQQ (RMatrix_zero_eq_projection u)
    (reference_sqrt_sq hu hhalf) (reference_sqrt_mul_inv hu hhalf) hwhite,
    trace_reference_mul_whitenedProjection, show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num]
  ring

end

end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicBoundary
