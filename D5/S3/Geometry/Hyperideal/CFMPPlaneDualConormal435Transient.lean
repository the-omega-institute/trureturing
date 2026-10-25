import D5.S3.Geometry.Hyperideal.CFMPPlaneEdgeCofactor435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualTriangleNormal435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPLorentzLiftSurface435Transient CFMPNativePullbackMetric435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPActualTriangleNormal435Transient

namespace CFMPPlaneDualConormal435Transient

def basisPoint (V0 b c : W) (x : Fin 3 → ℝ) : W :=
  x 0 • V0+x 1 • b+x 2 • c

def dualRaw (V0 b c : W) (e : Fin 3) : W :=
  basisPoint V0 b c ((gram (pairingEntries V0 b c))⁻¹ *ᵥ normalCovector e)

theorem basis_pairing (V0 b c : W) (x y : Fin 3 → ℝ) :
    lorentz (basisPoint V0 b c x) (basisPoint V0 b c y) =
      dotProduct x ((gram (pairingEntries V0 b c)).mulVec y) := by
  simp [basisPoint,gram,pairingEntries,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,lorentz,Fin.sum_univ_four,smul_eq_mul]
  <;> ring

theorem dual_pairing (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) (x : Fin 3 → ℝ) :
    lorentz (basisPoint V0 b c x) (dualRaw V0 b c e) =
      dotProduct x (normalCovector e) := by
  unfold dualRaw
  rw [basis_pairing,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG),Matrix.one_mulVec]

theorem dual_norm (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) :
    lorentz (dualRaw V0 b c e) (dualRaw V0 b c e) =
      normalNumerator (pairingEntries V0 b c) e /
        (gram (pairingEntries V0 b c)).det := by
  change lorentz (basisPoint V0 b c
    ((gram (pairingEntries V0 b c))⁻¹ *ᵥ normalCovector e))
    (dualRaw V0 b c e) = _
  rw [dual_pairing V0 b c hG,dotProduct_comm,Matrix.inv_def,Ring.inverse_eq_inv,
    Matrix.smul_mulVec,dotProduct_smul]
  rw [← normalNumerator_eq_adjugate]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem dual_ne_zero (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) :
    dualRaw V0 b c e ≠ 0 := by
  intro hz
  have h := dual_pairing V0 b c hG e (normalCovector e)
  rw [hz] at h
  fin_cases e <;> norm_num [normalCovector,dotProduct,Fin.sum_univ_three,lorentz] at h

theorem dual_affine_readout (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) (q : ℝ × ℝ) :
    lorentz (V0+q.1 • b+q.2 • c) (dualRaw V0 b c e) =
      ![-q.1,-q.2,-1+q.1+q.2] e := by
  have h := dual_pairing V0 b c hG e ![1,q.1,q.2]
  fin_cases e <;>
    simpa [basisPoint,normalCovector,dotProduct,Fin.sum_univ_three] using h

theorem dual_edge_readout (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) (r : ℝ) :
    lorentz (rawPoint V0 b c e r) (dualRaw V0 b c e) = 0 := by
  unfold rawPoint
  rw [dual_affine_readout V0 b c hG]
  fin_cases e <;> simp [edgePoint] <;> ring

theorem dual_spacelike (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) (r : ℝ)
    (hq : 0 < radius (rawPoint V0 b c e r)) :
    0 < lorentz (dualRaw V0 b c e) (dualRaw V0 b c e) := by
  exact spacelike_of_timelike_orthogonal _ _ (neg_pos.mp hq)
    (dual_edge_readout V0 b c hG e r) (dual_ne_zero V0 b c hG e)

theorem dual_body_nonpositive (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) (q : ℝ × ℝ)
    (hq0 : 0 ≤ q.1) (hq1 : 0 ≤ q.2) (hqs : q.1+q.2 ≤ 1) :
    lorentz (V0+q.1 • b+q.2 • c) (dualRaw V0 b c e) ≤ 0 := by
  rw [dual_affine_readout V0 b c hG]
  fin_cases e <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  all_goals linarith

theorem native_edge_speed (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det < 0) (e : Fin 3) (r : ℝ)
    (hq : 0 < radius (rawPoint V0 b c e r))
    (hd : delta (rawPoint V0 b c e r) ≠ 0) :
    let Y := rawPoint V0 b c e r
    let D := rawTangent b c e
    Real.sqrt (dotProduct ((nativeMatrix Y).mulVec D) ((nativeMatrix Y).mulVec D) /
        (nativeMap Y 2)^2) =
      Real.sqrt (-(gram (pairingEntries V0 b c)).det) *
        Real.sqrt (lorentz (dualRaw V0 b c e) (dualRaw V0 b c e)) / radius Y := by
  dsimp only
  rw [native_edge_squared_speed V0 b c e r hq hd,
    dual_norm V0 b c hG.ne]
  exact scalar_edge_speed _ _ _ _ (Real.sqrt_nonneg _) hq hG.ne
    (Real.sq_sqrt (neg_pos.mpr hG).le)
    (by rw [← dual_norm V0 b c hG.ne]; exact (dual_spacelike V0 b c hG.ne e r hq).le)

def dualUnit (V0 b c : W) (e : Fin 3) : W :=
  (Real.sqrt (lorentz (dualRaw V0 b c e) (dualRaw V0 b c e)))⁻¹ • dualRaw V0 b c e

theorem pairing_dualUnit (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) (a : Fin 3 → ℝ) :
    lorentz (basisPoint V0 b c a) (dualUnit V0 b c e) =
      dotProduct a (normalCovector e) /
        Real.sqrt (lorentz (dualRaw V0 b c e) (dualRaw V0 b c e)) := by
  have he (A N : W) (t : ℝ) : lorentz A (t • N) = t*lorentz A N := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    <;> ring
  unfold dualUnit
  rw [he,dual_pairing V0 b c hG]
  simp [div_eq_mul_inv,mul_comm]

theorem dual_unit_norm (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) (e : Fin 3) (r : ℝ)
    (hq : 0 < radius (rawPoint V0 b c e r)) :
    lorentz (dualUnit V0 b c e) (dualUnit V0 b c e) = 1 := by
  have hn := dual_spacelike V0 b c hG e r hq
  have he (t : ℝ) (N : W) : lorentz (t • N) (t • N) = t^2*lorentz N N := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    <;> ring
  unfold dualUnit
  rw [he,inv_pow,Real.sq_sqrt hn.le]
  exact inv_mul_cancel₀ hn.ne'

theorem native_edge_curve_derivative (V0 b c : W) (e : Fin 3) (r : ℝ)
    (hq : 0 < radius (rawPoint V0 b c e r))
    (hd : delta (rawPoint V0 b c e r) ≠ 0) :
    HasDerivAt (fun t : ℝ => nativeMap (rawPoint V0 b c e t))
      ((nativeMatrix (rawPoint V0 b c e r)).mulVec (rawTangent b c e)) r := by
  have hraw : HasDerivAt (rawPoint V0 b c e) (rawTangent b c e) r := by
    fin_cases e
    · simpa [rawPoint,edgePoint,rawTangent] using
        ((hasDerivAt_const r V0).add ((hasDerivAt_id r).smul_const c))
    · simpa [rawPoint,edgePoint,rawTangent] using
        ((hasDerivAt_const r V0).add ((hasDerivAt_id r).smul_const b))
    · simpa [rawPoint,edgePoint,rawTangent,sub_eq_add_neg,add_comm] using
        (((hasDerivAt_const r V0).add
          (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).smul_const b)).add
          ((hasDerivAt_id r).smul_const c))
  exact (nativeMap_hasFDerivAt _ hq hd).comp_hasDerivAt r hraw

def referenceFlux (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ) (e : Fin 3) (r : ℝ) : ℝ :=
  ![-CFMPPlaneMomentDivergence435Transient.fluxX g a C (0,r),
    -CFMPPlaneMomentDivergence435Transient.fluxY g a C (r,0),
    CFMPPlaneMomentDivergence435Transient.fluxX g a C (1-r,r)+
      CFMPPlaneMomentDivergence435Transient.fluxY g a C (1-r,r)] e

theorem reference_flux_readout (g : Fin 6 → ℝ) (a : Fin 3 → ℝ)
    (C : ℝ) (e : Fin 3) (r : ℝ) :
    referenceFlux g a C e r =
      C*dotProduct a (normalCovector e)/
        CFMPPlaneMomentDivergence435Transient.Q g (edgePoint e r) := by
  fin_cases e <;>
    simp [referenceFlux,CFMPPlaneMomentDivergence435Transient.fluxX,
      CFMPPlaneMomentDivergence435Transient.fluxY,edgePoint,normalCovector,
      dotProduct,Fin.sum_univ_three] <;> ring

theorem native_edge_flux (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det < 0) (a : Fin 3 → ℝ) (e : Fin 3) (r : ℝ)
    (hq : 0 < radius (rawPoint V0 b c e r))
    (hd : delta (rawPoint V0 b c e r) ≠ 0) :
    let Y := rawPoint V0 b c e r
    let D := rawTangent b c e
    referenceFlux (pairingEntries V0 b c) a
        (Real.sqrt (-(gram (pairingEntries V0 b c)).det)) e r =
      lorentz (basisPoint V0 b c a) (dualUnit V0 b c e) *
        Real.sqrt (dotProduct ((nativeMatrix Y).mulVec D) ((nativeMatrix Y).mulVec D) /
          (nativeMap Y 2)^2) := by
  dsimp only
  rw [reference_flux_readout,pairing_dualUnit V0 b c hG.ne,
    native_edge_speed V0 b c hG e r hq hd]
  rw [← (raw_edge_pairings V0 b c e r).1]
  exact (scalar_edge_flux _ _ _ _ hq.ne'
    (dual_spacelike V0 b c hG.ne e r hq)).symm

end CFMPPlaneDualConormal435Transient
