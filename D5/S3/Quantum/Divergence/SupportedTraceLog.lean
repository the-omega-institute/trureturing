/- GID: D5/S3/Quantum/Divergence/SupportedTraceLog
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/SupportedTraceLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite joint convexity of supported PSD trace-log pairings. -/

import D5.S3.Quantum.Divergence.FannesRootFidelityHolevo
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.LogExp

/-! Finite joint convexity for supported trace-log pairings with arbitrary masses. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.SupportedTraceLog

open FannesRootFidelityHolevo (supported_of_le)
open private matrix_log_sum relativeEntropy from D5.S3.Quantum.Divergence.FannesRootFidelityHolevo

section Support

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every vector in the reference kernel lies in the numerator kernel. -/
private abbrev HasSupportIn (S T : Matrix n n ℂ) : Prop :=
  ∀ x, T *ᵥ x = 0 → S *ᵥ x = 0

private def supportProjection (T : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun t : ℝ => if t = 0 then (0 : ℝ) else 1) T

private theorem mul_own_supportProjection {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    T * supportProjection T = T := by
  let e : ℝ → ℝ := fun t => if t = 0 then 0 else 1
  have h := cfc_mul (fun t : ℝ => t) e T continuous_id.continuousOn
    (T.finite_real_spectrum.continuousOn _)
  rw [cfc_id' ℝ T hT.isSelfAdjoint] at h
  change T * cfc e T = T
  rw [← h]
  calc
    cfc (fun t => t * e t) T = cfc (fun t : ℝ => t) T := by
      apply cfc_congr
      intro t _
      by_cases ht : t = 0 <;> simp [e, ht]
    _ = T := cfc_id' ℝ T hT.isSelfAdjoint

private theorem mul_supportProjection {S T : Matrix n n ℂ} (hT : T.IsHermitian)
    (hST : HasSupportIn S T) : S * supportProjection T = S := by
  let K : Matrix n n ℂ := 1 - supportProjection T
  have hTK : T * K = 0 := by
    simp only [K, Matrix.mul_sub, Matrix.mul_one, mul_own_supportProjection hT, sub_self]
  have hSK : S * K = 0 := by
    apply Matrix.ext
    intro i j
    have hz := hST (K *ᵥ Pi.single j (1 : ℂ)) (by
      rw [Matrix.mulVec_mulVec, hTK, Matrix.zero_mulVec])
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hz
    simpa only [Matrix.col_apply, Matrix.zero_apply, Pi.zero_apply] using congrFun hz i
  have hsub : S - S * supportProjection T = 0 := by
    simpa only [K, Matrix.mul_sub, Matrix.mul_one] using hSK
  exact (sub_eq_zero.mp hsub).symm

omit [DecidableEq n] in
private theorem HasSupportIn.smul {S T : Matrix n n ℂ} (hST : HasSupportIn S T)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) : HasSupportIn (a • S) (b • T) := by
  intro x hx
  rw [Matrix.smul_mulVec] at hx ⊢
  rw [hST x ((smul_eq_zero.mp hx).resolve_left hb), smul_zero]

omit [DecidableEq n] in
private theorem HasSupportIn.smul_same {S T : Matrix n n ℂ}
    (hST : HasSupportIn S T) (a : ℝ) : HasSupportIn (a • S) (a • T) := by
  rcases eq_or_ne a 0 with rfl | ha
  · intro x _
    simp
  · exact hST.smul a ha

omit [DecidableEq n] in
/-- Finite PSD sums preserve pointwise support inclusion. -/
private theorem hasSupportIn_sum {ι : Type*} [Fintype ι] (S T : ι → Matrix n n ℂ)
    (hT : ∀ i, (T i).PosSemidef) (hST : ∀ i, HasSupportIn (S i) (T i)) :
    HasSupportIn (∑ i, S i) (∑ i, T i) := by
  classical
  intro x hx
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i hi
  have hle : T i ≤ ∑ j, T j :=
    Finset.single_le_sum (fun j _ => (hT j).nonneg) hi
  exact hST i x (supported_of_le (hT i) hle x hx)

private theorem traceLog_scale {S T : Matrix n n ℂ}
    (hS : S.IsHermitian) (hT : T.IsHermitian) (hST : HasSupportIn S T)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    relativeEntropy (a • S) (b • T) =
      a * relativeEntropy S T + (a * (Real.log a - Real.log b)) * S.trace.re := by
  have hlog :
      S * (CFC.log (a • S) - CFC.log (b • T)) =
        S * (CFC.log S - CFC.log T) + (Real.log a - Real.log b) • S := by
    unfold CFC.log
    rw [hS.log_smul_of_ne_zero ha, hT.log_smul_of_ne_zero hb]
    change S * (Real.log a • supportProjection S + cfc Real.log S -
      (Real.log b • supportProjection T + cfc Real.log T)) = _
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
      mul_own_supportProjection hS, mul_supportProjection hT hST, sub_smul]
    abel
  simp only [relativeEntropy, Matrix.smul_mul, hlog, Matrix.trace_smul,
    Matrix.trace_add, Complex.smul_re, Complex.add_re, smul_eq_mul]
  ring

private theorem traceLog_scale_same {S T : Matrix n n ℂ}
    (hS : S.IsHermitian) (hT : T.IsHermitian) (hST : HasSupportIn S T) (w : ℝ) :
    relativeEntropy (w • S) (w • T) = w * relativeEntropy S T := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [relativeEntropy]
  · rw [traceLog_scale hS hT hST hw hw, sub_self, mul_zero, zero_mul, add_zero]

end Support

section JointConvexity

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype ι] [Nonempty ι]

omit [DecidableEq n] [Nonempty n] [Nonempty ι] in
private theorem trace_sum_inverse_smul (S : ι → Matrix n n ℂ) {m : ℝ}
    (hm : m ≠ 0) (ht : (∑ i, S i).trace = (m : ℂ)) :
    (∑ i, (m⁻¹ • S i).trace) = 1 := by
  rw [← Matrix.trace_sum, ← Finset.smul_sum, Matrix.trace_smul, ht, Complex.real_smul,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hm, Complex.ofReal_one]

private theorem traceLog_log_sum_of_trace (S T : ι → Matrix n n ℂ)
    (hS : ∀ i, (S i).PosSemidef) (hT : ∀ i, (T i).PosSemidef)
    (hST : ∀ i, HasSupportIn (S i) (T i))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hsumS : (∑ i, S i).trace = (s : ℂ)) (hsumT : (∑ i, T i).trace = (t : ℂ)) :
    relativeEntropy (∑ i, S i) (∑ i, T i) ≤ ∑ i, relativeEntropy (S i) (T i) := by
  classical
  have hs' : s⁻¹ ≠ 0 := (inv_pos.mpr hs).ne'
  have ht' : t⁻¹ ≠ 0 := (inv_pos.mpr ht).ne'
  have hposS : (∑ i, S i).PosSemidef := Matrix.posSemidef_sum _ fun i _ => hS i
  have hposT : (∑ i, T i).PosSemidef := Matrix.posSemidef_sum _ fun i _ => hT i
  have h := matrix_log_sum (fun i => s⁻¹ • S i) (fun i => t⁻¹ • T i)
    (fun i => (smul_nonneg (inv_nonneg.mpr hs.le) (hS i).nonneg).posSemidef)
    (fun i => (smul_nonneg (inv_nonneg.mpr ht.le) (hT i).nonneg).posSemidef)
    (trace_sum_inverse_smul S hs.ne' hsumS) (trace_sum_inverse_smul T ht.ne' hsumT)
    (fun i => (hST i).smul s⁻¹ ht')
  have hscaled :
      relativeEntropy (s⁻¹ • (∑ i, S i)) (t⁻¹ • (∑ i, T i)) ≤
        ∑ i, relativeEntropy (s⁻¹ • S i) (t⁻¹ • T i) := by
    simpa only [← Finset.smul_sum] using h
  let correction := s⁻¹ * (Real.log s⁻¹ - Real.log t⁻¹)
  have hpoint (i : ι) :
      relativeEntropy (s⁻¹ • S i) (t⁻¹ • T i) =
        s⁻¹ * relativeEntropy (S i) (T i) + correction * (S i).trace.re :=
    traceLog_scale (hS i).isHermitian (hT i).isHermitian (hST i) hs' ht'
  have hblocks :
      (∑ i, relativeEntropy (s⁻¹ • S i) (t⁻¹ • T i)) =
        s⁻¹ * (∑ i, relativeEntropy (S i) (T i)) + correction * (∑ i, S i).trace.re := by
    simp only [hpoint, Matrix.trace_sum, Complex.re_sum, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hblocks, traceLog_scale hposS.isHermitian hposT.isHermitian
    (hasSupportIn_sum S T hT hST) hs' ht'] at hscaled
  change s⁻¹ * relativeEntropy (∑ i, S i) (∑ i, T i) + correction * (∑ i, S i).trace.re ≤
    s⁻¹ * (∑ i, relativeEntropy (S i) (T i)) + correction * (∑ i, S i).trace.re at hscaled
  apply le_of_not_gt
  intro hgt
  exact (not_lt_of_ge hscaled)
    (add_lt_add_left (mul_lt_mul_of_pos_left hgt (inv_pos.mpr hs)) _)

private theorem traceLog_log_sum (S T : ι → Matrix n n ℂ)
    (hS : ∀ i, (S i).PosSemidef) (hT : ∀ i, (T i).PosSemidef)
    (hST : ∀ i, HasSupportIn (S i) (T i)) :
    relativeEntropy (∑ i, S i) (∑ i, T i) ≤ ∑ i, relativeEntropy (S i) (T i) := by
  classical
  by_cases hSzero : (∑ i, S i) = 0
  · have hzero (i : ι) : S i = 0 := by
      have hle : S i ≤ ∑ j, S j :=
        Finset.single_le_sum (fun j _ => (hS j).nonneg) (Finset.mem_univ i)
      rw [hSzero] at hle
      exact le_antisymm hle (hS i).nonneg
    simp [hzero, relativeEntropy]
  · have hTzero : (∑ i, T i) ≠ 0 := by
      intro hzero
      apply hSzero
      apply Matrix.ext
      intro i j
      have hz := hasSupportIn_sum S T hT hST (Pi.single j (1 : ℂ)) (by
        rw [hzero, Matrix.zero_mulVec])
      rw [Matrix.mulVec_single_one] at hz
      simpa only [Matrix.col_apply, Matrix.zero_apply, Pi.zero_apply] using congrFun hz i
    have htrace {A : Matrix n n ℂ} (hA : A.PosSemidef) (hne : A ≠ 0) :
        0 < A.trace.re ∧ A.trace = (A.trace.re : ℂ) := by
      obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hA.trace_nonneg
      have hcast : A.trace = (A.trace.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa only [Complex.ofReal_im] using him.symm
      have hne' : A.trace.re ≠ 0 := by
        intro h
        apply hne
        apply hA.trace_eq_zero_iff.mp
        simpa only [h, Complex.ofReal_zero] using hcast
      exact ⟨lt_of_le_of_ne hre (Ne.symm hne'), hcast⟩
    obtain ⟨hs, hsTr⟩ := htrace (Matrix.posSemidef_sum _ fun i _ => hS i) hSzero
    obtain ⟨ht, htTr⟩ := htrace (Matrix.posSemidef_sum _ fun i _ => hT i) hTzero
    exact traceLog_log_sum_of_trace S T hS hT hST hs ht hsTr htTr

/-- Supported trace-log is jointly convex over finite families of PSD pairs.
The homogeneous form allows any nonnegative common weights. -/
theorem traceLog_jointConvex (w : ι → ℝ) (S T : ι → Matrix n n ℂ)
    (hw : ∀ i, 0 ≤ w i)
    (hS : ∀ i, (S i).PosSemidef) (hT : ∀ i, (T i).PosSemidef)
    (hST : ∀ i x, T i *ᵥ x = 0 → S i *ᵥ x = 0) :
    let A := ∑ i, w i • S i
    let C := ∑ i, w i • T i
    (A * (CFC.log A - CFC.log C)).trace.re ≤
      ∑ i, w i * (S i * (CFC.log (S i) - CFC.log (T i))).trace.re := by
  have h := traceLog_log_sum (fun i => w i • S i) (fun i => w i • T i)
    (fun i => (smul_nonneg (hw i) (hS i).nonneg).posSemidef)
    (fun i => (smul_nonneg (hw i) (hT i).nonneg).posSemidef)
    (fun i => HasSupportIn.smul_same (hST i) (w i))
  have hpoint (i : ι) := traceLog_scale_same (hS i).isHermitian (hT i).isHermitian (hST i) (w i)
  simp only [hpoint] at h
  simpa only [relativeEntropy] using h

end JointConvexity

end D5.S3.Quantum.Divergence.SupportedTraceLog
