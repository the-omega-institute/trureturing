/- GID: D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiNullReferencePenalty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp spectral cost of a positive trace-normalized reference increment. -/

import D5.S3.Divergence.AudenaertBinaryHolevoBound

/-! A positive trace-one reference increment has a sharp logarithmic cost
controlled by the positive floor. The proof compares the trace of the
logarithmic derivative to the scalar derivative along the same affine path. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace
open D5.S3.Divergence.AudenaertBinaryHolevoBound (log_hasDerivAt_affine_of_lower_bound)

namespace D5.S3.Quantum.Divergence.UmegakiNullReferencePenalty

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem density_le_one {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) : ρ ≤ 1 := by
  have hsum : ∑ i, hρ.isHermitian.eigenvalues i = 1 := by
    simpa using congrArg Complex.re (hρ.isHermitian.trace_eq_sum_eigenvalues.symm.trans htrace)
  rw [← map_one (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ))]
  apply (le_algebraMap_iff_spectrum_le hρ.isHermitian.isSelfAdjoint).mpr
  rw [hρ.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hρ.eigenvalues_nonneg j) (Finset.mem_univ i)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem trace_log_path_hasDerivAt {n : ℕ}
    (A C ρ : Matrix (Fin n) (Fin n) ℂ) (lam t : ℝ) (hlam : 0 < lam)
    (hC : lam • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ C)
    (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => (A * CFC.log (C + s • ρ)).trace.re)
      (A * logDeriv (C + t • ρ) ρ).trace.re t := by
  have hf : ∀ s ∈ Set.Ioi (-(lam / 2)), (lam / 2) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤
      C + s • ρ := by
    intro s hs
    have hρlow : (-(lam / 2)) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ s • ρ := by
      calc
        _ = -((lam / 2) • (1 : Matrix (Fin n) (Fin n) ℂ)) := neg_smul _ _
        _ ≤ -((lam / 2) • ρ) := neg_le_neg (smul_le_smul_of_nonneg_left hρone (by positivity))
        _ = (-(lam / 2)) • ρ := (neg_smul _ _).symm
        _ ≤ s • ρ := smul_le_smul_of_nonneg_right hs.le hρ
    convert add_le_add hC hρlow using 1
    rw [← add_smul]
    congr 1
    ring
  have hd := log_hasDerivAt_affine_of_lower_bound C ρ t (lam / 2) (by positivity) _
    (Ioi_mem_nhds (show -(lam / 2) < t by linarith)) hf
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp ((Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap.comp
      (mulLeftLinearMap (Fin n) ℝ A).toContinuousLinearMap)
  exact L.hasFDerivAt.comp_hasDerivAt t hd

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_posSemidef {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.PosDef) (hX : X.PosSemidef) : (logDeriv M X).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  apply integral_nonneg_of_ae
  filter_upwards [] with s
  let R : Matrix (Fin n) (Fin n) ℂ := (M + s • 1)⁻¹
  change 0 ≤ R * X * R
  have hR : R.IsHermitian :=
    (hM.isHermitian.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all s))).inv
  have h : 0 ≤ R * X * Rᴴ := (hX.mul_mul_conjTranspose_same R).nonneg
  rwa [hR.eq] at h

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- A trace-one positive increment has a uniform logarithmic cost under the
Löwner bounds on the weight and reference matrices. -/
theorem log_increment_ge {n : ℕ} (A C ρ : Matrix (Fin n) (Fin n) ℂ) (u lam e : ℝ)
    (hu : 0 < u) (hlam : 0 < lam) (he : 0 ≤ e) (hA : u • C ≤ A)
    (hC : lam • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ C)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    u * lam * Real.log (1 + e / lam) ≤ (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re := by
  let M (t : ℝ) := C + t • ρ
  let F (t : ℝ) := (A * CFC.log (M t)).trace.re - u * lam * Real.log (lam + t)
  have hρone := density_le_one hρ htrace
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F
      ((A * logDeriv (M t) ρ).trace.re - u * lam / (lam + t)) t := by
    have hlog := ((hasDerivAt_id t).const_add lam).log (by dsimp; positivity)
    convert! (trace_log_path_hasDerivAt A C ρ lam t hlam hC hρ.nonneg hρone ht).sub
      (hlog.const_mul (u * lam)) using 1
    simp only [M, div_eq_mul_inv, one_mul, id_eq]
  have hnonneg (t : ℝ) (ht : 0 ≤ t) :
      u * lam / (lam + t) ≤ (A * logDeriv (M t) ρ).trace.re := by
    have hMt : lam • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ M t :=
      hC.trans (le_add_of_nonneg_right (smul_nonneg ht hρ.nonneg))
    have hM : (M t).PosDef :=
      ((IsStrictlyPositive.smul hlam isStrictlyPositive_one).of_le hMt).posDef
    have hρC : ρ ≤ lam⁻¹ • C := hρone.trans (by
      simpa [smul_smul, hlam.ne'] using smul_le_smul_of_nonneg_left hC (inv_nonneg.mpr hlam.le))
    have hMC : M t ≤ (1 + t / lam) • C := by
      calc
        M t ≤ C + t • (lam⁻¹ • C) := add_le_add le_rfl (smul_le_smul_of_nonneg_left hρC ht)
        _ = (1 + t / lam) • C := by rw [add_smul, one_smul, smul_smul, div_eq_mul_inv]
    let k := u * lam / (lam + t)
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hscale : k * (1 + t / lam) = u := by
      dsimp [k]
      field_simp [hlam.ne', (add_pos_of_pos_of_nonneg hlam ht).ne']
    have horder : k • M t ≤ A := by
      apply le_trans (smul_le_smul_of_nonneg_left hMC hk)
      simpa only [smul_smul, hscale] using hA
    have hp := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp horder)
      (logDeriv_posSemidef (M t) ρ hM hρ)
    change 0 ≤ ((A - k • M t) * logDeriv (M t) ρ).trace.re at hp
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul,
      Matrix.trace_smul, trace_mul_logDeriv _ _ hM hρ.isHermitian, htrace] at hp
    simpa only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one, sub_nonneg] using hp
  have hmono : MonotoneOn F (Set.Icc 0 e) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 e)
    · exact fun t ht => (hd t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ht.1.le).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact sub_nonneg.mpr (hnonneg t ht.1.le)
  have h := hmono ⟨le_rfl, he⟩ ⟨he, le_rfl⟩ he
  simp only [F, M, zero_smul, add_zero] at h
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, show 1 + e / lam = (lam + e) / lam by
    field_simp, Real.log_div (add_pos_of_pos_of_nonneg hlam he).ne' hlam.ne', mul_sub]
  linarith

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- The pure state of a unit eigenvector at the floor attains the bound
when the weight is exactly `u • C`. -/
theorem log_increment_eq_of_eigenvector {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (u lam e : ℝ) (hlam : 0 < lam) (he : 0 ≤ e)
    (hC : lam • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ C)
    (hv : star v ⬝ᵥ v = 1) (hev : C *ᵥ v = (lam : ℂ) • v) :
    let P := vecMulVec v (star v)
    P.PosSemidef ∧ P.trace = 1 ∧
      ((u • C) * (CFC.log (C + e • P) - CFC.log C)).trace.re =
        u * lam * Real.log (1 + e / lam) := by
  let P := vecMulVec v (star v)
  have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have htrace : P.trace = 1 := by
    change (vecMulVec v (star v)).trace = 1
    rw [Matrix.trace_vecMulVec, dotProduct_comm, hv]
  refine ⟨hP, htrace, ?_⟩
  have hPP : P * P = P := by simp [P, vecMulVec_mul_vecMulVec, hv]
  have hCP : C * P = lam • P := by
    change C * vecMulVec v (star v) = _
    rw [mul_vecMulVec, hev, ← smul_vecMulVec]
    rfl
  let M (t : ℝ) := C + t • P
  let F (t : ℝ) := ((u • C) * CFC.log (M t)).trace.re - u * lam * Real.log (lam + t)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F 0 t := by
    let k := u * lam / (lam + t)
    let B := u • C - k • M t
    have hlamt := add_pos_of_pos_of_nonneg hlam ht
    have hMt : (M t).PosDef := ((IsStrictlyPositive.smul hlam isStrictlyPositive_one).of_le
      (hC.trans (le_add_of_nonneg_right (smul_nonneg ht hP.nonneg)))).posDef
    have hMP : M t * P = (lam + t) • P := by
      change (C + t • P) * P = _
      rw [Matrix.add_mul, Matrix.smul_mul, hCP, hPP, add_smul]
    have hBP : B * P = 0 := by
      have hk : k * (lam + t) = u * lam := div_mul_cancel₀ _ hlamt.ne'
      simp [B, Matrix.sub_mul, hMP, hCP, smul_smul, hk]
    let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      (mulLeftLinearMap (Fin n) ℝ B).toContinuousLinearMap
    have hBL : B * logDeriv (M t) P = 0 := by
      unfold D5.S3.Divergence.LogDerivTrace.logDeriv
      change L (∫ s in Set.Ioi (0 : ℝ), (M t + s • 1)⁻¹ * P * (M t + s • 1)⁻¹) = 0
      rw [← L.integral_comp_comm (logDeriv_integrable _ _ hMt)]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      let Q := M t + s • (1 : Matrix (Fin n) (Fin n) ℂ)
      have hQ : Q.PosDef := hMt.add_posSemidef
        (Matrix.nonneg_iff_posSemidef.mp (smul_nonneg hs.le zero_le_one))
      have hQP : Q * P = (lam + t + s) • P := by
        simp [Q, Matrix.add_mul, hMP, add_smul]
      have hRP : Q⁻¹ * P = (lam + t + s)⁻¹ • P := by
        have h := congrArg (fun X => Q⁻¹ * X) hQP
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det Q).mp
          hQ.isUnit), Matrix.one_mul, Matrix.mul_smul] at h
        calc
          Q⁻¹ * P = (lam + t + s)⁻¹ • ((lam + t + s) • (Q⁻¹ * P)) := by
            rw [smul_smul, inv_mul_cancel₀ (add_pos hlamt hs).ne', one_smul]
          _ = _ := by rw [← h]
      change B * (Q⁻¹ * P * Q⁻¹) = 0
      rw [hRP, ← Matrix.mul_assoc, Matrix.mul_smul, hBP, smul_zero, Matrix.zero_mul]
    have hpair : ((u • C) * logDeriv (C + t • P) P).trace.re = k := by
      change ((u • C) * logDeriv (M t) P).trace.re = k
      change ((u • C - k • M t) * logDeriv (M t) P) = 0 at hBL
      rw [Matrix.sub_mul, sub_eq_zero] at hBL
      rw [hBL, Matrix.smul_mul, Matrix.trace_smul,
        trace_mul_logDeriv _ _ hMt hP.isHermitian, htrace]
      simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
    have hlog := ((hasDerivAt_id t).const_add lam).log hlamt.ne'
    have hdiff := (trace_log_path_hasDerivAt (u • C) C P lam t hlam hC hP.nonneg
      (density_le_one hP htrace) ht).sub (hlog.const_mul (u * lam))
    rw [hpair] at hdiff
    convert! hdiff using 1
    simp only [k, div_eq_mul_inv, one_mul, id_eq, sub_self]
  obtain rfl | he' := he.eq_or_lt
  · simp
  obtain ⟨t, _, ht⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) he'
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => hd s hs.1.le)
  have h := sub_eq_zero.mp ((div_eq_zero_iff.mp ht.symm).resolve_right (by simpa using he'.ne'))
  simp only [F, M, zero_smul, add_zero] at h
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, show 1 + e / lam = (lam + e) / lam by
    field_simp, Real.log_div (add_pos hlam he').ne' hlam.ne', mul_sub]
  linarith

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- A loss at most the sharp value at a positive threshold rules out
any strictly larger Löwner floor when the increment has positive mass. -/
theorem not_floor_of_log_increment_le {n : ℕ}
    (A C ρ : Matrix (Fin n) (Fin n) ℂ) (u threshold lam e : ℝ)
    (hu : 0 < u) (hthreshold : 0 < threshold) (hlt : threshold < lam) (he : 0 < e)
    (hA : u • C ≤ A) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (hloss : (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re ≤
      u * threshold * Real.log (1 + e / threshold)) :
    ¬ lam • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ C := by
  intro hC
  let f (s : ℝ) := s * (Real.log (s + e) - Real.log s)
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt f (Real.log (s + e) - Real.log s + (s / (s + e) - 1)) s := by
    have ha := add_pos hs he
    have h := ((hasDerivAt_id s).add_const e).log ha.ne'
    convert (hasDerivAt_id s).mul (h.sub (Real.hasDerivAt_log hs.ne')) using 1
    · rfl
    · change _ = 1 * (Real.log (s + e) - Real.log s) + s * (1 / (s + e) - s⁻¹)
      field_simp [hs.ne', ha.ne']
  have hmono : StrictMonoOn f (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [isOpen_Ioi.interior_eq] at hs
      have hs' : 0 < s := hs
      have ha := add_pos hs' he
      rw [(hd s hs').deriv]
      have hratio : s / (s + e) < 1 := (div_lt_one ha).mpr (lt_add_of_pos_right s he)
      have hlog := Real.log_lt_sub_one_of_pos (div_pos hs' ha) hratio.ne
      rw [Real.log_div hs'.ne' ha.ne'] at hlog
      linarith
  have hlam := hthreshold.trans hlt
  have hval (s : ℝ) (hs : 0 < s) :
      u * f s = u * s * Real.log (1 + e / s) := by
    rw [show 1 + e / s = (s + e) / s by field_simp,
      Real.log_div (add_pos hs he).ne' hs.ne']
    exact (mul_assoc _ _ _).symm
  have hstrict := mul_lt_mul_of_pos_left (hmono hthreshold hlam hlt) hu
  rw [hval _ hthreshold, hval _ hlam] at hstrict
  exact hstrict.not_ge ((log_increment_ge A C ρ u lam e hu hlam he.le hA hC hρ htrace).trans hloss)

#print axioms log_increment_ge
#print axioms log_increment_eq_of_eigenvector
#print axioms not_floor_of_log_increment_le

end D5.S3.Quantum.Divergence.UmegakiNullReferencePenalty
