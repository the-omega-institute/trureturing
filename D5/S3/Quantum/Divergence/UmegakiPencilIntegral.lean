/- GID: D5/S3/Quantum/Divergence/UmegakiPencilIntegral
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiPencilIntegral
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: The corrected finite Umegaki pairing as a weighted negative-part trace integral. -/

import D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import D5.S3.Resource.LogDet.LogDetInformationSubmodularity

/-!
# The finite Umegaki pencil integral

For a positive semidefinite first endpoint and a positive definite second endpoint,
the real scalar-shift proof completes Frenkel's affine-pencil formula
(arXiv:2208.12194, Theorem 6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory RHLinalg Set
open scoped BigOperators ComplexOrder ENNReal MatrixOrder Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Matrix
open D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
open D5.S3.Resource.LogDet.PathSpectralClassical
open D5.S3.Resource.LogDet.LogDetInformationSubmodularity

namespace D5.S3.Quantum.Divergence.UmegakiPencilIntegral

def shiftKernel (a b r : ℝ) : ℝ :=
  Real.log (b + r) - Real.log (a + r) + (a - b) / (b + r)

private theorem shiftKernel_nonneg {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hr : 0 < r) : 0 ≤ shiftKernel a b r := by
  have hx : 0 < a + r := by positivity
  have hy : 0 < b + r := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne', show (a + r) / (b + r) - 1 =
    (a - b) / (b + r) by field_simp; ring] at h
  unfold shiftKernel
  linarith

theorem integral_shiftKernel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    IntegrableOn (shiftKernel a b) (Ioi 0) ∧
      (∫ r in Ioi (0 : ℝ), shiftKernel a b r) =
        a * Real.log a - a * Real.log b - (a - b) := by
  let F (r : ℝ) := (a + r) * Real.log (a + r) - (a + r) * Real.log (b + r)
  have hF : ContinuousWithinAt F (Ici 0) 0 := by
    have hx : ContinuousAt (fun r : ℝ => a + r) 0 := by fun_prop
    have hy : ContinuousAt (fun r : ℝ => b + r) 0 := by fun_prop
    have hlog : ContinuousAt Real.log (b + (0 : ℝ)) :=
      Real.continuousAt_log (by simpa using hb.ne')
    exact ((Real.continuous_mul_log.continuousAt.comp hx).sub
      (hx.mul (hlog.comp hy))).continuousWithinAt
  have hderiv (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      HasDerivAt F (-shiftKernel a b r) r := by
    have hr0 : 0 < r := hr
    have hx : 0 < a + r := by positivity
    have hy : 0 < b + r := by positivity
    have dx : HasDerivAt (fun s : ℝ => a + s) 1 r := (hasDerivAt_id r).const_add a
    have dy : HasDerivAt (fun s : ℝ => b + s) 1 r := (hasDerivAt_id r).const_add b
    convert (dx.mul (dx.log hx.ne')).sub (dx.mul (dy.log hy.ne')) using 1
    unfold shiftKernel
    field_simp [hx.ne', hy.ne']
    ring
  let q (r : ℝ) := (a + r) / (b + r)
  have hden : Tendsto (fun r : ℝ => b + r) atTop atTop := by
    simpa only [id_eq, add_comm b] using tendsto_atTop_add_const_right atTop b tendsto_id
  have hq : Tendsto q atTop (𝓝 1) := by
    have hinv : Tendsto (fun r : ℝ => (b + r)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    have h := (hinv.const_mul (a - b)).const_add 1
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hy : b + r ≠ 0 := (add_pos hb hr).ne'
    dsimp [q]
    field_simp [hy]
    ring
  have hbounds : ∀ᶠ r in atTop, a - b ≤ F r ∧ F r ≤ (a - b) * q r := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hx : 0 < a + r := by positivity
    have hy : 0 < b + r := by positivity
    have hqr : 0 < q r := div_pos hx hy
    have hFq : F r = (a + r) * Real.log (q r) := by
      simp only [F, q, Real.log_div hx.ne' hy.ne']
      ring
    have hu := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hqr) hx.le
    have hl := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (inv_pos.mpr hqr)) hx.le
    rw [Real.log_inv] at hl
    have hupper : (a + r) * (q r - 1) = (a - b) * q r := by
      dsimp [q]
      field_simp [hy.ne']
      ring
    have hlower : (a + r) * ((q r)⁻¹ - 1) = -(a - b) := by
      dsimp [q]
      rw [inv_div]
      field_simp [hx.ne']
      ring
    rw [hupper] at hu
    rw [hlower] at hl
    rw [hFq]
    constructor <;> linarith
  have hlim : Tendsto F atTop (𝓝 (a - b)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [mul_one] using hq.const_mul (a - b))
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  have hnonpos (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) : -shiftKernel a b r ≤ 0 :=
    neg_nonpos.mpr (shiftKernel_nonneg ha hb hr)
  have hi := integrableOn_Ioi_deriv_of_nonpos hF hderiv hnonpos hlim
  have he := integral_Ioi_of_hasDerivAt_of_nonpos hF hderiv hnonpos hlim
  refine ⟨integrable_neg_iff.mp hi, ?_⟩
  rw [integral_neg] at he
  simp only [F, add_zero] at he
  linarith

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem cfc_add_shift (T : Matrix n n ℂ) (hT : T.IsHermitian) (r : ℝ) :
    cfc (fun x : ℝ => x + r) T = T + r • (1 : Matrix n n ℂ) := by
  have hid : cfc (id : ℝ → ℝ) T = T := cfc_id ℝ T hT
  calc
    _ = cfc (id : ℝ → ℝ) T + algebraMap ℝ (Matrix n n ℂ) r :=
      cfc_add_const r id T continuousOn_id hT
    _ = _ := by rw [hid, Algebra.algebraMap_eq_smul_one]

theorem cfc_shift (T : Matrix n n ℂ) (hT : T.IsHermitian) (r : ℝ) (f : ℝ → ℝ) :
    cfc f (T + r • (1 : Matrix n n ℂ)) = cfc (fun x => f (x + r)) T := by
  rw [← cfc_add_shift T hT r]
  exact (cfc_comp' f (fun x => x + r) T
    ((T.finite_real_spectrum.image _).continuousOn _) (continuousOn_id.add_const r) hT).symm

private theorem inv_eq_cfc {T : Matrix n n ℂ} (hT : T.PosDef) :
    T⁻¹ = cfc (fun x : ℝ => x⁻¹) T := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact (cfc_ringInverse_id (R := ℝ) T hT.isUnit hT.isHermitian).symm

private theorem trace_re_eq_sum {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    T.trace.re = ∑ i, hT.eigenvalues i := by
  simpa using congrArg Complex.re hT.trace_eq_sum_eigenvalues

private theorem trace_product_difference
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (A * (cfc f A - cfc g B)).trace.re =
      ∑ i, ∑ j, (hA.eigenvalues i * f (hA.eigenvalues i) -
        hA.eigenvalues i * g (hB.eigenvalues j)) * overlap hA hB i j := by
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re, trace_self_cfc A hA f,
    ← overlap_weighted_row hA hB]
  have hcross := trace_cfc_product A B hA hB (fun x => x) g
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA
  rw [hid] at hcross
  rw [hcross]
  simp_rw [sub_mul, Finset.sum_sub_distrib]

private theorem shifted_trace_eq_overlap {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) {r : ℝ} (hr : 0 < r) :
    let X := A + r • (1 : Matrix n n ℂ)
    let Y := B + r • (1 : Matrix n n ℂ)
    (CFC.log Y).trace.re - (CFC.log X).trace.re + ((A - B) * Y⁻¹).trace.re =
      ∑ i, ∑ j, shiftKernel (hA.isHermitian.eigenvalues i)
        (hB.isHermitian.eigenvalues j) r * overlap hA.isHermitian hB.isHermitian i j := by
  dsimp only
  let ha := hA.isHermitian
  let hb := hB.isHermitian
  let f : ℝ → ℝ := fun x => (x + r)⁻¹
  let Y := B + r • (1 : Matrix n n ℂ)
  have hy : Y.PosDef := hB.add_posSemidef (Matrix.PosSemidef.one.smul hr.le)
  have hinv : Y⁻¹ = cfc f B := (inv_eq_cfc hy).trans (cfc_shift B hb r _)
  have cross := trace_cfc_product A B ha hb (fun x => x) f
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A ha
  rw [hid] at cross
  change (cfc Real.log Y).trace.re - (cfc Real.log (A + r • 1)).trace.re +
    ((A - B) * Y⁻¹).trace.re = _
  rw [cfc_shift B hb, cfc_shift A ha, trace_cfc_eq_sum B hb, trace_cfc_eq_sum A ha,
    hinv, sub_mul, Matrix.trace_sub, Complex.sub_re, cross, trace_self_cfc B hb f]
  rw [← overlap_weighted_column ha hb (fun j => Real.log (hb.eigenvalues j + r)),
    ← overlap_weighted_row ha hb (fun i => Real.log (ha.eigenvalues i + r)),
    ← overlap_weighted_column ha hb (fun j => hb.eigenvalues j * f (hb.eigenvalues j))]
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold shiftKernel f
  rw [div_eq_mul_inv]
  ring

private theorem det_eq_ofReal_prod {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    T.det = ((∏ i, hT.eigenvalues i : ℝ) : ℂ) := by
  rw [hT.det_eq_prod_eigenvalues]
  exact (Complex.ofReal_prod (s := Finset.univ) hT.eigenvalues).symm

private theorem shifted_trace_eq_spectral [Nonempty n] {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) {r : ℝ} (hr : 0 < r) :
    let X := A + r • (1 : Matrix n n ℂ)
    let Y := B + r • (1 : Matrix n n ℂ)
    let R := (CFC.sqrt X)⁻¹
    let hK := isHermitian_conjTranspose_mul_mul R (hB.isHermitian.sub hA.isHermitian)
    (CFC.log Y).trace.re - (CFC.log X).trace.re + ((A - B) * Y⁻¹).trace.re =
      ∑ i, (Real.log (1 + hK.eigenvalues i) -
        hK.eigenvalues i / (1 + hK.eigenvalues i)) := by
  let X := A + r • (1 : Matrix n n ℂ)
  let Y := B + r • (1 : Matrix n n ℂ)
  let S := CFC.sqrt X
  let R := S⁻¹
  let K := Rᴴ * (B - A) * R
  let hK : K.IsHermitian := isHermitian_conjTranspose_mul_mul R (hB.isHermitian.sub hA.isHermitian)
  let Q := relativeCongruence Y X
  have hx : X.PosDef := Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hr)
  have hy : Y.PosDef := hB.add_posSemidef (Matrix.PosSemidef.one.smul hr.le)
  have hq : Q.PosDef := relativeCongruence_pos Y X hy hx
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff_isStrictlyPositive).mpr hx.isStrictlyPositive
  have hSdet := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hSdet
  have hRh : Rᴴ = R := ((CFC.sqrt_nonneg X).posSemidef.isHermitian.inv).eq
  have hSS : S * S = X := CFC.sqrt_mul_sqrt_self X hx.posSemidef.nonneg
  have hQ : Q = K + (1 : ℝ) • 1 := by
    have hD : Y = B - A + X := by dsimp [X, Y]; abel
    have hRXR : R * X * R = 1 := by rw [← hSS, ← mul_assoc, hRS, one_mul, hSR]
    change R * Y * R = _
    rw [hD, mul_add, add_mul, hRXR, one_smul, show K = R * (B - A) * R by simp only [K, hRh]]
  have hY : Y = S * Q * S := by
    change Y = S * (R * Y * R) * S
    calc
      Y = (S * R) * Y * (R * S) := by rw [hSR, hRS, one_mul, mul_one]
      _ = _ := by noncomm_ring
  have hdet : Y.det = X.det * Q.det := by
    calc
      Y.det = S.det * Q.det * S.det := by rw [hY, Matrix.det_mul, Matrix.det_mul]
      _ = X.det * Q.det := by rw [← hSS, Matrix.det_mul]; ring
  have hdetre : Y.det.re = X.det.re * Q.det.re := by
    rw [hdet, det_eq_ofReal_prod hx.isHermitian, det_eq_ofReal_prod hq.isHermitian]
    rw [← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  have det_re_pos {T : Matrix n n ℂ} (ht : T.PosDef) : 0 < T.det.re := by
    rw [det_eq_ofReal_prod ht.isHermitian, Complex.ofReal_re]
    exact Finset.prod_pos fun i _ => ht.eigenvalues_pos i
  have hlog : (CFC.log Y).trace.re - (CFC.log X).trace.re = (CFC.log Q).trace.re := by
    rw [trace_log_eq_log_det Y hy, trace_log_eq_log_det X hx, trace_log_eq_log_det Q hq, hdetre,
      Real.log_mul (det_re_pos hx).ne' (det_re_pos hq).ne']
    ring
  have hQinv : Q⁻¹ = S * Y⁻¹ * S := by
    change (S⁻¹ * Y * S⁻¹)⁻¹ = _
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv S hSdet, mul_assoc]
  have htraceinv : ((A - B) * Y⁻¹).trace.re = (Q⁻¹ - 1).trace.re := by
    have hd : A - B = X - Y := by dsimp [X, Y]; abel
    rw [hd, sub_mul, Matrix.mul_nonsing_inv Y ((Matrix.isUnit_iff_isUnit_det Y).mp hy.isUnit),
      Matrix.trace_sub, Matrix.trace_sub, hQinv, Matrix.trace_mul_cycle, ← hSS]
  have hlogsum : (CFC.log Q).trace.re = ∑ i, Real.log (1 + hK.eigenvalues i) := by
    change (cfc Real.log Q).trace.re = _
    rw [hQ, cfc_shift K hK, trace_cfc_eq_sum K hK]
    simp only [add_comm _ (1 : ℝ)]
  have hinvsum : (Q⁻¹ - 1).trace.re = ∑ i, ((1 + hK.eigenvalues i)⁻¹ - 1) := by
    rw [inv_eq_cfc hq, hQ, cfc_shift K hK, Matrix.trace_sub, Complex.sub_re,
      trace_cfc_eq_sum K hK]
    simp [Finset.sum_sub_distrib, Matrix.trace_one, add_comm _ (1 : ℝ)]
  change (CFC.log Y).trace.re - (CFC.log X).trace.re + ((A - B) * Y⁻¹).trace.re = _
  rw [hlog, htraceinv, hlogsum, hinvsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hne : 1 + hK.eigenvalues i ≠ 0 := by
    intro h
    have hs : 0 ∈ spectrum ℝ Q := by
      have hmap : spectrum ℝ (cfc (fun x : ℝ => x + 1) K) =
          (fun x : ℝ => x + 1) '' spectrum ℝ K :=
        cfc_map_spectrum (a := K) (f := fun x : ℝ => x + 1) hK
          (continuousOn_id.add_const 1)
      rw [hQ, ← cfc_add_shift K hK, hmap, hK.spectrum_real_eq_range_eigenvalues]
      exact ⟨hK.eigenvalues i, ⟨i, rfl⟩, by linarith⟩
    exact spectrum.zero_notMem ℝ hq.isUnit hs
  field_simp [hne]
  ring

/-- For finite PSD A and PD B, the weighted negative-part pencil integral equals
the Umegaki trace pairing with its affine trace correction. -/
theorem lintegral_weighted_negPart_pencil_eq_umegaki
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosDef) :
    let hM (t : ℝ) := hA.isHermitian.add
      ((hB.isHermitian.sub hA.isHermitian).smul (IsSelfAdjoint.all t))
    (∫⁻ t, ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart (hM t)))) =
      ENNReal.ofReal ((A * (CFC.log A - cfc Real.log B)).trace.re - (A - B).trace.re) := by
  classical
  have hton := lintegral_weighted_negPart_pencil hA hB.posSemidef
  dsimp only at hton ⊢
  refine hton.trans ?_
  cases isEmpty_or_nonempty n with
  | inl hn =>
    simp [Matrix.trace]
  | inr hn =>
    let ha := hA.isHermitian
    let hb := hB.isHermitian
    let a := ha.eigenvalues
    let b := hb.eigenvalues
    let w := overlap ha hb
    let f (r : ℝ) := ∑ i, ∑ j, shiftKernel (a i) (b j) r * w i j
    have hpair (i j : n) := integral_shiftKernel (hA.eigenvalues_nonneg i) (hB.eigenvalues_pos j)
    have hp (i j : n) : IntegrableOn (fun r => shiftKernel (a i) (b j) r * w i j) (Ioi 0) :=
      (hpair i j).1.mul_const _
    have hrow (i : n) : IntegrableOn (fun r => ∑ j, shiftKernel (a i) (b j) r * w i j)
        (Ioi 0) := integrable_finsetSum _ fun j _ => hp i j
    have hf : IntegrableOn f (Ioi 0) := integrable_finsetSum _ fun i _ => hrow i
    have hfpos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (shiftKernel_nonneg (hA.eigenvalues_nonneg i) (hB.eigenvalues_pos j) hr)
          (sq_nonneg _)
    calc
      _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (f r) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact congrArg ENNReal.ofReal
          ((shifted_trace_eq_spectral hA hB hr).symm.trans (shifted_trace_eq_overlap hA hB hr))
      _ = ENNReal.ofReal (∫ r in Ioi (0 : ℝ), f r) :=
        (ofReal_integral_eq_lintegral_ofReal hf hfpos).symm
      _ = _ := by
        congr 1
        change (∫ r in Ioi (0 : ℝ), ∑ i, ∑ j, shiftKernel (a i) (b j) r * w i j) = _
        have hintegral (i j : n) :
            (∫ r in Ioi (0 : ℝ), shiftKernel (a i) (b j) r * w i j) =
              (a i * Real.log (a i) - a i * Real.log (b j) - (a i - b j)) * w i j := by
          rw [integral_mul_const]
          exact congrArg (· * w i j) (hpair i j).2
        rw [integral_finsetSum _ (fun i _ => hrow i)]
        simp_rw [integral_finsetSum _ (fun j _ => hp _ j), hintegral]
        change _ = (A * (cfc Real.log A - cfc Real.log B)).trace.re - (A - B).trace.re
        rw [trace_product_difference A B ha hb, Matrix.trace_sub, Complex.sub_re,
          trace_re_eq_sum ha, trace_re_eq_sum hb, ← overlap_weighted_row ha hb a,
          ← overlap_weighted_column ha hb b]
        simp_rw [← Finset.sum_sub_distrib, sub_mul]
        rfl

#print axioms lintegral_weighted_negPart_pencil_eq_umegaki

end D5.S3.Quantum.Divergence.UmegakiPencilIntegral
