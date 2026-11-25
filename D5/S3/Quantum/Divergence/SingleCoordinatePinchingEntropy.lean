/- GID: D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Shifted determinants and the trace entropy cost of one-coordinate pinching. -/

import D5.S3.Quantum.Divergence.SingleCoordinateSchur
import D5.S3.Quantum.Divergence.UmegakiPencilIntegral
import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Quantum.Subentropy.UniformIntegrals

/-! Equal trace cancels the scalar shift corrections, allowing the pointwise Schur
bound to be integrated against the shifted determinants of the two matrices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy (trace_self_cfc)
open D5.S3.Quantum.Divergence.UmegakiPencilIntegral (shiftKernel integral_shiftKernel cfc_shift)
open D5.S3.Resource.LogDet.LogDetInformationSubmodularity (trace_log_eq_log_det)
open D5.S3.Resource.LogDet.PathSpectralClassical (trace_cfc_eq_sum)

namespace D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The difference of shifted log determinants is integrable when the positive
semidefinite matrices have equal trace. Its integral is the trace entropy difference,
with the sign corresponding to the order of the determinant ratio. -/
theorem integral_log_det_shift_sub (X Y : Matrix n n ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (htr : X.trace.re = Y.trace.re) :
    IntegrableOn (fun s : ℝ => Real.log (Y + s • 1).det.re - Real.log (X + s • 1).det.re)
      (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), Real.log (Y + s • 1).det.re - Real.log (X + s • 1).det.re) =
      (X * CFC.log X).trace.re - (Y * CFC.log Y).trace.re := by
  cases isEmpty_or_nonempty n with
  | inl hn => simp [Matrix.det_isEmpty, Matrix.trace]
  | inr hn =>
    let x := hX.isHermitian.eigenvalues
    let y := hY.isHermitian.eigenvalues
    have hsum : ∑ i, x i = ∑ i, y i := by
      have hx : X.trace.re = ∑ i, x i := by
        simpa using congrArg Complex.re hX.isHermitian.trace_eq_sum_eigenvalues
      have hy : Y.trace.re = ∑ i, y i := by
        simpa using congrArg Complex.re hY.isHermitian.trace_eq_sum_eigenvalues
      rw [← hx, ← hy, htr]
    let kernelSum (a : n → ℝ) (s : ℝ) := ∑ i, shiftKernel (a i) 1 s
    have hkernel (a : n → ℝ) (ha : ∀ i, 0 ≤ a i) :
        IntegrableOn (kernelSum a) (Ioi 0) ∧
        (∫ s in Ioi (0 : ℝ), kernelSum a s) =
          (∑ i, a i * Real.log (a i)) - ((∑ i, a i) - ∑ _i : n, (1 : ℝ)) := by
      have hscalar (i : n) := integral_shiftKernel (ha i) zero_lt_one
      refine ⟨integrable_finsetSum _ (fun i _ => (hscalar i).1), ?_⟩
      unfold kernelSum
      rw [integral_finsetSum _ (fun i _ => (hscalar i).1)]
      simp_rw [(hscalar _).2, Real.log_one, mul_zero, sub_zero, Finset.sum_sub_distrib]
    obtain ⟨hix, hex⟩ := hkernel x hX.eigenvalues_nonneg
    obtain ⟨hiy, hey⟩ := hkernel y hY.eigenvalues_nonneg
    have hlog (T : Matrix n n ℂ) (hT : T.PosSemidef) (s : ℝ) (hs : 0 < s) :
        Real.log (T + s • 1).det.re = ∑ i, Real.log (hT.isHermitian.eigenvalues i + s) := by
      have hp : (T + s • 1).PosDef :=
        (Matrix.PosDef.one.smul hs).posSemidef_add hT
      rw [← trace_log_eq_log_det _ hp]
      change (cfc Real.log (T + s • 1)).trace.re = _
      rw [cfc_shift T hT.isHermitian, trace_cfc_eq_sum T hT.isHermitian]
    have hpoint : (fun s : ℝ => kernelSum x s - kernelSum y s)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))]
          (fun s => Real.log (Y + s • 1).det.re - Real.log (X + s • 1).det.re) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [hlog X hX s hs, hlog Y hY s hs]
      change kernelSum x s - kernelSum y s = (∑ i, Real.log (y i + s)) - ∑ i, Real.log (x i + s)
      simp only [kernelSum, shiftKernel, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_div, hsum]
      ring
    refine ⟨(hix.sub hiy).congr hpoint, ?_⟩
    rw [← integral_congr_ae hpoint, integral_sub hix hiy, hex, hey, hsum]
    change _ = (X * cfc Real.log X).trace.re - (Y * cfc Real.log Y).trace.re
    rw [trace_self_cfc X hX.isHermitian, trace_self_cfc Y hY.isHermitian]
    change _ = (∑ i, x i * Real.log (x i)) - ∑ i, y i * Real.log (y i)
    ring

/-- The Löwner sandwich bounds the trace entropy cost of pinching one coordinate,
with no normalization of the matrices or restriction on the retained dimension. -/
theorem trace_entropy_pinching_bound (C F : Matrix n n ℂ) (h : Matrix n Unit ℂ)
    (a lam c u v : ℝ) (hC : C.PosDef) (hlam : 0 < lam) (hlc : lam < c) (hu : 0 < u)
    (hd : 0 < (v - u) / 2) (hdu : (v - u) / 2 < u)
    (hcap : C ≤ c • (1 : Matrix n n ℂ))
    (hlo : u • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ) ≤
      fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ))
    (hhi : fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ) ≤
      v • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ)) :
    let d := (v - u) / 2
    let A := fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ)
    let A₀ := fromBlocks F 0 0 (a • 1 : Matrix Unit Unit ℂ)
    let cost := (A * CFC.log A).trace.re - (A₀ * CFC.log A₀).trace.re
    0 ≤ cost ∧
      cost ≤ (u * d ^ 2 / (u ^ 2 - d ^ 2)) * lam * (c / (c - lam)) * Real.log (c / lam) := by
  intro d A A₀ cost
  have hc := hlam.trans hlc
  have hlow := Matrix.le_iff.mp hlo
  have ha : 0 < a := by
    have hdiag := (Complex.nonneg_iff.mp (hlow.diag_nonneg (i := Sum.inr ()))).1
    have halower : u * lam ≤ a := by
      simpa [fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.smul_apply, Complex.smul_re] using hdiag
    exact (mul_pos hu hlam).trans_le halower
  have hA : A.PosSemidef := by
    have hbase := UmegakiRareFlagBKM.block_diag_posDef C (1 : Matrix Unit Unit ℂ)
      hC Matrix.PosDef.one hlam
    have hadd := (hbase.smul hu).posSemidef.add hlow
    rwa [add_sub_cancel] at hadd
  have hA₀ : A₀.PosSemidef := by
    have hFpos : F.PosDef := by
      have hdiff := hlow.submatrix (Sum.inl : n → n ⊕ Unit)
      have hadd := (hC.smul hu).add_posSemidef hdiff
      change (u • C + (F - u • C)).PosDef at hadd
      rwa [add_sub_cancel] at hadd
    exact (UmegakiRareFlagBKM.block_diag_posDef F (1 : Matrix Unit Unit ℂ)
      hFpos Matrix.PosDef.one ha).posSemidef
  have htrace : A.trace.re = A₀.trace.re := by
    simp [A, A₀, Matrix.trace, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₂]
  let deficit (s : ℝ) := Real.log (A₀ + s • 1).det.re - Real.log (A + s • 1).det.re
  obtain ⟨hi, he⟩ := integral_log_det_shift_sub A A₀ hA hA₀ htrace
  change IntegrableOn deficit (Ioi 0) at hi
  change (∫ s in Ioi (0 : ℝ), deficit s) = cost at he
  have hsq : d ^ 2 < u ^ 2 := pow_lt_pow_left₀ hdu hd.le (by decide)
  let coeff := (u * d ^ 2 / (u ^ 2 - d ^ 2)) * lam * (c / (c - lam))
  let majorant (s : ℝ) := coeff * (1 / (s + u * lam) - 1 / (s + u * c))
  obtain ⟨hm, hmval⟩ := Subentropy.UniformIntegrals.reciprocal_difference
    (u * lam) (u * c) (mul_pos hu hlam) (mul_le_mul_of_nonneg_left hlc.le hu.le)
  have hmi : IntegrableOn majorant (Ioi 0) := hm.const_mul coeff
  have hbounds (s : ℝ) (hs : 0 < s) : 0 ≤ deficit s ∧ deficit s ≤ majorant s := by
    have hpoint := SingleCoordinateSchur.schur_det_log_bound C F h a lam c u v s
      hC hlam hc hu hd hdu hs.le hcap hlo hhi
    refine ⟨hpoint.2.2.2.2.2.2.1, hpoint.2.2.2.2.2.2.2.trans_eq ?_⟩
    have hals : 0 < u * lam + s := by positivity
    have hcs : 0 < u * c + s := by positivity
    change (d ^ 2 * lam * c / ((u * c + s) * (u * lam + s))) / (1 - d ^ 2 / u ^ 2) = _
    dsimp [majorant, coeff]
    rw [show 1 - d ^ 2 / u ^ 2 = (u ^ 2 - d ^ 2) / u ^ 2 by field_simp]
    rw [add_comm s, add_comm s]
    field_simp [hu.ne', hals.ne', hcs.ne', (sub_pos.mpr hsq).ne', (sub_pos.mpr hlc).ne']
    ring
  rw [← he]
  constructor
  · exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using (hbounds s hs).1)
  · calc
      _ ≤ ∫ s in Ioi (0 : ℝ), majorant s := integral_mono_ae hi hmi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using (hbounds s hs).2)
      _ = coeff * Real.log (c / lam) := by
        unfold majorant
        rw [integral_const_mul, hmval, ← Real.log_div (mul_pos hu hc).ne' (mul_pos hu hlam).ne',
          mul_div_mul_left _ _ hu.ne']

#print axioms integral_log_det_shift_sub
#print axioms trace_entropy_pinching_bound

end D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy
