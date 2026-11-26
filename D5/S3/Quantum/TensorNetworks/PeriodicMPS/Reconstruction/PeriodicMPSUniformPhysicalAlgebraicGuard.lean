/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Two real linear exceptional slices and a six-dimensional mixed-trace bound. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformCompactGraph
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphCriticalDimension

/-! Real exceptional slices of the trace-aligned transfer coefficient guard. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformPhysicalAlgebraicGuard

open Set MvPolynomial
open scoped ComplexConjugate
open PeriodicMPSUniformCompactGraph (Parameters)
open SevenSiteCriticalCertificate (sliceBlock)
open SevenSitePhysicalRankBridge
  (Ordinary Rotation SlicePoint align unalign_align physicalChart analyticAt_physicalChart)
open SevenSitePhysicalRankAssembly (alignedSlice asOrdinary)

open private phase from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
open private phase_two_charts parametersOfOrdinary parametersOfOrdinary_asOrdinary
  differentiable_parametersOfOrdinary zeroMixed dimH_zeroMixed_le from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphCriticalDimension

noncomputable section

private theorem exists_physicalChart_alignedSlice (p : Ordinary) (hK : (align p).2.2.2 ≠ 0) :
    ∃ (b : Bool) (v : Rotation), physicalChart (if b then 1 else -1) (v, alignedSlice p) = p := by
  let q := align p
  let K := q.2.2.2
  let r := Real.sqrt (Complex.normSq K)
  let l := K / (r : ℂ)
  let x := alignedSlice p
  have hk : 0 < Complex.normSq K := Complex.normSq_pos.2 hK
  have hr : 0 < r := Real.sqrt_pos.2 hk
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hl : Complex.normSq l = 1 := by
    rw [show l = K / (r : ℂ) from rfl, Complex.normSq_div, Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt (Complex.normSq_nonneg K), div_self hk.ne']
  obtain ⟨b, c, hc⟩ := phase_two_charts l hl
  let angles : Rotation := (-2 * q.1.im, 2 * q.1.re, c)
  refine ⟨b, angles, ?_⟩
  change physicalChart (if b then 1 else -1) (angles, x) = p
  have hs : ((↑angles.2.1 : ℂ) - Complex.I * ↑angles.1) / 2 = q.1 := by
    have he := Complex.re_add_im q.1
    change (((2 * q.1.re : ℝ) : ℂ) - Complex.I * ((-2 * q.1.im : ℝ) : ℂ)) / 2 = q.1
    push_cast
    linear_combination he
  have hd : (x 0 : ℂ) + Complex.I * (x 3 : ℂ) = q.2.1 := by
    change (q.2.1.re : ℂ) + Complex.I * (q.2.1.im : ℂ) = q.2.1
    rw [mul_comm Complex.I, Complex.re_add_im]
  have he : (x 2 : ℂ) + Complex.I * (x 4 : ℂ) = q.2.2.1 / l ^ 2 := by
    change ((q.2.2.1 / l ^ 2).re : ℂ) + Complex.I * ((q.2.2.1 / l ^ 2).im : ℂ) = _
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hmul : l * (x 1 : ℂ) = K := div_mul_cancel₀ _ hrC
  have hlne : l ≠ 0 := div_ne_zero hK hrC
  have hc' : (if b then 1 else -1) * phase angles.2.2 = l := hc
  simp only [physicalChart, Complex.ofRealCLM_apply, hs, hc', hd, he, hmul]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero 2 hlne)]
  exact unalign_align p

/-- The zero aligned mixed-trace locus has real Hausdorff dimension at most six. -/
theorem dimH_zeroMixed_parameters_le :
    dimH {u : Parameters | (align (asOrdinary u)).2.2.2 = 0} ≤ 6 := by
  have hsub : {u : Parameters | (align (asOrdinary u)).2.2.2 = 0} ⊆
      parametersOfOrdinary '' {p : Ordinary | (align p).2.2.2 = 0} :=
    fun u hu => ⟨asOrdinary u, hu, parametersOfOrdinary_asOrdinary u⟩
  refine (dimH_mono hsub).trans
    (differentiable_parametersOfOrdinary.differentiableOn.dimH_image_le.trans ?_)
  exact dimH_zeroMixed_le

/-- The polynomial specialization of `k U (c - b²)` in the native cofactor coordinates. -/
def physicalGuard : MvPolynomial (Fin 5) ℂ :=
  let ket := sliceBlock (C Complex.I) X true
  let bra := sliceBlock (C Complex.I) X false
  ket 1 * (ket 0 * bra 0) * (ket 1 ^ 2 * (ket 0 + bra 2) * (bra 0 + ket 2))

private def sliceD (x : SlicePoint) : ℂ := (x 0 : ℂ) + Complex.I * (x 3 : ℂ)
private def sliceE (x : SlicePoint) : ℂ := (x 2 : ℂ) + Complex.I * (x 4 : ℂ)

private theorem eval_physicalGuard_factored (x : SlicePoint) :
    eval (fun i => (x i : ℂ)) physicalGuard =
      (x 1 : ℂ) * (sliceD x * conj (sliceD x)) *
        ((x 1 : ℂ) ^ 2 * (sliceD x + conj (sliceE x)) * (conj (sliceD x) + sliceE x)) := by
  simp [physicalGuard, sliceBlock, sliceD, sliceE, Complex.conj_ofReal, Complex.conj_I]

/-- The factored guard uses the coefficients of the trace-aligned mixed-transfer quartic. -/
theorem eval_physicalGuard (x : SlicePoint) :
    let k : ℂ := x 1
    let d := (x 0 : ℂ) + Complex.I * (x 3 : ℂ)
    let e := (x 2 : ℂ) + Complex.I * (x 4 : ℂ)
    let U := d * conj d
    let b := U - e * conj e
    let c := b ^ 2 + k ^ 2 * (d + conj e) * (conj d + e)
    eval (fun i => (x i : ℂ)) physicalGuard = k * U * (c - b ^ 2) := by
  dsimp only
  rw [add_sub_cancel_left, eval_physicalGuard_factored]
  rfl

/-- At positive mixed trace the exact exceptional conditions are `d = 0` and
`d = -conj e`. -/
theorem eval_physicalGuard_eq_zero_iff (x : SlicePoint) (hk : 0 < x 1) :
    eval (fun i => (x i : ℂ)) physicalGuard = 0 ↔
      (x 0 = 0 ∧ x 3 = 0) ∨ (x 0 = -x 2 ∧ x 3 = x 4) := by
  have hkC : (x 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hconj : conj (sliceD x + conj (sliceE x)) = conj (sliceD x) + sliceE x := by simp
  rw [eval_physicalGuard_factored]
  have hzero : sliceD x = 0 ↔ x 0 = 0 ∧ x 3 = 0 := by
    simp [sliceD, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hcross : sliceD x + conj (sliceE x) = 0 ↔ x 0 = -x 2 ∧ x 3 = x 4 := by
    simp [sliceD, sliceE, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, add_eq_zero_iff_eq_neg]
  have hcross' : conj (sliceD x) + sliceE x = 0 ↔ x 0 = -x 2 ∧ x 3 = x 4 := by
    rw [← hconj]
    exact star_eq_zero.trans hcross
  simp [mul_eq_zero, hkC, pow_ne_zero 2 hkC, hzero, hcross, hcross']

/-- The linear slice `d = 0`, parametrized by `(k, Re e, Im e)`. -/
def zeroDetSlice : (Fin 3 → ℝ) →ₗ[ℝ] SlicePoint where
  toFun t := ![0, t 0, t 1, 0, t 2]
  map_add' t s := by
    ext i
    fin_cases i <;> simp
  map_smul' a t := by
    ext i
    fin_cases i <;> simp

/-- The linear slice `d = -conj e`, parametrized by `(k, Re e, Im e)`. -/
def conjugateDetSlice : (Fin 3 → ℝ) →ₗ[ℝ] SlicePoint where
  toFun t := ![-t 1, t 0, t 1, t 2, t 2]
  map_add' t s := by
    ext i
    fin_cases i <;> simp
    ac_rfl
  map_smul' a t := by
    ext i
    fin_cases i <;> simp [mul_neg]

/-- Both linear parametrizations have the same coordinate projection as a left inverse. -/
theorem exceptionalSlice_leftInverse :
    Function.LeftInverse (fun x : SlicePoint => ![x 1, x 2, x 4]) zeroDetSlice ∧
    Function.LeftInverse (fun x : SlicePoint => ![x 1, x 2, x 4]) conjugateDetSlice := by
  constructor <;> intro t <;> funext i <;> fin_cases i <;> rfl

private theorem mem_range_zeroDetSlice (x : SlicePoint) :
    x ∈ range zeroDetSlice ↔ x 0 = 0 ∧ x 3 = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h3⟩
    refine ⟨![x 1, x 2, x 4], ?_⟩
    funext i
    fin_cases i <;> simp [zeroDetSlice, h0, h3]

private theorem mem_range_conjugateDetSlice (x : SlicePoint) :
    x ∈ range conjugateDetSlice ↔ x 0 = -x 2 ∧ x 3 = x 4 := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h3⟩
    refine ⟨![x 1, x 2, x 4], ?_⟩
    funext i
    fin_cases i <;> simp [conjugateDetSlice, h0, h3]

private theorem dimH_physicalChart_linearSlice_le (l : ℂ)
    (L : (Fin 3 → ℝ) →ₗ[ℝ] SlicePoint) :
    dimH (physicalChart l '' {q | 0 < q.2 1 ∧ q.2 ∈ range L}) ≤ 6 := by
  let F (q : Rotation × (Fin 3 → ℝ)) := physicalChart l (q.1, L q.2)
  have hL : Differentiable ℝ L := L.toContinuousLinearMap.differentiable
  have hchart : Differentiable ℝ (physicalChart l) :=
    fun q => (analyticAt_physicalChart l q).differentiableAt
  have hF : Differentiable ℝ F :=
    hchart.comp (differentiable_fst.prodMk (hL.comp differentiable_snd))
  refine (dimH_mono (t := range F) ?_).trans ?_
  · rintro _ ⟨⟨v, x⟩, ⟨_, t, rfl⟩, rfl⟩
    exact ⟨(v, t), rfl⟩
  · refine hF.dimH_range_le.trans_eq ?_
    norm_num [Rotation, Module.finrank_prod, Module.finrank_pi_fintype]

/-- For either phase frame, the images of the two positive exceptional slices
have Hausdorff dimension at most six. -/
theorem dimH_physicalChart_exceptionalSlices_le (l : ℂ) :
    dimH (physicalChart l '' {q | 0 < q.2 1 ∧ q.2 ∈ range zeroDetSlice}) ≤ 6 ∧
    dimH (physicalChart l '' {q | 0 < q.2 1 ∧ q.2 ∈ range conjugateDetSlice}) ≤ 6 :=
  ⟨dimH_physicalChart_linearSlice_le l zeroDetSlice,
    dimH_physicalChart_linearSlice_le l conjugateDetSlice⟩

/-- The positive guard-zero slice is exactly the union of the two linear slices
restricted to positive mixed trace. -/
theorem dimH_physicalChart_guardZero_le (l : ℂ) :
    dimH (physicalChart l ''
      {q | 0 < q.2 1 ∧ eval (fun i => (q.2 i : ℂ)) physicalGuard = 0}) ≤ 6 := by
  have hs : {q : Rotation × SlicePoint |
      0 < q.2 1 ∧ eval (fun i => (q.2 i : ℂ)) physicalGuard = 0} =
      {q | 0 < q.2 1 ∧ q.2 ∈ range zeroDetSlice} ∪
      {q | 0 < q.2 1 ∧ q.2 ∈ range conjugateDetSlice} := by
    ext q
    change (_ ∧ _) ↔ (_ ∧ _) ∨ (_ ∧ _)
    rw [← and_or_left]
    exact and_congr_right fun hk => (eval_physicalGuard_eq_zero_iff q.2 hk).trans
      (or_congr (mem_range_zeroDetSlice q.2).symm (mem_range_conjugateDetSlice q.2).symm)
  rw [hs, image_union, dimH_union]
  exact sup_le (dimH_physicalChart_exceptionalSlices_le l).1
    (dimH_physicalChart_exceptionalSlices_le l).2

/-- The guard-zero parameter locus within the nonzero mixed-trace sector has
Hausdorff dimension at most six. -/
theorem dimH_physicalGuard_zero_le :
    dimH {u : Parameters | (align (asOrdinary u)).2.2.2 ≠ 0 ∧
      eval (fun i => (alignedSlice (asOrdinary u) i : ℂ)) physicalGuard = 0} ≤ 6 := by
  let S (b : Bool) : Set Ordinary := physicalChart (if b then 1 else -1) ''
    {q | 0 < q.2 1 ∧ eval (fun i => (q.2 i : ℂ)) physicalGuard = 0}
  refine (dimH_mono (t := ⋃ b : Bool, parametersOfOrdinary '' S b) ?_).trans ?_
  · rintro u ⟨hK, hg⟩
    obtain ⟨b, v, hframe⟩ := exists_physicalChart_alignedSlice (asOrdinary u) hK
    have hk : 0 < alignedSlice (asOrdinary u) 1 :=
      Real.sqrt_pos.2 (Complex.normSq_pos.2 hK)
    exact mem_iUnion.mpr ⟨b, asOrdinary u, ⟨(v, alignedSlice (asOrdinary u)), ⟨hk, hg⟩, hframe⟩,
      parametersOfOrdinary_asOrdinary u⟩
  · rw [dimH_iUnion]
    exact iSup_le fun b => differentiable_parametersOfOrdinary.differentiableOn.dimH_image_le.trans
      (dimH_physicalChart_guardZero_le (if b then 1 else -1))

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformPhysicalAlgebraicGuard
