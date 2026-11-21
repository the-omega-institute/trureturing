/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphCriticalDimension
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphCriticalDimension
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The compact seven-site exceptional set has dimension at most six. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankAssembly
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The rank-deficient ordinary locus and its closure in the compact seven-site graph. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteGraphCriticalDimension

open Function (Injective)
open Set SevenSiteCompactGraph SevenSiteGraphBoundary
open SevenSitePhysicalRankBridge SevenSitePhysicalRankAssembly
open SevenSiteTraceBase (Word amplitude map_amplitude)
open SevenSiteCriticalCertificate (criticalMatrix)
open PeriodicMPSProjectiveCoordinates (mass mass_pos projector)
open PeriodicMPSCompactReadout (Readout readout)
open PeriodicMPSUniformHardCoreLocalization (twoSiteObservation)
open scoped Topology ENNReal Matrix.Norms.Elementwise ComplexConjugate

open private phase phase_re phase_im
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge

noncomputable section

private theorem analyticAt_traceChart_entry (u : Parameters) (i : Fin 5) :
    AnalyticAt ℝ (fun v => traceChart v i) u := by
  fin_cases i
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj (0 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u
  · exact (ContinuousLinearMap.proj (1 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u
  · exact (ContinuousLinearMap.proj (2 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u
  · exact (ContinuousLinearMap.proj (3 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u

private theorem analyticAt_chartAmplitude (u : Parameters) (w : Word 7) :
    AnalyticAt ℝ (fun v => amplitude (traceChart v) w) u := by
  let p : MvPolynomial (Fin 5) ℂ := amplitude MvPolynomial.X w
  have he (v : Parameters) : MvPolynomial.aeval (traceChart v) p = amplitude (traceChart v) w := by
    change MvPolynomial.eval (traceChart v) p = _
    dsimp only [p]
    rw [map_amplitude]
    congr 1
    funext i
    exact MvPolynomial.eval_X (f := traceChart v) i
  simpa only [he] using (AnalyticAt.aeval_mvPolynomial
    (f := fun v => traceChart v) (analyticAt_traceChart_entry u) p)

private theorem analyticAt_chartWeighted (u : Parameters) (i : Fin 6) :
    AnalyticAt ℝ (fun v => weighted (traceChart v) i) u := by
  have h := analyticAt_traceChart_entry u
  fin_cases i
  · exact (h 0).fun_pow 2
  · exact (h 0).fun_mul (h 1)
  · exact (h 1).fun_pow 2
  · exact h 2
  · exact h 3
  · exact h 4

private theorem analyticAt_projector_of_entries {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ι → ℂ} {x : E}
    (hf : ∀ i, AnalyticAt ℝ (fun y => f y i) x) (hx : f x ≠ 0) :
    AnalyticAt ℝ (fun y => projector (f y)) x := by
  have hconj (i : ι) : AnalyticAt ℝ (fun y => conj (f y i)) x :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt _).comp (hf i)
  have hmass : AnalyticAt ℝ (fun y => mass (f y)) x := by
    unfold mass
    apply Finset.analyticAt_fun_sum
    intro i _
    have he (z : ℂ) : Complex.normSq z = (z * conj z).re := by
      simp [Complex.normSq_apply, Complex.mul_re]
    simp_rw [he]
    exact (Complex.reCLM.analyticAt _).comp ((hf i).fun_mul (hconj i))
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  change AnalyticAt ℝ (fun y => (mass (f y))⁻¹ • (f y i * conj (f y j))) x
  exact (hmass.inv (mass_pos _ hx).ne').smul ((hf i).fun_mul (hconj j))

private theorem analyticAt_chartGraph (u : Parameters) (hu : u ∈ chart.source) :
    AnalyticAt ℝ (graph ∘ traceChart) u := by
  have hw : weighted (traceChart u) ≠ 0 := by
    intro h
    have h₀ := congrFun h (0 : Fin 6)
    norm_num [weighted, traceChart] at h₀
  have ha : amplitude (traceChart u) ≠ 0 := hu
  exact (analyticAt_projector_of_entries (analyticAt_chartWeighted u) hw).prod
    (analyticAt_projector_of_entries (analyticAt_chartAmplitude u) ha)

theorem analyticAt_graphReadout (u : Parameters) (hu : u ∈ chart.source) :
    AnalyticAt ℝ graphReadout u := by
  let Q := (twoSiteObservation 5).toContinuousLinearMap.restrictScalars ℝ
  let P := fun v : Parameters => (graph (traceChart v)).2
  have hP : AnalyticAt ℝ P u := analyticAt_snd.comp (analyticAt_chartGraph u hu)
  have hQ : AnalyticAt ℝ (fun v => Q (P v)) u := (Q.analyticAt (P u)).comp (f := P) hP
  exact (readout.analyticAt (Q (P u))).comp (f := fun v => Q (P v)) hQ

/-- Coordinates where the real differential has rank below the dimension of its source. -/
def criticalCoordinates : Set Parameters :=
  {u | u ∈ chart.source ∧ ¬ Injective (fderiv ℝ graphReadout u)}

/-- The rank-deficient graph points in the ordinary chart. -/
def chartCritical : Set Source := chart '' criticalCoordinates

theorem mem_chartCritical_iff {x : Source} :
    x ∈ chartCritical ↔ x ∈ chart.target ∧ ¬ Injective (fderiv ℝ graphReadout (chart.symm x)) := by
  constructor
  · rintro ⟨u, ⟨hu, hr⟩, rfl⟩
    exact ⟨chart.map_source hu, by simpa only [chart.left_inv hu] using hr⟩
  · rintro ⟨hx, hr⟩
    exact ⟨chart.symm x, ⟨chart.map_target hx, hr⟩, chart.right_inv hx⟩

private theorem isClosed_boundary_union_chartCritical : IsClosed (chartBoundary ∪ chartCritical) := by
  let U : Set Parameters := chart.source ∩
    (fderiv ℝ graphReadout) ⁻¹' {L : Parameters →L[ℝ] Readout | Injective L}
  have hd : ContinuousOn (fderiv ℝ graphReadout) chart.source :=
    fun u hu => (analyticAt_graphReadout u hu).fderiv.continuousAt.continuousWithinAt
  have hU : IsOpen U :=
    hd.isOpen_inter_preimage chart.open_source ContinuousLinearMap.isOpen_injective
  have he : (chartBoundary ∪ chartCritical)ᶜ = chart '' U := by
    ext x
    constructor
    · intro hx
      have ht : x ∈ chart.target := by
        by_contra h
        exact hx (Or.inl h)
      have hi : Injective (fderiv ℝ graphReadout (chart.symm x)) := by
        by_contra h
        exact hx (Or.inr (mem_chartCritical_iff.mpr ⟨ht, h⟩))
      exact ⟨chart.symm x, ⟨chart.map_target ht, hi⟩, chart.right_inv ht⟩
    · rintro ⟨u, ⟨hu, hi⟩, rfl⟩
      change Injective (fderiv ℝ graphReadout u) at hi
      rintro (hb | hc)
      · exact hb (chart.map_source hu)
      · exact (mem_chartCritical_iff.mp hc).2
          (by simpa only [chart.left_inv hu] using hi)
  exact isOpen_compl_iff.mp (he ▸ chart.isOpen_image_of_subset_source hU inter_subset_left)

/-- The ordinary rank-deficient locus, closed in the compact graph. -/
def graphCriticalLocus : Set Source := closure chartCritical

theorem isClosed_graphCriticalLocus : IsClosed graphCriticalLocus := isClosed_closure

/-- The boundary and the closed rank-deficient locus form the bad set for continuation. -/
def graphBadLocus : Set Source := chartBoundary ∪ graphCriticalLocus

private theorem graphBadLocus_eq : graphBadLocus = chartBoundary ∪ chartCritical := by
  apply Subset.antisymm
  · exact union_subset subset_union_left
      (closure_minimal subset_union_right isClosed_boundary_union_chartCritical)
  · exact union_subset subset_union_left (subset_closure.trans subset_union_right)

theorem mem_graphCriticalLocus_iff_of_mem_target {x : Source} (hx : x ∈ chart.target) :
    x ∈ graphCriticalLocus ↔ ¬ Injective (fderiv ℝ graphReadout (chart.symm x)) := by
  constructor
  · intro h
    have hb : x ∈ graphBadLocus := Or.inr h
    rw [graphBadLocus_eq] at hb
    rcases hb with hb | hc
    · exact (hb hx).elim
    · exact (mem_chartCritical_iff.mp hc).2
  · intro h
    exact subset_closure (mem_chartCritical_iff.mpr ⟨hx, h⟩)

theorem not_mem_graphBadLocus_iff {x : Source} :
    x ∉ graphBadLocus ↔ x ∈ chart.target ∧ Injective (fderiv ℝ graphReadout (chart.symm x)) := by
  rw [graphBadLocus_eq]
  constructor
  · intro hb
    have ht : x ∈ chart.target := by
      by_contra h
      exact hb (Or.inl h)
    refine ⟨ht, ?_⟩
    by_contra hi
    exact hb (Or.inr (mem_chartCritical_iff.mpr ⟨ht, hi⟩))
  · rintro ⟨ht, hi⟩ (hb | hc)
    · exact hb ht
    · exact (mem_chartCritical_iff.mp hc).2 hi

theorem isCompact_graphBadLocus : IsCompact graphBadLocus := by
  rw [graphBadLocus_eq]
  exact isClosed_boundary_union_chartCritical.isCompact

private theorem phase_of_unit (z : ℂ) (hz : Complex.normSq z = 1)
    (hd : 1 + z.re ≠ 0) : ∃ c : ℝ, phase c = z := by
  let d := 1 + z.re
  let t := z.im / d
  have hlin : d * t = z.im := mul_div_cancel₀ _ hd
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two] using hz
  have ht : d * t ^ 2 = 1 - z.re := by
    apply mul_left_cancel₀ hd
    calc
      d * (d * t ^ 2) = (d * t) ^ 2 := by ring
      _ = z.im ^ 2 := by rw [hlin]
      _ = d * (1 - z.re) := by dsimp [d]; nlinarith [hsq]
  have hden : d * (1 + t ^ 2) = 2 := by rw [mul_add, mul_one, ht]; dsimp [d]; ring
  have hhalf : 2 * t / 2 = t := by ring
  have hpos : 1 + t ^ 2 ≠ 0 := by positivity
  refine ⟨2 * t, Complex.ext ?_ ?_⟩
  · rw [phase_re, hhalf]
    apply (div_eq_iff hpos).2
    apply mul_left_cancel₀ hd
    calc
      d * (1 - t ^ 2) = 2 * z.re := by rw [mul_sub, mul_one, ht]; dsimp [d]; ring
      _ = d * (z.re * (1 + t ^ 2)) := by rw [mul_left_comm d, hden, mul_comm]
  · rw [phase_im, hhalf]
    apply (div_eq_iff hpos).2
    apply mul_left_cancel₀ hd
    calc
      d * (2 * t) = 2 * z.im := by rw [mul_left_comm d, hlin]
      _ = d * (z.im * (1 + t ^ 2)) := by rw [mul_left_comm d, hden, mul_comm]

private theorem phase_two_charts (l : ℂ) (hl : Complex.normSq l = 1) :
    ∃ (b : Bool) (c : ℝ), (if b then 1 else -1) * phase c = l := by
  by_cases h : 1 + l.re = 0
  · obtain ⟨c, hc⟩ := phase_of_unit (-l) (by simpa only [Complex.normSq_neg] using hl) (by
      rw [Complex.neg_re]
      intro he
      linarith)
    exact ⟨false, c, by simp [hc]⟩
  · obtain ⟨c, hc⟩ := phase_of_unit l hl h
    exact ⟨true, c, by simp [hc]⟩

private def physicalSliceImage : Set Ordinary :=
  (fun q : Bool × (Rotation × SlicePoint) => physicalChart (if q.1 then 1 else -1) q.2) ''
    {q | q.2.2 ∈ certifiedCriticalSlice}

private theorem mem_physicalSliceImage (p : Ordinary) (hK : (align p).2.2.2 ≠ 0)
    (hx : alignedSlice p ∈ certifiedCriticalSlice) : p ∈ physicalSliceImage := by
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
  refine ⟨(b, angles, x), hx, ?_⟩
  change physicalChart (if b then 1 else -1) (angles, x) = p
  have hs : ((↑angles.2.1 : ℂ) - Complex.I * ↑angles.1) / 2 = q.1 := by
    have he := Complex.re_add_im q.1
    change (((2 * q.1.re : ℝ) : ℂ) - Complex.I * ((-2 * q.1.im : ℝ) : ℂ)) / 2 = q.1
    push_cast
    linear_combination he
  have hd : (x 0 : ℂ) + Complex.I * (x 3 : ℂ) = q.2.1 := by
    change (q.2.1.re : ℂ) + Complex.I * (q.2.1.im : ℂ) = q.2.1
    rw [mul_comm Complex.I]
    exact Complex.re_add_im q.2.1
  have he : (x 2 : ℂ) + Complex.I * (x 4 : ℂ) = q.2.2.1 / l ^ 2 := by
    change ((q.2.2.1 / l ^ 2).re : ℂ) + Complex.I * ((q.2.2.1 / l ^ 2).im : ℂ) = _
    rw [mul_comm Complex.I]
    exact Complex.re_add_im (q.2.2.1 / l ^ 2)
  have hmul : l * (x 1 : ℂ) = K := div_mul_cancel₀ _ hrC
  have hlne : l ≠ 0 := div_ne_zero hK hrC
  have hc' : (if b then 1 else -1) * phase angles.2.2 = l := hc
  simp only [physicalChart, Complex.ofRealCLM_apply, hs, hc', hd, he, hmul]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero 2 hlne)]
  exact unalign_align p

private theorem dimH_physicalSliceImage_le : dimH physicalSliceImage ≤ 6 := by
  obtain ⟨ι, hι, D, g, hg, hcover⟩ := cover_physicalChart_criticalSlice
  let : Countable ι := hι
  apply (dimH_mono (show physicalSliceImage ⊆ ⋃ i, g i '' D i from hcover)).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  calc
    _ ≤ dimH (D i) := (hg i).dimH_image_le
    _ ≤ dimH (univ : Set (Rotation × (Fin 3 → ℝ))) := dimH_mono (subset_univ _)
    _ = 6 := by
      rw [Real.dimH_univ_eq_finrank]
      norm_num [Rotation, Module.finrank_prod, Module.finrank_pi_fintype]

private def zeroMixed : Set Ordinary := {p | (align p).2.2.2 = 0}

private theorem dimH_zeroMixed_le : dimH zeroMixed ≤ 6 := by
  rw [zeroMixed, ← image_zeroMixed]
  refine differentiable_zeroMixed.differentiableOn.dimH_image_le.trans_eq ?_
  rw [Real.dimH_univ_eq_finrank]
  norm_num [Module.finrank_prod, Complex.finrank_real_complex]

private def parametersOfOrdinary (p : Ordinary) : Parameters := ![p.1, p.2.1, p.2.2.1, p.2.2.2]

private theorem parametersOfOrdinary_asOrdinary (u : Parameters) :
    parametersOfOrdinary (asOrdinary u) = u := by
  funext i
  fin_cases i <;> rfl

private theorem differentiable_parametersOfOrdinary : Differentiable ℝ parametersOfOrdinary := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i <;> simp [parametersOfOrdinary] <;> fun_prop

private theorem criticalCoordinates_subset :
    criticalCoordinates ⊆ parametersOfOrdinary '' (zeroMixed ∪ physicalSliceImage) := by
  intro u hu
  obtain ⟨hsource, hrank⟩ := hu
  let p := asOrdinary u
  refine ⟨p, ?_, parametersOfOrdinary_asOrdinary u⟩
  by_cases hK : (align p).2.2.2 = 0
  · exact Or.inl hK
  · have hcoord : alignedSlice p 1 ≠ 0 :=
      (Real.sqrt_pos.2 (Complex.normSq_pos.2 hK)).ne'
    have hminor (i : Fin 10) :
        MvPolynomial.eval (fun j => (alignedSlice p j : ℂ)) (criticalMatrix Complex.I i).det = 0 :=
      not_ne_iff.mp (fun hm => hrank (injective_fderiv_graphReadout u hsource hK i hm))
    exact Or.inr (mem_physicalSliceImage p hK ⟨hcoord, hminor⟩)

private theorem dimH_criticalCoordinates_le : dimH criticalCoordinates ≤ 6 := by
  refine (dimH_mono criticalCoordinates_subset).trans
    (differentiable_parametersOfOrdinary.differentiableOn.dimH_image_le.trans ?_)
  rw [dimH_union]
  exact sup_le dimH_zeroMixed_le dimH_physicalSliceImage_le

private theorem dimH_chartCritical_le : dimH chartCritical ≤ 6 := by
  have he : Subtype.val '' chartCritical = (graph ∘ traceChart) '' criticalCoordinates := by
    rw [chartCritical, image_image]
    apply image_congr
    intro u hu
    have h : u ∈ chartDomain := hu.1
    change (chart.toFun u).val = graph (traceChart u)
    simp only [chart, dite_eq_left h]
  have hg : DifferentiableOn ℝ (graph ∘ traceChart) criticalCoordinates :=
    fun u hu => (analyticAt_chartGraph u hu.1).differentiableAt.differentiableWithinAt
  rw [← isometry_subtype_coe.dimH_image, he]
  exact hg.dimH_image_le.trans dimH_criticalCoordinates_le

theorem dimH_graphBadLocus_le : dimH graphBadLocus ≤ 6 := by
  rw [graphBadLocus_eq, dimH_union]
  exact sup_le dimH_chartBoundary_le dimH_chartCritical_le

#print axioms analyticAt_graphReadout
#print axioms isCompact_graphBadLocus
#print axioms dimH_graphBadLocus_le

end

end D5.S3.Quantum.TensorNetworks.SevenSiteGraphCriticalDimension
