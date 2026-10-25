import CFMPActualPositiveConvex284Transient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Instances.Matrix

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalVolume)
open CFMPActualExtendedAngle268Transient (positiveLengths positiveLengths_open)
open CFMPGlobalGenuineCovolume256Transient (realizedFamily)
open CFMPOriginalVolumeChoice255Transient (originalContract)
open CFMPActualNativeMass435Transient (referenceMass original_native_mass_eq_reference)
open CFMPOriginalFrameDensity435Transient (originalDensity)
open CFMPActualCellMotion435Transient (cellPoint)
open CFMPOriginalCellsIndependent435Transient (edgeMatrix)
open CFMPOriginalCellKernel435Transient (vertices_smooth edgeMatrix_smooth)
open CFMPActualNativeCellMotion435Transient (lift_cellPoint_mem_body)
open CFMPCompactKernelTube435Transient (V delta delta_compact)
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicNormalizedDensity
open D5.S3.Geometry.HyperbolicTopology

namespace CFMPActualPositiveVolume285Transient

private local instance : MeasurableSpace Native3 := borel _
private local instance : BorelSpace Native3 := ⟨rfl⟩

def cellKernel (n : Fin 20) (z : Lengths × V) : ℝ :=
  |(edgeMatrix z.1 n).det| * originalDensity z.1 (cellPoint z.1 n z.2)

theorem lengthGram_continuous : Continuous lengthGram := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp only [lengthGram] <;> fun_prop

theorem cellPoint_continuous (n : Fin 20) :
    Continuous (fun z : Lengths × V => cellPoint z.1 n z.2) := by
  have hv (j : Fin 4) (i : Fin 3) :
      Continuous (fun z : Lengths × V =>
        D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices z.1 n j i.castSucc) :=
    ((continuous_apply i.castSucc).comp (vertices_smooth n j).continuous).comp continuous_fst
  apply continuous_pi
  intro i
  change Continuous (fun z : Lengths × V =>
    D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices z.1 n 0 i.castSucc +
      ∑ j : Fin 3,
        (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices z.1 n j.succ i.castSucc -
          D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices z.1 n 0 i.castSucc) * z.2 j)
  exact (hv 0 i).add (continuous_finsetSum _ (fun j _ =>
    ((hv j.succ i).sub (hv 0 i)).mul ((continuous_apply j).comp continuous_snd)))

theorem cellKernel_continuousAt (n : Fin 20) (a : Lengths)
    (ha : a ∈ positiveLengths) (u : V) (hu : u ∈ delta) :
    ContinuousAt (cellKernel n) (a,u) := by
  have hcell := cellPoint_continuous n
  have hlift : Continuous (fun z : Lengths × V =>
      CFMPFrameMotion435Transient.lift (cellPoint z.1 n z.2)) := by
    apply continuous_pi
    intro i
    have hc (j : Fin 3) := (continuous_apply j).comp hcell
    fin_cases i <;> simp only [CFMPFrameMotion435Transient.lift] <;> fun_prop
  have hq : Continuous (fun z : Lengths × V =>
      -gramQuadratic z.1 (CFMPFrameMotion435Transient.lift (cellPoint z.1 n z.2))) := by
    have hG (i j : Fin 4) :
        Continuous (fun z : Lengths × V => lengthGram z.1 i j) :=
      ((continuous_apply j).comp ((continuous_apply i).comp lengthGram_continuous)).comp
        continuous_fst
    have hv (i : Fin 4) := (continuous_apply i).comp hlift
    unfold gramQuadratic
    exact (continuous_finsetSum _ (fun i _ => (hv i).mul
      (continuous_finsetSum _ (fun j _ => (hG i j).mul (hv j))))).neg
  have hqpos : 0 < -gramQuadratic a
      (CFMPFrameMotion435Transient.lift (cellPoint a n u)) :=
    neg_pos.mpr ((shared_radial_body a ha).2.2.2.1 _
      (lift_cellPoint_mem_body a ha n u hu))
  have hdet : Continuous (fun z : Lengths × V => |(edgeMatrix z.1 n).det|) :=
    ((edgeMatrix_smooth n).continuous.matrix_det.abs).comp continuous_fst
  have hroot : Continuous (fun z : Lengths × V => Real.sqrt (-(lengthGram z.1).det)) :=
    (lengthGram_continuous.matrix_det.neg.sqrt).comp continuous_fst
  exact hdet.continuousAt.mul
    (hroot.continuousAt.div (hq.continuousAt.pow 2) (pow_ne_zero 2 hqpos.ne'))

/-- Compact reference cells control the density even when a geometric frame degenerates. -/
theorem cellIntegral_continuousAt (n : Fin 20) (a : Lengths)
    (ha : a ∈ positiveLengths) :
    ContinuousAt (fun b : Lengths => ∫ u in delta, cellKernel n (b,u)) a := by
  obtain ⟨ε,hε,hball⟩ := (Metric.nhds_basis_closedBall (x := a)).mem_iff.mp
    (positiveLengths_open.mem_nhds ha)
  have hcompact : IsCompact (Metric.closedBall a ε ×ˢ delta) :=
    (isCompact_closedBall a ε).prod delta_compact
  have hcont : ContinuousOn (cellKernel n) (Metric.closedBall a ε ×ˢ delta) := by
    intro z hz
    exact (cellKernel_continuousAt n z.1 (hball hz.1) z.2 hz.2).continuousWithinAt
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  have hmeas : ∀ᶠ b in 𝓝 a,
      AEStronglyMeasurable (fun u => cellKernel n (b,u)) (volume.restrict delta) := by
    filter_upwards [positiveLengths_open.mem_nhds ha] with b hb
    have hc : ContinuousOn (fun u => cellKernel n (b,u)) delta := by
      intro u hu
      exact ((cellKernel_continuousAt n b hb u hu).comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
    exact hc.aestronglyMeasurable delta_compact.measurableSet
  apply continuousAt_of_dominated (F := fun b : Lengths => fun u : V => cellKernel n (b,u))
    (bound := fun _ : V => C) hmeas
  · filter_upwards [Metric.closedBall_mem_nhds a hε] with b hb
    filter_upwards [ae_restrict_mem delta_compact.measurableSet] with u hu
    exact hC (b,u) ⟨hb,hu⟩
  · exact integrableOn_const delta_compact.measure_ne_top
  · filter_upwards [ae_restrict_mem delta_compact.measurableSet] with u hu
    have hc : ContinuousAt (fun b : Lengths => (b,u)) a :=
      continuousAt_id.prodMk continuousAt_const
    exact (cellKernel_continuousAt n a ha u hu).comp (f := fun b : Lengths => (b,u)) (x := a) hc

theorem referenceMass_continuousAt (a : Lengths) (ha : a ∈ positiveLengths) :
    ContinuousAt referenceMass a := by
  unfold referenceMass
  exact tendsto_finsetSum _ (fun n _ => cellIntegral_continuousAt n a ha)

theorem referenceMass_eq_zero_of_det_nonneg (a : Lengths)
    (hd : 0 ≤ (lengthGram a).det) : referenceMass a = 0 := by
  have hroot : Real.sqrt (-(lengthGram a).det) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hd)
  simp [referenceMass,originalDensity,hroot]

theorem physicalVolume_eq_reference (G : RealizationFamily) (hG : realizedFamily G)
    (a : Lengths) (ha : CFMPGenuineLengthNeighborhood435Transient.genuine a) :
    physicalVolume G a = referenceMass a := by
  obtain ⟨M,hM,hGi,hGc⟩ := hG a ha
  obtain ⟨N,f,hN,_,hfi,hcompact,hsource⟩ :=
    CFMPGenuineLengthNeighborhood435Transient.genuine_realization_exists a ha
  have heq := CFMPOriginalVolumeChoice255Transient.original_normalized_volume_independent
    a M N hM hN (G a) f hGi hGc hsource
  let d : ℕ := 3
  let aH : NNReal := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Measure.hausdorffMeasure (d : ℝ))
  let c : ℝ≥0∞ := (aH : ℝ≥0∞)⁻¹
  have hm : c⁻¹ • rawNativeMeasure =
      (Measure.euclideanHausdorffMeasure 3 : Measure Native3) := by
    dsimp only [c]
    rw [inv_inv,Measure.coe_nnreal_smul]
    rfl
  have hcal := CFMPOriginalNormalizedVolume435Transient.normalized_native_h3_density
  rw [← hm] at hcal
  unfold physicalVolume
  rw [heq]
  simpa only [hm] using
    original_native_mass_eq_reference c hcal N a ha.1 hN f hfi hcompact hsource

theorem physicalVolume_tendsto_zero
    {ι : Type*} {L : Filter ι} (a : ι → Lengths) (p : Lengths)
    (hp : p ∈ positiveLengths) (hd : (lengthGram p).det = 0)
    (ha : Tendsto a L (𝓝 p)) (hg : ∀ᶠ i in L,
      CFMPGenuineLengthNeighborhood435Transient.genuine (a i))
    (G : RealizationFamily) (hG : realizedFamily G) :
    Tendsto (fun i => physicalVolume G (a i)) L (𝓝 0) := by
  have h := (referenceMass_continuousAt p hp).tendsto.comp ha
  rw [referenceMass_eq_zero_of_det_nonneg p hd.ge] at h
  exact h.congr' (hg.mono (fun i hi => (physicalVolume_eq_reference G hG (a i) hi).symm))

end CFMPActualPositiveVolume285Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualPositiveVolume285Transient.referenceMass_continuousAt,
      ``CFMPActualPositiveVolume285Transient.physicalVolume_eq_reference,
      ``CFMPActualPositiveVolume285Transient.physicalVolume_tendsto_zero] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP285 actual positive flat-volume bridge absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP285 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP285 CHECKED {name} axioms={axioms}"
