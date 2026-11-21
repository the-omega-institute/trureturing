/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphContinuation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphContinuation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Continuation from the hard-core fiber to actual seven-site states. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteActualSourceChart
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLinearTraceLift
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.CompactRegularFiberContinuation
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! The hard-core singleton lifts to the compact seven-site graph. A compact
codimension-two set containing the boundary and chart rank defects then yields
generic recovery of actual states against the full compact state source. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteGraphContinuation

open Set Filter
open Function (Injective comp_apply)
open SevenSiteCompactGraph SevenSiteGraphReadout
open SevenSiteTraceBase (amplitude amplitude_actual map_amplitude)
open SevenSiteLinearTraceLift (readColumn continuous_readColumn graph_lift_unique)
open SevenSiteGraphBoundary (chartBoundary)
open PeriodicMPSCompactReadout (Readout readout)
open PeriodicMPSUniformHardCoreLocalization
open PeriodicMPSUniformDeterminantPencil (witnessCore)
open PeriodicMPSUniformHardCorePencilDecoder (witnessTensor)
open PeriodicMPSProjectiveCoordinates
  (projector projector_diag_ne_zero_iff projector_scale continuousAt_projector mass mass_pos outer)
open scoped Topology ENNReal NNReal Matrix.Norms.Elementwise ComplexConjugate

open private readColumn_graph from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLinearTraceLift

open private vacuum witnessTensor_vacuum from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization

noncomputable section

private theorem center_contrast_ne_zero :
    readColumn (vacuum 5) SevenSiteActualSourceChart.center.val 0 ≠ 0 := by
  let p : Invariants := ![1, 0, 0, 0, 1]
  have hc : (![ (witnessCore 0).trace, (witnessCore 1).trace,
      (witnessCore 0).det, (witnessCore 1).det,
      (witnessCore 0 * witnessCore 1).trace] : Invariants) = p := by
    funext i
    fin_cases i <;>
      norm_num [p, witnessCore, Matrix.trace_fin_two, Matrix.det_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hA : amplitude p = witnessTensor 7 := by
    rw [← hc, amplitude_actual]
    rfl
  have hP : SevenSiteActualSourceChart.center.val = (SevenSiteCompactGraph.graph p).2 := by
    change projector (witnessTensor 7) = projector (amplitude p)
    rw [hA]
  have hvac : amplitude p (vacuum 5) = 1 := by
    rw [hA]
    exact witnessTensor_vacuum (m := 5) (by decide)
  have hn : amplitude p ≠ 0 := fun h => one_ne_zero (hvac.symm.trans (congrFun h _))
  have hm : mass (amplitude p) ≠ 0 := (mass_pos _ hn).ne'
  rw [hP, readColumn_graph]
  simpa [hvac, p, SevenSiteLinearTraceLift.commutatorSquare, weighted, Pi.smul_apply,
    smul_eq_mul] using (Complex.ofReal_ne_zero.mpr (inv_ne_zero hm))

/-- The full-state projection is injective over an open neighborhood of the
hard-core witness inside the compact trace graph. -/
theorem exists_state_injOn_near_center :
    ∃ W : Set ProjectorSource, IsOpen W ∧ SevenSiteActualSourceChart.center ∈ W ∧ InjOn state (state ⁻¹' W) := by
  let W : Set ProjectorSource := {P | readColumn (vacuum 5) P.val 0 ≠ 0}
  have hcontinuous : Continuous (fun P : ProjectorSource => readColumn (vacuum 5) P.val 0) :=
    (continuous_apply _).comp ((continuous_readColumn _).comp continuous_subtype_val)
  refine ⟨W, isOpen_ne_fun hcontinuous continuous_const, center_contrast_ne_zero, ?_⟩
  intro x hx y _ hxy
  exact Subtype.ext (graph_lift_unique x.property y.property (vacuum 5) hx
    (congrArg Subtype.val hxy))

/-- The literal hard-core observation has one lift even on the compact graph. -/
theorem exists_hardCore_graph_singleton :
    ∃ x : Source, state x = SevenSiteActualSourceChart.center ∧ ∀ y : Source, observe y = observe x → y = x := by
  obtain ⟨W, _, hw, hinj⟩ := exists_state_injOn_near_center
  obtain ⟨x, hx⟩ := surjective_state SevenSiteActualSourceChart.center
  refine ⟨x, hx, fun y hy => ?_⟩
  have hobs := (graph_readout_eq_iff x y).mp hy
  have hstate : state y = SevenSiteActualSourceChart.center := by
    apply Subtype.ext
    change y.val.2 = witnessProjector 5
    apply eq_witnessProjector_of_mem_closure (m := 5) (by decide) (state y).property
    have hxval : x.val.2 = witnessProjector 5 := congrArg Subtype.val hx
    rw [hxval] at hobs
    exact hobs.trans (twoSiteObservation_traceWord (m := 5) witnessCore)
  have hyW : state y ∈ W := hstate.symm ▸ hw
  have hxW : state x ∈ W := hx.symm ▸ hw
  exact hinj hyW hxW (hstate.trans hx.symm)

/-- An open part of the compact graph consists of singleton fibers. This permits
choosing the continuation witness in any dense good locus. -/
theorem exists_open_graph_singletons :
    ∃ U : Set Source, IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∀ y : Source, observe y = observe x → y = x := by
  obtain ⟨W, hWo, hw, hinj⟩ := exists_state_injOn_near_center
  obtain ⟨N, hNo, hcenter, G, hGo, hGd, hG⟩ :=
    PeriodicMPSUniformHardCoreCompactRecovery.exists_generic_compact_reconstruction 3 (by decide)
  have hcenterN : SevenSiteActualSourceChart.center ∈ N := hcenter
  let T : Set N := Subtype.val ⁻¹' W
  have hTo : IsOpen T := hWo.preimage continuous_subtype_val
  obtain ⟨p, hpT, hpG⟩ := dense_iff_inter_open.mp hGd T hTo ⟨⟨SevenSiteActualSourceChart.center, hcenterN⟩, hw⟩
  let S : Set ProjectorSource := Subtype.val '' (G ∩ T)
  have hSo : IsOpen S := hNo.isOpenMap_subtype_val _ (hGo.inter hTo)
  obtain ⟨x, hx⟩ := surjective_state p.val
  let U := state ⁻¹' S
  have hxU : x ∈ U := by
    change state x ∈ S
    rw [hx]
    exact ⟨p, ⟨hpG, hpT⟩, rfl⟩
  refine ⟨U, hSo.preimage continuous_state, ⟨x, hxU⟩, ?_⟩
  intro z hz y hy
  obtain ⟨q, ⟨hqG, hqW⟩, hq⟩ : state z ∈ S := hz
  have hobs := (graph_readout_eq_iff z y).mp hy
  have hstate : state y = state z := by
    apply Subtype.ext
    exact (hG q hqG (state y) (hobs.trans (congrArg
      (fun P : ProjectorSource => twoSiteObservation 5 P.val) hq).symm)).trans
        (congrArg Subtype.val hq)
  have hzW : state z ∈ W := hq ▸ hqW
  have hyW : state y ∈ W := hstate.symm ▸ hzW
  exact hinj hyW hzW hstate

private theorem chart_val {u : Parameters} (hu : u ∈ chart.source) :
    (chart u).val = graph (traceChart u) := by
  have hu' : u ∈ chartDomain := hu
  change (chart.toPartialEquiv.toFun u).val = _
  unfold chart
  dsimp only
  rw [dif_pos hu']

private theorem analyticAt_amplitude_real (p : Invariants) :
    AnalyticAt ℝ (amplitude (R := ℂ)) p := by
  apply AnalyticAt.pi
  intro w
  let a : MvPolynomial (Fin 5) ℂ := amplitude MvPolynomial.X w
  have h (q : Invariants) : MvPolynomial.eval q a = amplitude q w := by
    change MvPolynomial.eval q (amplitude MvPolynomial.X w) = _
    rw [map_amplitude]
    congr 1
    funext i
    exact MvPolynomial.eval_X (f := q) i
  have ha : AnalyticAt ℝ (fun q : Invariants => MvPolynomial.eval q a) p :=
    AnalyticOnNhd.eval_continuousLinearMap'
      (fun i : Fin 5 => (ContinuousLinearMap.proj i : Invariants →L[ℝ] ℂ)) a p (mem_univ _)
  simpa only [h] using ha

private theorem analyticAt_traceChart (u : Parameters) : AnalyticAt ℝ traceChart u := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj (0 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u
  · exact (ContinuousLinearMap.proj (1 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u
  · exact (ContinuousLinearMap.proj (2 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u
  · exact (ContinuousLinearMap.proj (3 : Fin 4) : Parameters →L[ℝ] ℂ).analyticAt u

private theorem analyticAt_projector_real {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (ha : a ≠ 0) : AnalyticAt ℝ projector a := by
  have h (i : ι) : AnalyticAt ℝ (fun p : ι → ℂ => p i) a :=
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).analyticAt a
  have hconj (i : ι) : AnalyticAt ℝ (fun p : ι → ℂ => conj (p i)) a :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt (a i)).comp_of_eq (h i) rfl
  have hm : AnalyticAt ℝ mass a := by
    unfold mass
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have he (z : ℂ) : Complex.normSq z = (z * conj z).re := by
      simp [Complex.normSq_apply, Complex.mul_re]
    simp_rw [he]
    exact (Complex.reCLM.analyticAt _).comp_of_eq ((h i).fun_mul (hconj i)) rfl
  have ho : AnalyticAt ℝ outer a := by
    change AnalyticAt ℝ (fun p : ι → ℂ => fun i j => p i * conj (p j)) a
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    exact (h i).fun_mul (hconj j)
  exact (hm.inv (mass_pos _ ha).ne').smul ho

/-- The ordinary-chart readout is real analytic at every nonzero trace amplitude. -/
theorem analyticAt_chart_readout {u : Parameters} (hu : u ∈ chart.source) :
    AnalyticAt ℝ (observe ∘ chart) u := by
  let f : Parameters → Readout := fun p =>
    readout (twoSiteObservation 5 (projector (amplitude (traceChart p))))
  let Q := ((twoSiteObservation 5).toContinuousLinearMap).restrictScalars ℝ
  have hA := (analyticAt_amplitude_real (traceChart u)).comp (analyticAt_traceChart u)
  have hp : AnalyticAt ℝ (fun p : Parameters => projector (amplitude (traceChart p))) u :=
    (analyticAt_projector_real (a := amplitude (traceChart u)) hu).comp_of_eq hA rfl
  have hq : AnalyticAt ℝ (fun p : Parameters => Q (projector (amplitude (traceChart p)))) u :=
    (Q.analyticAt _).comp_of_eq hp rfl
  have hf : AnalyticAt ℝ f u :=
    (readout.analyticAt _).comp_of_eq hq rfl
  apply hf.congr
  filter_upwards [chart.open_source.mem_nhds hu] with p hp
  change f p = readout (twoSiteObservation 5 (chart p).val.2)
  rw [chart_val hp] <;> rfl

private theorem analyticAt_graph_decode {x : Ambient} (hx : x.1 0 0 ≠ 0) :
    AnalyticAt ℂ SevenSiteCompactGraph.decode x := by
  let M := Matrix (Fin 6) (Fin 6) ℂ
  let fst : Ambient →L[ℂ] M := ContinuousLinearMap.fst ℂ M (StateMatrix 5)
  let entry (i : Fin 6) : Ambient →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (0 : Fin 6) : (Fin 6 → ℂ) →L[ℂ] ℂ).comp
      ((ContinuousLinearMap.proj i : M →L[ℂ] (Fin 6 → ℂ)).comp fst)
  have he (i : Fin 6) : AnalyticAt ℂ (fun y : Ambient => y.1 i 0) x :=
    (entry i).analyticAt x
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (he 1).div (he 0) hx
  · exact (he 3).div (he 0) hx
  · exact (he 4).div (he 0) hx
  · exact (he 5).div (he 0) hx

private theorem exists_lipschitz_chart (x : Source) (hx : x ∈ chart.target) :
    ∃ (c : OpenPartialHomeomorph Parameters Source) (K : ℝ≥0),
      x ∈ c.target ∧ LipschitzOnWith K c.symm c.target ∧
      c.source ⊆ chart.source ∧ (c : Parameters → Source) = chart := by
  have hdiag : x.val.1 0 0 ≠ 0 := hx.1
  have hC : ContDiffAt ℂ 1 SevenSiteCompactGraph.decode x.val :=
    (analyticAt_graph_decode hdiag).contDiffAt
  obtain ⟨K, M, hM, hLip⟩ := hC.exists_lipschitzOnWith
  obtain ⟨V, hVM, hVo, hxV⟩ := mem_nhds_iff.mp hM
  let T : Set Source := Subtype.val ⁻¹' V
  let c := (chart.symm.restrOpen T (hVo.preimage continuous_subtype_val)).symm
  have htarget : c.target = chart.target ∩ T := rfl
  refine ⟨c, K, htarget.symm ▸ ⟨hx, hxV⟩, ?_, fun _ hu => hu.1, rfl⟩
  intro y hy z hz
  exact hLip (hVM (htarget ▸ hy).2) (hVM (htarget ▸ hz).2)

private theorem finrank_parameters : Module.finrank ℝ Parameters = 8 := by
  norm_num [Parameters, Module.finrank_pi_fintype, Complex.finrank_real_complex]

/-- The continuation input is a compact set of Hausdorff dimension at most six
that contains the chart boundary and every intrinsic chart-rank defect. -/
theorem open_dense_graph_recovery {B : Set Source} (hBc : IsCompact B) (hB : dimH B ≤ 6)
    (hboundary : chartBoundary ⊆ B)
    (hrank : ∀ u ∈ chart.source, chart u ∉ B →
      Injective (fderiv ℝ (observe ∘ chart) u)) :
    IsOpen {x ∈ observe ⁻¹' (observe '' B)ᶜ | ∀ y : Source, observe y = observe x → y = x} ∧
    Dense {x ∈ observe ⁻¹' (observe '' B)ᶜ | ∀ y : Source, observe y = observe x → y = x} := by
  let graphCompact : CompactSpace Source := isCompact_iff_compactSpace.mp source_isCompact
  obtain ⟨K, hK⟩ := lipschitz_observe
  have hcover : Bᶜ ⊆ chart.target := by
    intro x hx
    by_contra hn
    exact hx (hboundary hn)
  have hdim : Module.finrank ℝ Readout = Module.finrank ℝ Parameters + 1 := by
    rw [finrank_parameters]
    norm_num [Readout, Module.finrank_pi_fintype]
  refine @PeriodicMPSCompactAnalyticCharts.compact_generic_recovery_of_dimH_bad
    Parameters Readout _ _ _ _ _ _ Source _ graphCompact observe K hK
    chart.target B chart.open_target chart_target_pathConnected.isConnected chart_target_dense
    hcover hBc (by rw [finrank_parameters]; decide) (by simpa [finrank_parameters] using hB)
    hdim ?_ ?_
  · intro x hx
    obtain ⟨c, L, hxc, hLip, hsub, hc⟩ := exists_lipschitz_chart x hx
    refine ⟨c, L, observe ∘ chart, hxc, hLip, ?_, ?_⟩
    · intro u _
      exact congrArg observe (congrFun hc u).symm
    · intro u hu huB
      have he : c u = chart u := congrFun hc u
      exact ⟨analyticAt_chart_readout (hsub hu),
        hrank u (hsub hu) (he ▸ huB)⟩
  · intro hDense
    obtain ⟨U, hUo, hUne, hU⟩ := exists_open_graph_singletons
    obtain ⟨x, hxU, hxGood⟩ := dense_iff_inter_open.mp hDense U hUo hUne
    exact ⟨x, hxGood, hU x hxU⟩

/-- Generic points may be taken to be actual trace-word states. Their two-site
observations identify them against every state in the compact closure. -/
theorem exists_open_dense_actual_state_recovery {B : Set Source}
    (hBc : IsCompact B) (hB : dimH B ≤ 6) (hboundary : chartBoundary ⊆ B)
    (hrank : ∀ u ∈ chart.source, chart u ∉ B →
      Injective (fderiv ℝ (observe ∘ chart) u)) :
    ∃ D : Set ProjectorSource, IsOpen D ∧ Dense D ∧ ∀ P ∈ D,
      P.val ∈ actualProjectors 5 ∧ ∀ Q : ProjectorSource,
        twoSiteObservation 5 Q.val = twoSiteObservation 5 P.val → Q = P := by
  let G : Set Source :=
    {x ∈ observe ⁻¹' (observe '' B)ᶜ | ∀ y : Source, observe y = observe x → y = x}
  obtain ⟨hGo, hGd⟩ : IsOpen G ∧ Dense G := open_dense_graph_recovery hBc hB hboundary hrank
  have hsat : state ⁻¹' (state '' G) = G := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      have hs : observe y = observe x :=
        congrArg (fun P : ProjectorSource => readout (twoSiteObservation 5 P.val)) he
      exact (hy.2 x hs.symm) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have hquot := continuous_state.isClosedMap.isQuotientMap continuous_state surjective_state
  have hpre : IsOpen (state ⁻¹' (state '' G)) := by rwa [hsat]
  refine ⟨state '' G, hquot.isCoinducing.isOpen_preimage.mp hpre,
    surjective_state.denseRange.dense_image continuous_state hGd, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, fun Q hQ => ?_⟩
  · have hxB : x ∉ B := fun hb => hx.1 ⟨x, hb, rfl⟩
    have hxt : x ∈ chart.target := by
      by_contra hn
      exact hxB (hboundary hn)
    let u := chart.symm x
    have hu : u ∈ chart.source := chart.map_target hxt
    have he : chart u = x := chart.right_inv hxt
    have hxA : x.val.2 ∈ Prod.snd '' (graph '' defined) := by
      rw [← he, chart_val hu]
      exact ⟨graph (traceChart u), ⟨traceChart u, hu, rfl⟩, rfl⟩
    rw [image_graph_snd] at hxA
    obtain ⟨A, hA, heA⟩ := hxA
    exact ⟨A, hA, heA.symm⟩
  · obtain ⟨y, rfl⟩ := surjective_state Q
    exact congrArg state (hx.2 y ((graph_readout_eq_iff x y).mpr hQ))

#print axioms exists_hardCore_graph_singleton
#print axioms open_dense_graph_recovery
#print axioms exists_open_dense_actual_state_recovery

end

end D5.S3.Quantum.TensorNetworks.SevenSiteGraphContinuation
