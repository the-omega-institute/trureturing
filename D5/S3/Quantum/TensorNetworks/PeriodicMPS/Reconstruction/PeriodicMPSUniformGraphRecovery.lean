/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Uniform two-site recovery from a critical-locus dimension bound. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformGraphBoundary
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.CompactRegularFiberContinuation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformHardCoreCompactRecovery
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformLinearTraceLift
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Conditional generic recovery from the adjacent two-site marginal at every
period at least seven. The hypothesis concerns only the critical coordinates
of the normalized ordinary-chart observation. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformGraphRecovery

open Set Filter
open Function (Injective Surjective comp_apply)
open PeriodicMPSUniformCompactGraph
open PeriodicMPSUniformGraphBoundary (chartBoundary dimH_chartBoundary_le)
open PeriodicMPSCompactReadout (Readout readout)
open PeriodicMPSUniformHardCoreLocalization (twoSiteObservation witnessProjector)
open PeriodicMPSUniformDeterminantPencil (witnessCore)
open PeriodicMPSProjectiveCoordinates (projector mass mass_pos outer)
open SevenSiteTraceBase (Word amplitudeOfLength amplitudeOfLength_actual map_amplitudeOfLength)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped Topology ENNReal NNReal Matrix.Norms.Elementwise ComplexConjugate

open private weighted_ne_zero from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformCompactGraph

open private continuous_readColumn from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformLinearTraceLift

noncomputable section

variable {n m : ℕ}

private theorem source_eq_linear_lift (k : ℕ) :
    source (6 + k) = PeriodicMPSUniformLinearTraceLift.projectorSource k := by
  unfold source PeriodicMPSUniformLinearTraceLift.projectorSource
  congr 1
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨A, ht, hs, hd, he, hk⟩ :=
      PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates (p 0) (p 1) (p 2) (p 3) (p 4)
    have hcoords : (![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det,
        (A 0 * A 1).trace] : Invariants) = p := by
      funext i
      fin_cases i <;> assumption
    have hw := weighted_ne_zero (n := 6 + k) (by omega) hp
    refine ⟨A, ⟨?_, ?_⟩, ?_⟩
    · rw [← hcoords] at hw
      exact hw
    · change amplitudeOfLength (6 + k) p ≠ 0 at hp
      rw [← hcoords, amplitudeOfLength_actual] at hp
      exact hp
    · rw [← hcoords, graph_actual]
      rfl
  · rintro ⟨A, ⟨_, hA⟩, rfl⟩
    let p : Invariants := ![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det,
      (A 0 * A 1).trace]
    refine ⟨p, ?_, ?_⟩
    · change amplitudeOfLength (6 + k) p ≠ 0
      rw [amplitudeOfLength_actual]
      exact hA
    · rw [graph_actual]
      rfl

/-- The full-amplitude readout recovers the weighted projector by continuity
throughout its open guard in the compact graph. The zero column uses tail
length `k = n - 6`. -/
private theorem exists_open_lift_guard (k : ℕ) :
    ∃ W : Set (StateMatrix (6 + k)), IsOpen W ∧
      projector (traceWord 2 2 (6 + k) witnessCore) ∈ W ∧
      ∀ x y : Source (6 + k), x.val.2 ∈ W → x.val.2 = y.val.2 → x = y := by
  let column := PeriodicMPSUniformLinearTraceLift.readColumn k (fun _ => 0)
  let W := {P | column P ≠ 0}
  refine ⟨W, isOpen_ne_fun (continuous_readColumn k _) continuous_const,
    PeriodicMPSUniformLinearTraceLift.readColumn_witnessCore_ne_zero k, ?_⟩
  intro x y hx hxy
  have hy : column y.val.2 ≠ 0 := hxy ▸ hx
  have first_x := PeriodicMPSUniformLinearTraceLift.lift_eq_of_readColumn_ne_zero
    (source_eq_linear_lift k ▸ x.property) (fun _ => 0) hx
  have first_y := PeriodicMPSUniformLinearTraceLift.lift_eq_of_readColumn_ne_zero
    (source_eq_linear_lift k ▸ y.property) (fun _ => 0) hy
  exact Subtype.ext (Prod.ext (first_x.trans ((congrArg (projector ∘ column) hxy).trans
    first_y.symm)) hxy)

/-- Nine real Pauli coordinates of the literal normalized marginal on the compact graph. -/
def observe (m : ℕ) (x : Source (2 + m)) : Readout := readout (observation m x)

private theorem lipschitz_observe (m : ℕ) : ∃ K : ℝ≥0, LipschitzWith K (observe m) := by
  let Q := (twoSiteObservation m).toContinuousLinearMap
  have hP : LipschitzWith 1 (fun x : Source (2 + m) => x.val.2) := by
    intro x y
    change edist x.val.2 y.val.2 ≤
      (1 : ℝ≥0∞) * max (edist x.val.1 y.val.1) (edist x.val.2 y.val.2)
    rw [one_mul]
    exact le_max_right _ _
  exact ⟨_, readout.lipschitzWith.comp (Q.lipschitzWith.comp hP)⟩

private theorem observe_eq_iff (hn : 0 < 2 + m) (x y : Source (2 + m)) :
    observe m y = observe m x ↔ observation m y = observation m x :=
  PeriodicMPSCompactReadout.readout_eq_iff (physicalProjection hn x) (physicalProjection hn y)

/-- The compact hard-core reconstruction neighborhood supplies graph singleton
fibers on an open set after imposing the full-amplitude readout guard. -/
private theorem exists_open_graph_singletons (m : ℕ) (hn : 7 ≤ 2 + m) :
    ∃ U : Set (Source (2 + m)), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∀ y : Source (2 + m), observe m y = observe m x → y = x := by
  have hperiod : 2 + m = 6 + (m - 4) := by omega
  have hg := exists_open_lift_guard (m - 4)
  rw [← hperiod] at hg
  obtain ⟨W, hWo, hw, hlift⟩ := hg
  -- The hard-core witness input is `r = m - 2 = n - 4`.
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  obtain ⟨N, hNo, hcenter, G, hGo, hGd, hG⟩ :=
    PeriodicMPSUniformHardCoreCompactRecovery.exists_generic_compact_reconstruction r (by omega)
  let π := physicalProjection (n := 2 + (r + 2)) (by omega)
  let T : Set N := (Subtype.val ∘ Subtype.val) ⁻¹' W
  have hTo : IsOpen T := hWo.preimage (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨p, hpT, hpG⟩ := dense_iff_inter_open.mp hGd T hTo ⟨⟨_, hcenter⟩, hw⟩
  let S : Set (physical (2 + (r + 2))) := Subtype.val '' (G ∩ T)
  have hSo : IsOpen S := hNo.isOpenMap_subtype_val _ (hGo.inter hTo)
  have hπ : Function.Surjective π := surjective_physicalProjection _
  obtain ⟨x, hx⟩ := hπ p.val
  have hxS : π x ∈ S := by
    rw [hx]
    exact ⟨p, ⟨hpG, hpT⟩, rfl⟩
  refine ⟨π ⁻¹' S, hSo.preimage (continuous_physicalProjection _), ⟨x, hxS⟩, ?_⟩
  intro z hz y hy
  obtain ⟨q, ⟨hqG, hqW⟩, hq⟩ : π z ∈ S := hz
  have hobs := (observe_eq_iff (by omega) z y).mp hy
  have he := congrArg (fun P : physical (2 + (r + 2)) => twoSiteObservation (r + 2) P.val) hq
  have hstate := hG q hqG (π y) (hobs.trans he.symm)
  have hyz : y.val.2 = z.val.2 := hstate.trans (congrArg Subtype.val hq)
  have hzW : z.val.2 ∈ W := by
    change (π z).val ∈ W
    rw [← hq]
    exact hqW
  exact (hlift z y hzW hyz.symm).symm

private theorem chart_val (hn : 2 ≤ n) {u : Parameters} (hu : u ∈ (chart hn).source) :
    ((chart hn) u).val = graph n (traceChart u) := by
  have h : u ∈ chartDomain n := hu
  change ((chart hn).toPartialEquiv.toFun u).val = _
  unfold chart
  dsimp only
  rw [dite_eq_left h]

private theorem analyticAt_amplitude_real (n : ℕ) (p : Invariants) :
    AnalyticAt ℝ (amplitudeOfLength (R := ℂ) n) p := by
  apply AnalyticAt.pi
  intro w
  let a : MvPolynomial (Fin 5) ℂ := amplitudeOfLength n MvPolynomial.X w
  have h (q : Invariants) : MvPolynomial.eval q a = amplitudeOfLength n q w := by
    change MvPolynomial.eval q (amplitudeOfLength n MvPolynomial.X w) = _
    rw [map_amplitudeOfLength]
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

private theorem analyticAt_weighted (p : Invariants) : AnalyticAt ℝ weighted p := by
  have h (i : Fin 5) : AnalyticAt ℝ (fun q : Invariants => q i) p :=
    (ContinuousLinearMap.proj i : Invariants →L[ℝ] ℂ).analyticAt p
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (h 0).pow 2
  · exact (h 0).fun_mul (h 1)
  · exact (h 1).pow 2
  · exact h 2
  · exact h 3
  · exact h 4

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

private theorem analyticAt_chartGraph (hn : 0 < n) {u : Parameters}
    (hu : u ∈ chartDomain n) : AnalyticAt ℝ (graph n ∘ traceChart) u := by
  have ht := analyticAt_traceChart u
  have hw := (analyticAt_weighted (traceChart u)).comp ht
  have hT := (analyticAt_amplitude_real n (traceChart u)).comp ht
  have hP : AnalyticAt ℝ (fun v : Parameters => projector (weighted (traceChart v))) u :=
    (analyticAt_projector_real (weighted_ne_zero hn hu)).comp_of_eq hw rfl
  have hA : AnalyticAt ℝ (fun v : Parameters => projector (amplitudeOfLength n (traceChart v))) u :=
    (analyticAt_projector_real hu).comp_of_eq hT rfl
  exact hP.prod hA

/-- The actual normalized chart observation, extended by its formula to the
ambient coordinate space. The derivative is taken only on the ordinary domain. -/
def chartObservation (m : ℕ) (u : Parameters) : Readout :=
  readout (twoSiteObservation m (projector (amplitudeOfLength (2 + m) (traceChart u))))

theorem chartObservation_eqOn (hn : 2 ≤ 2 + m) :
    EqOn (chartObservation m) (observe m ∘ chart hn) (chart hn).source := by
  intro u hu
  change chartObservation m u = readout (twoSiteObservation m ((chart hn) u).val.2)
  rw [chart_val hn hu]
  rfl

set_option maxHeartbeats 1000000 in
theorem analyticAt_chartObservation {u : Parameters} (hu : u ∈ chartDomain (2 + m)) :
    AnalyticAt ℝ (chartObservation m) u := by
  let Q := ((twoSiteObservation m).toContinuousLinearMap).restrictScalars ℝ
  let a := amplitudeOfLength (2 + m) ∘ traceChart
  have hA : AnalyticAt ℝ a u :=
    (analyticAt_amplitude_real (2 + m) (traceChart u)).comp (analyticAt_traceChart u)
  have hP : AnalyticAt ℝ (fun v => projector (a v)) u :=
    (analyticAt_projector_real hu).comp_of_eq hA rfl
  have hQ : AnalyticAt ℝ (fun v => Q (projector (a v))) u :=
    (Q.analyticAt _).comp_of_eq hP rfl
  exact (readout.analyticAt _).comp_of_eq hQ rfl

private theorem analyticAt_decode {x : Ambient n} (hx : x.1 0 0 ≠ 0) :
    AnalyticAt ℂ decode x := by
  let M := Matrix (Fin 6) (Fin 6) ℂ
  let fst : Ambient n →L[ℂ] M := ContinuousLinearMap.fst ℂ M (StateMatrix n)
  let entry (i : Fin 6) : Ambient n →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (0 : Fin 6) : (Fin 6 → ℂ) →L[ℂ] ℂ).comp
      ((ContinuousLinearMap.proj i : M →L[ℂ] (Fin 6 → ℂ)).comp fst)
  have h (i : Fin 6) : AnalyticAt ℂ (fun y : Ambient n => y.1 i 0) x :=
    (entry i).analyticAt x
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (h 1).div (h 0) hx
  · exact (h 3).div (h 0) hx
  · exact (h 4).div (h 0) hx
  · exact (h 5).div (h 0) hx

private theorem exists_lipschitz_chart (hn : 2 ≤ n) (x : Source n) (hx : x ∈ (chart hn).target) :
    ∃ (c : OpenPartialHomeomorph Parameters (Source n)) (K : ℝ≥0),
      x ∈ c.target ∧ LipschitzOnWith K c.symm c.target ∧
      c.source ⊆ (chart hn).source ∧ (c : Parameters → Source n) = chart hn := by
  have hdiag : x.val.1 0 0 ≠ 0 := hx.1
  have hC : ContDiffAt ℂ 1 decode x.val := (analyticAt_decode hdiag).contDiffAt
  obtain ⟨K, M, hM, hLip⟩ := hC.exists_lipschitzOnWith
  obtain ⟨V, hVM, hVo, hxV⟩ := mem_nhds_iff.mp hM
  let T : Set (Source n) := Subtype.val ⁻¹' V
  let c := ((chart hn).symm.restrOpen T (hVo.preimage continuous_subtype_val)).symm
  have htarget : c.target = (chart hn).target ∩ T := rfl
  refine ⟨c, K, htarget.symm ▸ ⟨hx, hxV⟩, ?_, fun _ hu => hu.1, rfl⟩
  intro y hy z hz
  exact hLip (hVM (htarget ▸ hy).2) (hVM (htarget ▸ hz).2)

/-- Real rank defects of the actual normalized observation on the ordinary
trace-one chart of the length `2 + m` graph. -/
def criticalCoordinates (m : ℕ) : Set Parameters :=
  {u ∈ chartDomain (2 + m) | ¬ Injective (fderiv ℝ (chartObservation m) u)}

private def bad (hn : 2 ≤ 2 + m) : Set (Source (2 + m)) :=
  chartBoundary hn ∪ chart hn '' criticalCoordinates m

private theorem isClosed_bad (hn : 2 ≤ 2 + m) : IsClosed (bad hn) := by
  let U : Set Parameters := (chart hn).source ∩
    (fderiv ℝ (chartObservation m)) ⁻¹' {L : Parameters →L[ℝ] Readout | Injective L}
  have hd : ContinuousOn (fderiv ℝ (chartObservation m)) (chart hn).source :=
    fun u hu => (analyticAt_chartObservation hu).fderiv.continuousAt.continuousWithinAt
  have hU : IsOpen U :=
    hd.isOpen_inter_preimage (chart hn).open_source ContinuousLinearMap.isOpen_injective
  have he : (bad hn)ᶜ = chart hn '' U := by
    ext x
    constructor
    · intro hx
      have ht : x ∈ (chart hn).target := by
        by_contra h
        exact hx (Or.inl h)
      refine ⟨(chart hn).symm x, ⟨(chart hn).map_target ht, ?_⟩, (chart hn).right_inv ht⟩
      change Injective (fderiv ℝ (chartObservation m) ((chart hn).symm x))
      by_contra h
      exact hx (Or.inr ⟨_, ⟨(chart hn).map_target ht, h⟩, (chart hn).right_inv ht⟩)
    · rintro ⟨u, ⟨hu, hi⟩, rfl⟩ (hb | ⟨v, hv, he⟩)
      · exact hb ((chart hn).map_source hu)
      · have hvu := (chart hn).injOn hv.1 hu he
        exact hv.2 (hvu.symm ▸ hi)
  exact isOpen_compl_iff.mp (he ▸ (chart hn).isOpen_image_of_subset_source hU inter_subset_left)

private theorem dimH_bad_le (hn : 2 ≤ 2 + m) (hcrit : dimH (criticalCoordinates m) ≤ 6) :
    dimH (bad hn) ≤ 6 := by
  have he : Subtype.val '' (chart hn '' criticalCoordinates m) =
      (graph (2 + m) ∘ traceChart) '' criticalCoordinates m := by
    rw [image_image]
    exact image_congr (fun _ hu => chart_val hn hu.1)
  have hd : DifferentiableOn ℝ (graph (2 + m) ∘ traceChart) (criticalCoordinates m) :=
    fun _ hu => (analyticAt_chartGraph (by omega) hu.1).differentiableAt.differentiableWithinAt
  unfold bad
  rw [dimH_union, ← isometry_subtype_coe.dimH_image (s := chart hn '' criticalCoordinates m), he]
  exact sup_le (dimH_chartBoundary_le hn) (hd.dimH_image_le.trans hcrit)

private theorem finrank_parameters : Module.finrank ℝ Parameters = 8 := by
  norm_num [Parameters, Module.finrank_pi_fintype, Complex.finrank_real_complex]

private theorem open_dense_graph_recovery (m : ℕ) (hn : 7 ≤ 2 + m)
    (hcrit : dimH (criticalCoordinates m) ≤ 6) :
    let h₂ : 2 ≤ 2 + m := by omega
    let G := {x ∈ observe m ⁻¹' (observe m '' bad h₂)ᶜ |
      ∀ y : Source (2 + m), observe m y = observe m x → y = x}
    IsOpen G ∧ Dense G := by
  let h₂ : 2 ≤ 2 + m := by omega
  let graphCompact : CompactSpace (Source (2 + m)) := compactSpace_source (by omega)
  obtain ⟨K, hK⟩ := lipschitz_observe m
  have hcover : (bad h₂)ᶜ ⊆ (chart h₂).target := by
    intro x hx
    by_contra hn
    exact hx (Or.inl hn)
  have hdim : Module.finrank ℝ Readout = Module.finrank ℝ Parameters + 1 := by
    rw [finrank_parameters]
    norm_num [Readout, Module.finrank_pi_fintype]
  refine @PeriodicMPSCompactAnalyticCharts.compact_generic_recovery_of_dimH_bad
    Parameters Readout _ _ _ _ _ _ (Source (2 + m)) _ graphCompact (observe m) K hK
    (chart h₂).target (bad h₂) (chart h₂).open_target
    (chart_target_pathConnected h₂).isConnected (chart_target_dense h₂)
    hcover (isClosed_bad h₂).isCompact (by rw [finrank_parameters]; decide)
    (by simpa [finrank_parameters] using dimH_bad_le h₂ hcrit) hdim ?_ ?_
  · intro x hx
    obtain ⟨c, L, hxc, hLip, hsub, hc⟩ := exists_lipschitz_chart h₂ x hx
    refine ⟨c, L, chartObservation m, hxc, hLip, ?_, ?_⟩
    · intro u hu
      rw [chartObservation_eqOn h₂ (hsub hu)]
      exact congrArg (observe m) (congrFun hc u).symm
    · intro u hu huB
      have he : c u = chart h₂ u := congrFun hc u
      refine ⟨analyticAt_chartObservation (hsub hu), ?_⟩
      by_contra h
      exact huB (Or.inr ⟨u, ⟨hsub hu, h⟩, he.symm⟩)
  · intro hDense
    obtain ⟨U, hUo, hUne, hU⟩ := exists_open_graph_singletons m hn
    obtain ⟨x, hxU, hxGood⟩ := dense_iff_inter_open.mp hDense U hUo hUne
    exact ⟨x, hxGood, hU x hxU⟩

set_option maxHeartbeats 1000000 in
/-- For each physical period `n = 2 + m ≥ 7`, a real Hausdorff dimension bound
on the critical set yields a relatively Euclidean-open dense subset of actual
projectors, identified by a single adjacent marginal against every compact
competitor. Here `m = n - 2` is the number of traced-out sites. -/
theorem generic_twoSite_recovery (m : ℕ) (hn : 7 ≤ 2 + m)
    (hcrit : dimH (criticalCoordinates m) ≤ 6) :
    ∃ D : Set (physical (2 + m)), IsOpen D ∧ Dense D ∧ ∀ P ∈ D,
      P.val ∈ actualProjectors (2 + m) ∧ ∀ Q : physical (2 + m),
        twoSiteObservation m Q.val = twoSiteObservation m P.val → Q = P := by
  let h₂ : 2 ≤ 2 + m := by omega
  let hpos : 0 < 2 + m := by omega
  let graphCompact : CompactSpace (Source (2 + m)) := compactSpace_source hpos
  let π := physicalProjection hpos
  let G : Set (Source (2 + m)) :=
    {x ∈ observe m ⁻¹' (observe m '' bad h₂)ᶜ |
      ∀ y : Source (2 + m), observe m y = observe m x → y = x}
  obtain ⟨hGo, hGd⟩ : IsOpen G ∧ Dense G := open_dense_graph_recovery m hn hcrit
  have hsat : π ⁻¹' (π '' G) = G := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      have hstate : y.val.2 = x.val.2 := congrArg Subtype.val he
      have hobs : observation m x = observation m y :=
        congrArg (twoSiteObservation m) hstate.symm
      have hxy : x = y := hy.2 x ((observe_eq_iff hpos y x).mpr hobs)
      rwa [hxy]
    · exact fun hx => ⟨x, hx, rfl⟩
  have hc : Continuous π := continuous_physicalProjection hpos
  have hs : Surjective π := surjective_physicalProjection hpos
  have hquot := hc.isClosedMap.isQuotientMap hc hs
  have hpre : IsOpen (π ⁻¹' (π '' G)) := by rwa [hsat]
  refine ⟨π '' G, hquot.isCoinducing.isOpen_preimage.mp hpre,
    hs.denseRange.dense_image hc hGd, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, fun Q hQ => ?_⟩
  · have hxB : x ∉ bad h₂ := fun hb => hx.1 ⟨x, hb, rfl⟩
    have hxt : x ∈ (chart h₂).target := by
      by_contra hn
      exact hxB (Or.inl hn)
    let u := (chart h₂).symm x
    have hu : u ∈ (chart h₂).source := (chart h₂).map_target hxt
    have he : chart h₂ u = x := (chart h₂).right_inv hxt
    change x.val.2 ∈ actualProjectors (2 + m)
    rw [← image_graph_snd, ← he, chart_val h₂ hu]
    exact ⟨graph (2 + m) (traceChart u), ⟨traceChart u, hu, rfl⟩, rfl⟩
  · obtain ⟨y, rfl⟩ := hs Q
    have hmarginal : observation m y = observation m x := hQ
    have hyx : y = x := hx.2 y ((observe_eq_iff hpos x y).mpr hmarginal)
    exact congrArg π hyx

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformGraphRecovery
