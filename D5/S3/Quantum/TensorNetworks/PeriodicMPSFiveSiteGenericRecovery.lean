/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteGenericRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteGenericRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteRegularLocus]
   utility: none
   digest: A single adjacent two-site marginal generically identifies five-site periodic binary states. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialRegular
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGermSeparation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSCompactAnalyticCharts
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSitePhaseTransfer

/-! Generic unit-phase recovery from the adjacent two-site marginal. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteGenericRecovery

open Filter Set PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteRegularLocus
  PeriodicMPSFiveSiteSpecialGerms PeriodicMPSFiveSiteSpecialRegular PeriodicMPSFiveSiteOrdinaryTrace
  PeriodicMPSFiveSitePhysicalObservation PeriodicMPSFiveSiteCompactSpecialFiber
  PeriodicMPSCompactAnalyticCharts PeriodicMPSAnalyticBranchSeparation
  PeriodicMPSFiveSitePhaseTransfer PeriodicMPSFiveSiteSpecialGermSeparation
open PeriodicMPSFiveSiteNormalization (normalizedGram)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSParentIntersection (Bond)
open scoped Topology

noncomputable section

private theorem regularChart_at (p : source) (hp : p ∈ regularSource) :
    Nonempty (RegularChart (E := Parameters) onSource p) := by
  let V : Set source := Subtype.val ⁻¹' chartDomain
  let hV : IsOpen V := isOpen_chartDomain.preimage continuous_subtype_val
  let h : domain ≃ₜ V := ordinaryHomeomorph.trans
    (interSubtypeHomeomorph source chartDomain).symm
  let hn : Nonempty domain := ⟨⟨decode p.val, hp.2.1⟩⟩
  let c := openSubsetChart isOpen_domain hV hn h
  have hp' : p ∈ c.target := by
    rw [show c.target = V from openSubsetChart_target _ _ _ _]
    exact hp.1
  have hs : c.symm p = decode p.val := by
    exact openSubsetChart_symm_apply isOpen_domain hV hn h ⟨p, hp.1⟩
  refine ⟨⟨c, hp', observe, ?_, ?_, ?_⟩⟩
  · intro q hq
    have hq' : q ∈ domain := by
      rwa [show c.source = domain from openSubsetChart_source _ _ _ _] at hq
    change observe q = onSource (c q)
    rw [show c q = (⟨encode q, encode_mem_source hq'⟩ : source) from
      openSubsetChart_apply isOpen_domain hV hn h ⟨q, hq'⟩]
    exact (observe_encode ⟨q, hq'⟩).symm
  · rw [hs]
    exact analyticAt_observe _ hp.2.1
  · rw [hs]
    exact hp.2.2

private theorem sameFiber_good (p : good) {q : source} (hq : onSource q = onSource p.val) :
    q ∈ good := by
  change onSource q ∉ _
  rw [hq]
  exact p.property

private def chosenFamily (p : good) :
    FiberGraphs (E := Parameters) onSource (onSource p.val) good := by
  haveI : CompactSpace source := isCompact_iff_compactSpace.mp source_isCompact
  apply Classical.choice
  apply exists_fiber_graphs continuous_onSource (mem_range_self p.val) isOpen_good
  · intro q hq
    exact sameFiber_good p hq
  · norm_num [Readings, Parameters, Module.finrank_pi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex]
  · intro q hq
    exact regularChart_at q (good_subset_regular (sameFiber_good p hq))

private def chosenChart (p : good) :
    AnalyticAmbiguityChart Parameters (Subtype.val ⁻¹' ambiguous onSource) p :=
  (chosenFamily p).ambiguityChart isOpen_good ⟨p.val, rfl⟩

private theorem special_fiber (i : Fin 4) (q : source)
    (hq : onSource q = onSource (specialPoint i)) : ∃ j, q = specialPoint j := by
  have h := (measured_eq_iff q.property (specialPoint i).property).mp hq
  rw [specialPoint_observation] at h
  exact specialPoint_exhausts h

private theorem special_good (i : Fin 4) : specialPoint i ∈ good := by
  intro h
  obtain ⟨q, hq, he⟩ := h
  obtain ⟨j, rfl⟩ := special_fiber i q he
  exact hq ⟨specialPoint_in_ordinary j, specialPoint_regular j⟩

private theorem special_chart_distinct :
    ∃ p : good, ∀ k, ¬ EqOn (chosenChart p).graph ((chosenChart p).competitor k)
      (chosenChart p).domain := by
  let p : good := ⟨specialPoint 0, special_good 0⟩
  refine ⟨p, ?_⟩
  apply (chosenFamily p).ambiguityChart_distinct isOpen_good ⟨p.val, rfl⟩
  intro q hq
  obtain ⟨j, he⟩ := special_fiber 0 q.val q.property
  have hj : (0 : Fin 4) ≠ j := by
    intro h
    apply hq
    apply Subtype.ext
    exact he.trans (congrArg specialPoint h.symm)
  rw [he]
  exact specialPoint_germs_distinct 0 j hj

/-- The compact observation has singleton fibers on a relatively open dense locus. -/
theorem compact_generic_recovery :
    ∃ G : Set source, IsOpen G ∧ Dense G ∧
      ∀ x ∈ G, ∀ y : source, observation y.val = observation x.val → y = x := by
  letI : PathConnectedSpace good := isPathConnected_iff_pathConnectedSpace.mp isPathConnected_good
  let A : Set good := Subtype.val ⁻¹' ambiguous onSource
  obtain ⟨hA, hdA⟩ := open_dense_compl_of_analytic_fiber_charts
    (A := A) chosenChart special_chart_distinct
  let G : Set source := Subtype.val '' Aᶜ
  have hG : IsOpen G := isOpen_good.isOpenMap_subtype_val _ hA
  have hg : Dense G := by
    have h : good ⊆ closure G := by
      intro p hp
      exact image_closure_subset_closure_image continuous_subtype_val ⟨⟨p, hp⟩, hdA _, rfl⟩
    exact fun p => closure_minimal h isClosed_closure (dense_good p)
  refine ⟨G, hG, hg, ?_⟩
  rintro x ⟨z, hz, rfl⟩ y he
  by_contra hne
  exact hz ⟨y, hne, (measured_eq_iff y.property z.val.property).mpr he⟩

/-- Among unit-mass five-site periodic binary bond-two amplitudes, a single adjacent
two-site marginal determines the state up to unit phase on an open dense locus.
The competing state may be any actual unit-mass periodic binary bond-two state. -/
theorem generic_unitPhase_recovery :
    ∃ U : Set UnitStates, IsOpen U ∧ Dense U ∧
      ∀ p ∈ U, ∀ q : UnitStates, normalizedGram q.val = normalizedGram p.val →
        ∃ z : ℂ, ‖z‖ = 1 ∧ q.val = z • p.val := by
  obtain ⟨G, hG, hd, h⟩ := compact_generic_recovery
  exact transfer_unitPhase hG hd h

/-- One adjacent two-site reduced density determines the full unit-mass
five-site periodic binary bond-two amplitude on an open dense locus. -/
theorem generic_rawTwo_unitPhase_recovery :
    ∃ U : Set UnitWordStates, IsOpen U ∧ Dense U ∧
      ∀ (A B : Fin 2 → Bond) (hA : wordMass (traceWord 2 2 5 A) = 1),
        (⟨traceWord 2 2 5 A, ⟨A, rfl⟩, hA⟩ : UnitWordStates) ∈ U →
        PeriodicMPSTwoSiteAmbiguity.rawTwo B 1 = PeriodicMPSTwoSiteAmbiguity.rawTwo A 1 →
          ∃ z : ℂ, ‖z‖ = 1 ∧ traceWord 2 2 5 B = z • traceWord 2 2 5 A := by
  obtain ⟨G, hG, hd, h⟩ := compact_generic_recovery
  obtain ⟨U, hU, hdU, he⟩ := transfer_rawTwo_unitPhase hG hd h
  refine ⟨U, hU, hdU, ?_⟩
  intro A B hA hAU hR
  exact he A B hA ((wordMass_eq_of_rawTwo_eq A B hR).trans hA) hAU hR

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteGenericRecovery
