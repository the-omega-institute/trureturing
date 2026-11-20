/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSSixSiteGenericRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSSixSiteGenericRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteRegularLocus]
   utility: none
   digest: One adjacent two-site marginal generically determines the actual six-site periodic MPS ray. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCriticalCover
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteRegularLocus
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGermSeparation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialRegular
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSitePhaseTransfer

/-! Generic recovery on the actual unit-mass six-site amplitude image. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteGenericRecovery

open Set Filter
open PeriodicMPSSixSiteCompactSource PeriodicMPSSixSiteOrdinaryTrace
  PeriodicMPSSixSiteRegularLocus PeriodicMPSSixSiteSpecialGerms
  PeriodicMPSSixSiteSpecialRegular PeriodicMPSSixSiteLocalGraphs
  PeriodicMPSSixSiteSpecialGermSeparation PeriodicMPSSixSitePhaseTransfer
open PeriodicMPSSixSiteCriticalCover (lift cover_critical_equations)
open PeriodicMPSSixSiteCriticalChart (minorOver)
open PeriodicMPSSixSiteCriticalRank (evaluated_minor_eq_zero_of_kernel)
open PeriodicMPSSixSitePhysicalObservation (traceParameter)
open PeriodicMPSFiveSitePhysicalObservation (complexParameter)
open PeriodicMPSProjectiveCoordinates (projector projector_ratio projector_diag_ne_zero_iff)
open PeriodicMPSParentIntersection (Bond)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped Topology

open private special_coordinates from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGerms

noncomputable section

private theorem critical_cover : CriticalCover := by
  apply criticalCover_of_kernel cover_critical_equations
  intro q hq v hv hker
  have hminor (k : Fin 10) :=
    evaluated_minor_eq_zero_of_kernel q hq v hv hker k
  constructor
  all_goals
    rw [minorOver, MvPolynomial.eval_map]
    exact hminor _

private theorem special_regular (i : Fin 2) : specialPoint i ∈ regularSource := by
  let a := complexParameter (center i)
  let v := traceParameter (center i)
  have hv : v 0 ≠ 0 := (special_coordinates i).2.1
  have hd : (specialPoint i).val.1 0 0 ≠ 0 :=
    (projector_diag_ne_zero_iff v 0).2 hv
  have hr (j : Fin 6) : (specialPoint i).val.1 j 0 / (specialPoint i).val.1 0 0 = v j / v 0 :=
    projector_ratio v j 0 hv
  have hdecode : decode (specialPoint i).val = toFirst a := by
    funext j
    unfold decode PeriodicMPSSixSiteCompactExceptional.firstTraceChart
    fin_cases j <;> simp only [Matrix.cons_val, hr]
    · change a 0 * a 2 / a 0 = a 2
      exact mul_div_cancel_left₀ _ (show a 0 ≠ 0 from hv)
    · rfl
    · rfl
    · exact one_div _
  have h := injective_normalizedObservation_special i
  have hreg : decode (specialPoint i).val ∈ regular := by
    rw [hdecode]
    exact regular_of_injective_normalizedObservation h.1 h.2
  exact ⟨⟨hd, hreg.1⟩, hreg⟩

private theorem special_exhausts {p : source} {i : Fin 2}
    (h : observation p.val = observation (specialPoint i).val) : ∃ j, p = specialPoint j := by
  rw [specialPoint_observation] at h
  exact specialPoint_exhausts h

private theorem separated_good_fiber : ∃ p : good, HasSeparatedFiber p := by
  have hp : specialPoint 0 ∈ good := by
    apply mem_good_iff.mpr
    intro q hq
    obtain ⟨i, rfl⟩ := special_exhausts (onSource_eq_iff.mp hq)
    exact special_regular i
  let p : good := ⟨specialPoint 0, hp⟩
  refine ⟨p, hasSeparatedFiber_of_observation p ?_⟩
  intro q hq hne
  obtain ⟨j, rfl⟩ := special_exhausts hq
  fin_cases j
  · exact (hne rfl).elim
  · exact specialPoint_germs_distinct

/-- The compact six-site observation has singleton fibers on a relatively open dense set. -/
theorem compact_generic_recovery :
    ∃ G : Set source, IsOpen G ∧ Dense G ∧
      ∀ x ∈ G, ∀ y : source, observation y.val = observation x.val → y = x :=
  compact_generic_recovery_of_separated_fiber critical_cover separated_good_fiber

/-- One adjacent two-site marginal determines a generic unit-mass six-site
periodic binary bond-two amplitude up to a unit phase, against every actual competitor. -/
theorem generic_rawTwo_unitPhase_recovery :
    ∃ U : Set UnitWordStates, IsOpen U ∧ Dense U ∧
      ∀ (A B : Fin 2 → Bond) (hA : wordMass (traceWord 2 2 6 A) = 1),
        (⟨traceWord 2 2 6 A, ⟨A, rfl⟩, hA⟩ : UnitWordStates) ∈ U →
        PeriodicMPSTwoSiteAmbiguity.rawTwo B 2 = PeriodicMPSTwoSiteAmbiguity.rawTwo A 2 →
          ∃ z : ℂ, ‖z‖ = 1 ∧ traceWord 2 2 6 B = z • traceWord 2 2 6 A := by
  obtain ⟨G, hG, hd, h⟩ := compact_generic_recovery
  obtain ⟨U, hU, hdU, he⟩ := transfer_rawTwo_unitPhase hG hd h
  refine ⟨U, hU, hdU, ?_⟩
  intro A B hA hAU hR
  exact he A B hA ((wordMass_eq_of_rawTwo_eq A B hR).trans hA) hAU hR

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteGenericRecovery
