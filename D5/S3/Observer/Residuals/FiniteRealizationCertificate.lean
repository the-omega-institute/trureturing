/- GID: D5/S3/Observer/Residuals/FiniteRealizationCertificate
   generality: G
   mirror-B: D5/B/S3/Observer/Residuals/FiniteRealizationCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every unrealizable real protocol signature has a finite strict linear certificate. -/

/- Library-search audit trail (2026-08-28):
   * The body-shape search found the canonical dependent product `jointReadout`,
     which constructs the realization profile below.
   * Repository searches found no theorem extracting a finite linear witness
     from an external point of a compact convex realization image.
   * Pinned Mathlib supplies the exact strict-separation theorem
     `geometric_hahn_banach_closed_point`, product-neighborhood basis lemmas,
     `Pi.single`, and compact extreme-value results. It has no packaged theorem
     saying that a continuous functional on an arbitrary product has finite
     coordinate support, so that bridge is proved locally. -/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

namespace D5.S3.Observer.Residuals.FiniteRealizationCertificate

open Set Filter
open scoped BigOperators Topology
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem continuous_linear_functional_finite_coordinates
    {Protocol : Type*} (functional : (Protocol -> ℝ) →L[ℝ] ℝ) :
    ∃ protocols : Finset Protocol, ∃ coefficient : Protocol -> ℝ,
      ∀ signature : Protocol -> ℝ,
        functional signature =
          ∑ protocol ∈ protocols, coefficient protocol * signature protocol := by
  classical
  have hpreimage :
      functional ⁻¹' Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : Protocol -> ℝ) :=
    functional.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (by constructor <;> norm_num))
  simp only [nhds_pi, Filter.mem_pi'] at hpreimage
  obtain ⟨protocols, neighborhood, hneighborhood, hsubset⟩ := hpreimage
  refine ⟨protocols, fun protocol => functional (Pi.single protocol 1), fun signature => ?_⟩
  let truncated : Protocol -> ℝ :=
    ∑ protocol ∈ protocols, Pi.single protocol (signature protocol)
  have hvanish : functional (signature - truncated) = 0 := by
    by_contra hnonzero
    let scale : ℝ := 2 / functional (signature - truncated)
    have hscaled_mem :
        scale • (signature - truncated) ∈
          Set.pi (↑protocols : Set Protocol) neighborhood := by
      intro protocol hprotocol
      have hprotocols : protocol ∈ protocols := hprotocol
      have hcoordinate : (signature - truncated) protocol = 0 := by
        simp [truncated, Finset.sum_pi_single, hprotocols]
      rw [Pi.smul_apply, hcoordinate, smul_zero]
      exact mem_of_mem_nhds (hneighborhood protocol)
    have hinterval := hsubset hscaled_mem
    change functional (scale • (signature - truncated)) ∈
      Set.Ioo (-1 : ℝ) 1 at hinterval
    have hscaled_value :
        functional (scale • (signature - truncated)) = 2 := by
      rw [functional.map_smul]
      dsimp only [scale]
      exact div_mul_cancel₀ 2 hnonzero
    rw [hscaled_value] at hinterval
    norm_num at hinterval
  have heq : functional signature = functional truncated := by
    have hsub : functional signature - functional truncated = 0 := by
      simpa only [map_sub] using hvanish
    exact sub_eq_zero.mp hsub
  rw [heq]
  simp only [truncated, map_sum]
  apply Finset.sum_congr rfl
  intro protocol _
  rw [show Pi.single protocol (signature protocol) =
      signature protocol • Pi.single protocol 1 by
    rw [← Pi.single_smul']
    simp]
  simp [mul_comm]

private theorem compact_supremum_lt
    {State : Type*} [TopologicalSpace State]
    (states : Set State) (hcompact : IsCompact states)
    (value : State -> ℝ) (hcontinuous : ContinuousOn value states)
    (bound : ℝ) (hbound : ∀ state ∈ states, value state < bound) :
    sSup ((fun state => (value state : WithBot ℝ)) '' states) <
      (bound : WithBot ℝ) := by
  rcases states.eq_empty_or_nonempty with rfl | hnonempty
  · simp
  obtain ⟨maximum, hmaximum_mem, hmaximum⟩ :=
    hcompact.exists_isMaxOn hnonempty hcontinuous
  have hgreatest :
      IsGreatest ((fun state => (value state : WithBot ℝ)) '' states)
        (value maximum : WithBot ℝ) := by
    refine ⟨⟨maximum, hmaximum_mem, rfl⟩, ?_⟩
    rintro _ ⟨state, hstate, rfl⟩
    exact WithBot.coe_le_coe.mpr (hmaximum hstate)
  rw [hgreatest.csSup_eq]
  exact WithBot.coe_lt_coe.mpr (hbound maximum hmaximum_mem)

/-- A compact convex state set and continuous affine real protocol readouts
construct their realization image through the canonical joint readout. Every
signature outside that image is strictly separated by finitely many protocols.
The lower completion of the real supremum records the empty-state case as
negative infinity without adding a nonemptiness premise. -/
theorem finite_realization_certificate
    {State Protocol : Type*} [TopologicalSpace State]
    [AddCommGroup State] [Module ℝ State]
    (states : Set State) (hcompact : IsCompact states)
    (hconvex : Convex ℝ states)
    (readout : Protocol -> State →ᴬ[ℝ] ℝ)
    (formalSignature : Protocol -> ℝ)
    (outside :
      let profile : State -> Protocol -> ℝ :=
        jointReadout (fun protocol => readout protocol)
      formalSignature ∉ profile '' states) :
    ∃ protocols : Finset Protocol, ∃ coefficient : Protocol -> ℝ,
      ((∑ protocol ∈ protocols,
          coefficient protocol * formalSignature protocol : ℝ) : WithBot ℝ) >
        sSup ((fun state : State =>
          ((∑ protocol ∈ protocols,
              coefficient protocol * readout protocol state : ℝ) : WithBot ℝ)) '' states) := by
  let profile : State -> Protocol -> ℝ :=
    jointReadout (fun protocol => readout protocol)
  change formalSignature ∉ profile '' states at outside
  have hprofile_continuous : Continuous profile := by
    apply continuous_pi
    intro protocol
    exact (readout protocol).continuous
  have hcompact_image : IsCompact (profile '' states) :=
    hcompact.image hprofile_continuous
  let profileAffine : State →ᵃ[ℝ] (Protocol -> ℝ) :=
    AffineMap.pi (fun protocol => (readout protocol).toAffineMap)
  have hprofile_eq : profile = profileAffine := by
    funext state protocol
    rfl
  have hconvex_image : Convex ℝ (profile '' states) := by
    rw [hprofile_eq]
    exact hconvex.affine_image profileAffine
  obtain ⟨functional, threshold, hrealizable, hformal⟩ :=
    geometric_hahn_banach_closed_point
      hconvex_image hcompact_image.isClosed outside
  obtain ⟨protocols, coefficient, hfunctional⟩ :=
    continuous_linear_functional_finite_coordinates functional
  refine ⟨protocols, coefficient, ?_⟩
  apply compact_supremum_lt states hcompact
    (fun state =>
      ∑ protocol ∈ protocols, coefficient protocol * readout protocol state)
  · fun_prop
  · intro state hstate
    calc
      ∑ protocol ∈ protocols, coefficient protocol * readout protocol state =
          functional (profile state) := by
            rw [hfunctional]
            rfl
      _ < threshold := hrealizable _ ⟨state, hstate, rfl⟩
      _ < functional formalSignature := hformal
      _ = ∑ protocol ∈ protocols,
          coefficient protocol * formalSignature protocol :=
        hfunctional formalSignature

#print axioms finite_realization_certificate

end D5.S3.Observer.Residuals.FiniteRealizationCertificate
