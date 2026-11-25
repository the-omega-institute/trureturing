/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphReadout
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphReadout
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Descent of singleton marginal fibers from the trace graph. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphBoundary
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout

/-! Readout and fiber descent for the compact seven-site trace graph. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteGraphReadout

open Set Function SevenSiteCompactGraph PeriodicMPSUniformHardCoreLocalization
open scoped ENNReal Matrix.Norms.Elementwise
open PeriodicMPSCompactReadout (Readout readout readout_eq_iff)

noncomputable section

abbrev ProjectorSource := ↥(closure (actualProjectors 5))

theorem snd_image_actualProjectors : Prod.snd '' source = closure (actualProjectors 5) := by
  rw [image_source_snd, image_graph_snd]
  congr 1
  ext P
  constructor
  · rintro ⟨A,hA,hP⟩
    exact ⟨A,hA,hP.symm⟩
  · rintro ⟨A,hA,hP⟩
    exact ⟨A,hA,hP.symm⟩

/-- Forgetting the weighted trace projector gives the compact source of literal states. -/
def state (x : Source) : ProjectorSource :=
  ⟨x.val.2,snd_image_actualProjectors ▸ mem_image_of_mem Prod.snd x.property⟩

theorem continuous_state : Continuous state :=
  (continuous_snd.comp continuous_subtype_val).subtype_mk _

theorem surjective_state : Surjective state := by
  intro y
  have hy : y.val ∈ Prod.snd '' source := by
    rw [snd_image_actualProjectors]
    exact y.property
  obtain ⟨x,hx,hxy⟩ := hy
  exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩

def observe (x : Source) : Readout := readout (twoSiteObservation 5 (state x).val)

theorem lipschitz_observe : ∃ K : NNReal, LipschitzWith K observe := by
  let Q := (twoSiteObservation 5).toContinuousLinearMap
  have hP : LipschitzWith 1 (fun x : Source => (state x).val) := by
    intro x y
    change edist x.val.2 y.val.2 ≤
      (1 : ℝ≥0∞) * max (edist x.val.1 y.val.1) (edist x.val.2 y.val.2)
    rw [one_mul]
    exact le_max_right _ _
  exact ⟨_, readout.lipschitzWith.comp (Q.lipschitzWith.comp hP)⟩

theorem graph_readout_eq_iff (x y : Source) :
    observe y = observe x ↔ twoSiteObservation 5 y.val.2 = twoSiteObservation 5 x.val.2 :=
  readout_eq_iff (state x) (state y)

/-- An open dense set of singleton observation fibers on the graph descends
to an open dense set of singleton literal-marginal fibers on the compact state source. -/
theorem state_singletons_of_graph_singletons {G : Set Source}
    (hGo : IsOpen G) (hGd : Dense G)
    (hG : ∀ x ∈ G, ∀ y : Source, observe y = observe x → y = x) :
    ∃ D : Set ProjectorSource, IsOpen D ∧ Dense D ∧
      ∀ x ∈ D, ∀ y : ProjectorSource,
        twoSiteObservation 5 y.val = twoSiteObservation 5 x.val → y = x := by
  have he : state '' G = (state '' Gᶜ)ᶜ := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩ ⟨z,hz,he⟩
      have hz' : z = x := hG x hx z (congrArg
        (fun p : ProjectorSource => readout (twoSiteObservation 5 p.val)) he)
      exact hz (hz' ▸ hx)
    · intro hy
      obtain ⟨x,rfl⟩ := surjective_state y
      have hx : x ∈ G := by
        by_contra h
        exact hy ⟨x,h,rfl⟩
      exact ⟨x,hx,rfl⟩
  refine ⟨state '' G, he ▸ (continuous_state.isClosedMap _ hGo.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · intro y
    obtain ⟨x,rfl⟩ := surjective_state y
    exact image_closure_subset_closure_image continuous_state ⟨x,hGd x,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩ y hy
    obtain ⟨z,rfl⟩ := surjective_state y
    exact congrArg state (hG x hx z ((graph_readout_eq_iff x z).mpr hy))

end

end D5.S3.Quantum.TensorNetworks.SevenSiteGraphReadout
