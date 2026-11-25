/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHardCoreCompactRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHardCoreCompactRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreRecovery]
   utility: none
   digest: Local reconstruction against the whole compact closure. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreRecovery

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCompactRecovery

open Set Filter
open scoped Topology
open PeriodicMPSUniformHardCoreLocalization
open PeriodicMPSUniformHardCorePencilDecoder (witnessTensor)
open PeriodicMPSUniformHardCoreFirstJet (Coord witness cores)
open UniformMPSExpectedDimensionRefutation (traceWord)

open private chartProjector continuousAt_chartProjector eventually_nonzero_traceWord
  exists_chart_localization from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticChart

/-- A small observation guard admits no border-only competitors. A compact chart image
contains the closure of the actual projectors over the open guard. -/
theorem exists_open_guard_actual (r : ℕ) (hr : 3 ≤ r) :
    ∃ W : Set _, IsOpen W ∧ twoSiteObservation (r + 2) (witnessProjector (r + 2)) ∈ W ∧
      ∀ P ∈ closure (actualProjectors (r + 2)), twoSiteObservation (r + 2) P ∈ W →
        P ∈ actualProjectors (r + 2) := by
  obtain ⟨S, hSsub, hSo, hSw⟩ := mem_nhds_iff.mp (eventually_nonzero_traceWord r hr)
  obtain ⟨K, hKc, hKw, hKS⟩ := exists_compact_subset hSo hSw
  obtain ⟨W, hWo, hWw, hW⟩ := exists_chart_localization r hr
    (isOpen_interior.mem_nhds hKw)
  let F := twoSiteObservation (r + 2)
  let P := chartProjector r
  have hPc : ContinuousOn P K := fun x hx =>
    (continuousAt_chartProjector r x (hSsub (hKS hx))).continuousWithinAt
  have hImage : IsClosed (P '' K) := (hKc.image_of_continuousOn hPc).isClosed
  have hGuard : IsOpen (F ⁻¹' W) := hWo.preimage (continuous_twoSiteObservation _)
  refine ⟨W, hWo, ?_, ?_⟩
  · rw [witnessProjector, witnessTensor, twoSiteObservation_traceWord]
    exact hWw
  · intro q hq hqW
    have hqImage : q ∈ P '' K := by
      refine hImage.closure_subset_iff.mpr ?_ (hGuard.inter_closure ⟨hqW, hq⟩)
      rintro z ⟨hzW, hz⟩
      obtain ⟨x, hx, rfl⟩ := hW z hz hzW
      exact ⟨x, interior_subset hx, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hqImage
    exact ⟨cores x, hSsub (hKS hx), rfl⟩

/-- The uniform quartic separation gives relatively open dense singleton fibers in a
neighborhood of the witness in the compact source, against the whole compact source. -/
theorem exists_generic_compact_reconstruction (r : ℕ) (hr : 3 ≤ r) :
    ∃ N : Set (closure (actualProjectors (r + 2))), IsOpen N ∧
      (⟨witnessProjector (r + 2), subset_closure
        (witnessProjector_mem_actualProjectors (by omega))⟩ :
        closure (actualProjectors (r + 2))) ∈ N ∧
      ∃ G : Set N, IsOpen G ∧ Dense G ∧
        ∀ P ∈ G, ∀ Q : closure (actualProjectors (r + 2)),
          twoSiteObservation (r + 2) Q.val = twoSiteObservation (r + 2) P.val.val →
          Q.val = P.val.val := by
  obtain ⟨W, hWo, hWw, hActual⟩ := exists_open_guard_actual r hr
  obtain ⟨N, hNo, hNw, G, hGo, hGd, hG⟩ :=
    PeriodicMPSUniformHardCoreRecovery.exists_generic_actual_reconstruction r hr
  let A := actualProjectors (r + 2)
  let X := closure A
  let F := twoSiteObservation (r + 2)
  let guard : Set (StateMatrix (r + 2)) := F ⁻¹' W
  have hguard : IsOpen guard := hWo.preimage (continuous_twoSiteObservation _)
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp hNo
  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.mp hGo
  obtain ⟨U₀, hU₀o, hU₀⟩ := isOpen_induced_iff.mp hUo
  let N' : Set X := Subtype.val ⁻¹' (V ∩ guard)
  let G' : Set N' := (Subtype.val ∘ Subtype.val) ⁻¹' U₀
  have hN'w : (⟨witnessProjector (r + 2), subset_closure
        (witnessProjector_mem_actualProjectors (by omega))⟩ : X) ∈ N' := by
    refine ⟨?_, hWw⟩
    change (⟨witnessProjector (r + 2), witnessProjector_mem_actualProjectors (by omega)⟩ : A)
      ∈ Subtype.val ⁻¹' V
    rwa [hV]
  have hGmem (q : N') (hq : q ∈ G') :
      ∃ p : N, p ∈ G ∧ p.val.val = q.val.val := by
    let a : A := ⟨q.val.val, hActual _ q.val.property q.property.2⟩
    let p : N := ⟨a, hV ▸ q.property.1⟩
    exact ⟨p, hU ▸ (hU₀ ▸ hq), rfl⟩
  refine ⟨N', (hVo.inter hguard).preimage continuous_subtype_val, hN'w, G',
    hU₀o.preimage (continuous_subtype_val.comp continuous_subtype_val), ?_, ?_⟩
  · rw [dense_iff_inter_open]
    intro T hTo hTne
    obtain ⟨q, hq⟩ := hTne
    obtain ⟨T₁, hT₁o, hT₁⟩ := isOpen_induced_iff.mp hTo
    obtain ⟨T₀, hT₀o, hT₀⟩ := isOpen_induced_iff.mp hT₁o
    let a : A := ⟨q.val.val, hActual _ q.val.property q.property.2⟩
    let p : N := ⟨a, hV ▸ q.property.1⟩
    let S : Set N := (Subtype.val ∘ Subtype.val) ⁻¹' (T₀ ∩ guard)
    have hSo : IsOpen S := (hT₀o.inter hguard).preimage
      (continuous_subtype_val.comp continuous_subtype_val)
    have hq₀ : q.val.val ∈ T₀ := by
      change q ∈ Subtype.val ⁻¹' (Subtype.val ⁻¹' T₀)
      rwa [hT₀, hT₁]
    have hp : p ∈ S := ⟨hq₀, q.property.2⟩
    obtain ⟨z, hzS, hzG⟩ := dense_iff_inter_open.mp hGd S hSo ⟨p, hp⟩
    have hzV : z.val.val ∈ V := by
      change z.val ∈ Subtype.val ⁻¹' V
      rw [hV]
      exact z.property
    let z' : N' := ⟨⟨z.val.val, subset_closure z.val.property⟩,
      ⟨hzV, hzS.2⟩⟩
    refine ⟨z', hT₁ ▸ (hT₀ ▸ hzS.1), ?_⟩
    change z.val.val ∈ U₀
    change z ∈ Subtype.val ⁻¹' (Subtype.val ⁻¹' U₀)
    rwa [hU₀, hU]
  · intro q hq Q he
    obtain ⟨p, hp, hpq⟩ := hGmem q hq
    have hQ : Q.val ∈ A := hActual _ Q.property (he.symm ▸ q.property.2)
    exact (hG p hp ⟨Q.val, hQ⟩ (he.trans (congrArg F hpq).symm)).trans hpq

/-- A dense locus of regular projectors supplies compact singleton fibers in every
neighborhood of the witness. -/
theorem exists_compact_singleton_mem_dense (r : ℕ) (hr : 3 ≤ r)
    {R V : Set (closure (actualProjectors (r + 2)))} (hR : Dense R)
    (hV : V ∈ 𝓝 (⟨witnessProjector (r + 2), subset_closure
      (witnessProjector_mem_actualProjectors (by omega))⟩ : closure (actualProjectors (r + 2)))) :
    ∃ p ∈ V, p ∈ R ∧ ∀ q : closure (actualProjectors (r + 2)),
      twoSiteObservation (r + 2) q.val = twoSiteObservation (r + 2) p.val → q = p := by
  obtain ⟨N, hNo, hNw, G, hGo, hGd, hG⟩ := exists_generic_compact_reconstruction r hr
  obtain ⟨W, hWV, hWo, hWw⟩ := mem_nhds_iff.mp hV
  let T : Set N := Subtype.val ⁻¹' W
  have hTo : IsOpen T := hWo.preimage continuous_subtype_val
  obtain ⟨x, hxT, hxG⟩ := dense_iff_inter_open.mp hGd T hTo ⟨⟨_, hNw⟩, hWw⟩
  let S := Subtype.val '' (G ∩ T)
  have hSo : IsOpen S := hNo.isOpenMap_subtype_val _ (hGo.inter hTo)
  obtain ⟨p, hp, hpR⟩ := dense_iff_inter_open.mp hR S hSo ⟨x.val, x, ⟨hxG, hxT⟩, rfl⟩
  obtain ⟨x, ⟨hxG, hxT⟩, rfl⟩ := hp
  exact ⟨x.val, hWV hxT, hpR, fun q h => Subtype.ext (hG x hxG q h)⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCompactRecovery

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCompactRecovery.exists_generic_compact_reconstruction
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCompactRecovery.exists_compact_singleton_mem_dense
