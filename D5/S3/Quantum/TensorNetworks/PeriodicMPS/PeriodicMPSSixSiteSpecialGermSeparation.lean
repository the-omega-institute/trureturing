/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialGermSeparation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialGermSeparation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGerms]
   utility: none
   digest: The two branches of the six-site compact fiber have distinct normalized observation germs. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGerms
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGermSeparation

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialGermSeparation

open Set hiding center
open Filter PeriodicMPSSixSiteLocalGraphs PeriodicMPSSixSiteSpecialGerms
  PeriodicMPSSixSiteCompactSource PeriodicMPSSixSiteJetCoordinates
open PeriodicMPSFiveSitePhysicalObservation (rawTrace normalizeEntries restoreEntries restore_normalize)
open PeriodicMPSSixSitePhysicalObservation (rayAmplitude)
open scoped Topology

open private ambientDomain isOpen_ambientDomain rebuild continuousAt_rebuild
  rebuild_center specialPoint_in_chart raw_rebuild raw_measured_eq eventually_valid
  special_coordinates rawTrace_pos_center continuousAt_rawSource continuous_trace_raw
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGerms
open private rectangle_in_preimage tendsTo_inverse nearby_gain
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGermSeparation

noncomputable section

/-- A neighborhood of the second lift misses some observations arbitrarily close to
the first lift. The independent raw trace coordinate transports the cubic obstruction. -/
theorem specialPoint_germs_distinct :
    ∃ V : Set source, V ∈ 𝓝 (specialPoint 1) ∧
      ¬ ∀ᶠ p in 𝓝 (specialPoint 0),
        observation p.val ∈ (fun q : source => observation q.val) '' V := by
  classical
  obtain ⟨e₀, U₀, g₀, he₀, hx₀, hU₀, hy₀, _, _, hg₀, hj₀⟩ := exists_certified_graph 0
  obtain ⟨e₁, U₁, g₁, he₁, hx₁, hU₁, hy₁, _, _, hg₁, hj₁⟩ := exists_certified_graph 1
  let y := tangent (center 0)
  let τ := rawTrace (raw (center 0))
  have hraw := raw_center_eq 0 1
  have hy : y = tangent (center 1) := funext fun k => congrFun hraw k.castSucc
  have hτ : τ = rawTrace (raw (center 1)) := congrArg rawTrace hraw
  have hr : rebuild (specialPoint 1).val τ ∈ e₁.source := by
    rw [hτ, rebuild_center]
    exact hx₁
  obtain ⟨W, I, hW, hI, hWI⟩ := rectangle_in_preimage
    (f := fun x : Ambient × ℝ => rebuild x.1 x.2)
    (continuousAt_rebuild (specialPoint_in_chart 1)) (e₁.open_source.mem_nhds hr)
  let V : Set source := Subtype.val ⁻¹' (W ∩ ambientDomain)
  have hV : V ∈ 𝓝 (specialPoint 1) :=
    continuous_subtype_val.continuousAt
      (inter_mem hW (isOpen_ambientDomain.mem_nhds (specialPoint_in_chart 1)))
  refine ⟨V, hV, ?_⟩
  intro hobs
  let lift : E → source := fun u =>
    if hu : rawSource u ∈ source then ⟨rawSource u, hu⟩ else specialPoint 0
  have hl : Tendsto lift (𝓝 (center 0)) (𝓝 (specialPoint 0)) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun u => (lift u).val) (𝓝 (center 0)) (𝓝 (rawSource (center 0)))
    exact (continuousAt_rawSource (special_coordinates 0).1).tendsto.congr'
      ((eventually_valid 0).mono fun u hu => by simp [lift, hu.1])
  have hx : Tendsto e₀.symm (𝓝 y) (𝓝 (center 0)) :=
    tendsTo_inverse e₀ hx₀ (congrFun he₀ (center 0))
  have hbranch := (hl.comp hx).eventually hobs
  have hv := hx.eventually (eventually_valid 0)
  have hz := hx.eventually ((continuous_trace_raw.continuousAt :
    ContinuousAt (rawTrace ∘ raw) (center 0))
      (inter_mem hI (isOpen_ne.mem_nhds (rawTrace_pos_center 0).ne')))
  have hgain := nearby_gain hx ((special_coordinates 0).2.2.symm ▸ one_ne_zero)
  have hy₁' : y ∈ U₁ := by rw [hy]; exact hy₁
  apply normal_germs_ne hj₀ hj₁
  filter_upwards [hbranch, hv, hz, hgain, hU₀.mem_nhds hy₀,
    hU₁.mem_nhds hy₁'] with t ht htvalid htrace htg ht₀ ht₁
  obtain ⟨q, hq, he⟩ := ht
  change observation q.val = observation (lift (e₀.symm t)).val at he
  rw [show (lift (e₀.symm t)).val = rawSource (e₀.symm t) by simp [lift, htvalid.1]] at he
  let u := e₀.symm t
  let z := rebuild q.val (rawTrace (raw u))
  have hq' : q.val ∈ W ∩ ambientDomain := hq
  have hzs : z ∈ e₁.source := hWI q.val hq'.1 (rawTrace (raw u)) htrace.1
  have hraw' : raw z = raw u := by
    have he' : measured q.val = normalizeEntries (raw u) := by
      rw [raw_measured_eq u htg htvalid.2]
      exact congrArg (fun M (j : Fin 9) => PeriodicMPSFiveSitePhysicalObservation.entries M j.castSucc) he
    change raw (rebuild q.val (rawTrace (raw u))) = raw u
    have htne : rawTrace (raw u) ≠ 0 := htrace.2
    rw [raw_rebuild q.property hq'.2 htne, he', restore_normalize _ htne]
  have htg₀ := hg₀ t ht₀
  have htg₁ := hg₁ t ht₁
  have hz' : z = e₁.symm t := by
    have ht' : e₁ z = t := by
      rw [show e₁ z = tangent z from congrFun he₁ z]
      exact (funext fun (k : Fin 9) => congrFun hraw' k.castSucc).trans (congrArg Prod.fst htg₀)
    rw [← ht', e₁.left_inv hzs]
  exact (congrArg Prod.snd htg₀).symm.trans
    ((congrFun hraw' 9).symm.trans ((congrArg normal hz').trans (congrArg Prod.snd htg₁)))

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialGermSeparation
