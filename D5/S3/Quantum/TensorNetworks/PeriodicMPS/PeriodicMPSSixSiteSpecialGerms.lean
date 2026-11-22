/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialGerms
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialGerms
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSitePhysicalObservation]
   utility: none
   digest: The raw six-site charts recover the special compact lifts and their normalized germs. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSitePhysicalObservation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLocalGraphs
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSpecialFiber
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms

/-! Affine reconstruction with the mixed trace fixed and independent raw gain. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialGerms

open Set hiding center
open Filter PeriodicMPSSixSiteLocalGraphs PeriodicMPSSixSiteCompactSource
  PeriodicMPSSixSiteJetCoordinates PeriodicMPSSixSiteAnalyticDerivative
  PeriodicMPSSixSiteCompactSpecialFiber PeriodicMPSSixSiteMarginal
open PeriodicMPSSixSiteSpecialFiber (secondPhase)
open PeriodicMPSSixSitePhysicalObservation (traceParameter rayAmplitude raw_trace_eq
  normalize_raw_eq_observation)
open PeriodicMPSFiveSitePhysicalObservation (complexParameter entries rawTrace normalizeEntries
  restoreEntries restore_normalize)
open PeriodicMPSProjectiveCoordinates
open scoped Topology

open private continuous_amplitude gram_trace from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSource
open private source0 source1 from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialJets
open private secondPhase_cartesian from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialFiber
open private continuous_complexParameter pack unpack_pack pack_unpack
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms

noncomputable section

abbrev Q := Fin 4 → ℂ

/-- The compact lift associated with a raw source parameter. -/
def rawSource (u : E) : Ambient := graphPoint (traceParameter u)

private def mixedTuple (q : Q) : Fin 6 → ℂ :=
  ![q 0, q 0 * q 2, q 0 * q 2 ^ 2, q 1, q 3, 1]

private theorem traceParameter_eq (u : E) :
    traceParameter u = mixedTuple (complexParameter u) := rfl

private theorem continuous_mixedTuple : Continuous mixedTuple := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [mixedTuple] <;> fun_prop

private theorem continuous_traceParameter : Continuous traceParameter :=
  continuous_mixedTuple.comp continuous_complexParameter

private theorem continuous_rayAmplitude : Continuous rayAmplitude :=
  continuous_amplitude.comp continuous_traceParameter

private theorem traceParameter_ne_zero (u : E) : traceParameter u ≠ 0 := by
  intro h
  have he := congrFun h (4 + 1 : Fin 6)
  simpa [traceParameter, mixedTuple] using he

private theorem continuousAt_rawSource {u : E} (hu : rayAmplitude u ≠ 0) :
    ContinuousAt rawSource u :=
  ((continuousAt_projector (traceParameter_ne_zero u)).comp
    continuous_traceParameter.continuousAt).prodMk
    ((continuousAt_projector hu).comp continuous_rayAmplitude.continuousAt)

private def columnRatio (p : Ambient) (i : Fin 6) : ℂ := p.1 i 5 / p.1 5 5

private def rawCoordinates (p : Ambient) : Q :=
  ![columnRatio p 0, columnRatio p 3, columnRatio p 1 / columnRatio p 0, columnRatio p 4]

private theorem continuousAt_columnRatio {p : Ambient} (hp : p.1 5 5 ≠ 0) (i : Fin 6) :
    ContinuousAt (fun z => columnRatio z i) p := by
  have h (j : Fin 6) : Continuous (fun z : Ambient => z.1 j 5) :=
    (continuous_apply 5).comp ((continuous_apply j).comp continuous_fst)
  exact (h i).continuousAt.div (h 5).continuousAt hp

private theorem continuousAt_rawCoordinates {p : Ambient} (hp : p.1 5 5 ≠ 0)
    (h₀ : columnRatio p 0 ≠ 0) : ContinuousAt rawCoordinates p := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact continuousAt_columnRatio hp 0
  · exact continuousAt_columnRatio hp 3
  · exact (continuousAt_columnRatio hp 1).div (continuousAt_columnRatio hp 0) h₀
  · exact continuousAt_columnRatio hp 4

private def rawMass (q : Q) : ℝ := (gram (amplitude (mixedTuple q))).trace.re

private theorem continuous_trace_raw : Continuous (rawTrace ∘ raw : E → ℝ) := by
  have h (k : Fin 10) : Continuous (fun u : E => raw u k) :=
    continuous_iff_continuousAt.mpr fun u => (analytic_raw u k).continuousAt
  change Continuous (fun u : E => raw u 0 + 2 * raw u 5 + raw u 9)
  fun_prop

private theorem continuous_rawMass : Continuous rawMass := by
  have h : rawMass = (rawTrace ∘ raw) ∘ (fun q => pack q 1) := by
    funext q
    change rawMass q = rawTrace (raw (pack q 1))
    rw [raw_trace_eq, show pack q 1 8 = 1 from rfl, one_mul]
    simp [rayAmplitude, traceParameter_eq, unpack_pack, rawMass]
  rw [h]
  apply continuous_trace_raw.comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [pack] <;> fun_prop

private def ambientDomain : Set Ambient :=
  {p | p.1 5 5 ≠ 0 ∧ columnRatio p 0 ≠ 0 ∧ rawMass (rawCoordinates p) ≠ 0}

private theorem isOpen_ambientDomain : IsOpen ambientDomain := by
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨hp, h₀, hm⟩
  have hd : Continuous (fun z : Ambient => z.1 5 5) :=
    (continuous_apply _).comp ((continuous_apply _).comp continuous_fst)
  exact inter_mem (hd.continuousAt (isOpen_ne.mem_nhds hp))
    (inter_mem ((continuousAt_columnRatio hp 0) (isOpen_ne.mem_nhds h₀))
      ((continuous_rawMass.continuousAt.comp (continuousAt_rawCoordinates hp h₀))
        (isOpen_ne.mem_nhds hm)))

private theorem columnRatio_rawSource (u : E) (i : Fin 6) :
    columnRatio (rawSource u) i = traceParameter u i := by
  have h : traceParameter u 5 = 1 := rfl
  have he := projector_ratio (traceParameter u) i 5 (h.symm ▸ one_ne_zero)
  simpa [columnRatio, rawSource, graphPoint, h] using he

private theorem rawCoordinates_rawSource {u : E} (h₀ : complexParameter u 0 ≠ 0) :
    rawCoordinates (rawSource u) = complexParameter u := by
  funext i
  fin_cases i
  · exact columnRatio_rawSource u 0
  · exact columnRatio_rawSource u 3
  · change columnRatio (rawSource u) 1 / columnRatio (rawSource u) 0 = _
    rw [columnRatio_rawSource, columnRatio_rawSource]
    change (complexParameter u 0 * complexParameter u 2) / complexParameter u 0 = _
    exact mul_div_cancel_left₀ _ h₀
  · exact columnRatio_rawSource u 4

private theorem source_reconstruction {p : Ambient} (hp : p ∈ source)
    (hD : p ∈ ambientDomain) : p = graphPoint (mixedTuple (rawCoordinates p)) := by
  obtain ⟨a, ha, hA⟩ := source_invariant_projective hp
  have ham : mass a = 1 := ha
  have hP : p.1 = projector a := by
    rw [projector, ham, inv_one, one_smul]
    exact hA.symm
  have h₅ : a 5 ≠ 0 := by
    apply (projector_diag_ne_zero_iff a 5).mp
    rw [← hP]
    exact hD.1
  have hratio (i : Fin 6) : columnRatio p i = a i / a 5 := by
    unfold columnRatio
    rw [hP]
    exact projector_ratio a i 5 h₅
  have hA₀ : a 0 ≠ 0 := by
    intro he
    exact hD.2.1 (by rw [hratio, he, zero_div])
  have hq := source_quadric_column hp 5
  have hquad : (a 1 / a 5) ^ 2 = (a 0 / a 5) * (a 2 / a 5) := by
    rw [← hratio, ← hratio, ← hratio]
    unfold columnRatio
    rw [div_pow, div_mul_div_comm, hq, pow_two]
  have hb : a 0 / a 5 ≠ 0 := div_ne_zero hA₀ h₅
  have ht : mixedTuple (rawCoordinates p) = (a 5)⁻¹ • a := by
    funext i
    fin_cases i
    · change columnRatio p 0 = (a 5)⁻¹ * a 0
      rw [hratio, div_eq_mul_inv, mul_comm]
    · change columnRatio p 0 * (columnRatio p 1 / columnRatio p 0) = (a 5)⁻¹ * a 1
      rw [hratio, hratio, mul_div_cancel₀ _ hb, div_eq_mul_inv, mul_comm]
    · change columnRatio p 0 * (columnRatio p 1 / columnRatio p 0) ^ 2 = (a 5)⁻¹ * a 2
      rw [hratio, hratio]
      calc
        (a 0 / a 5) * (a 1 / a 5 / (a 0 / a 5)) ^ 2 = a 2 / a 5 := by
          apply mul_left_cancel₀ hb
          calc
            _ = (a 1 / a 5) ^ 2 := by field_simp [hb]
            _ = _ := hquad
        _ = _ := by rw [div_eq_mul_inv, mul_comm]
    · change columnRatio p 3 = (a 5)⁻¹ * a 3
      rw [hratio, div_eq_mul_inv, mul_comm]
    · change columnRatio p 4 = (a 5)⁻¹ * a 4
      rw [hratio, div_eq_mul_inv, mul_comm]
    · change 1 = (a 5)⁻¹ * a 5
      exact (inv_mul_cancel₀ h₅).symm
  have hne : amplitude (mixedTuple (rawCoordinates p)) ≠ 0 := by
    intro hz
    apply hD.2.2
    simp [rawMass, hz, gram_trace, flatten]
  apply eq_graphPoint_of_amplitude_ne_zero hp _ hne
  rw [ht, projector_scale _ (inv_ne_zero h₅)]
  exact hP

private def rebuild (p : Ambient) (τ : ℝ) : E :=
  pack (rawCoordinates p) (τ / rawMass (rawCoordinates p))

private theorem rawSource_rebuild {p : Ambient} (hp : p ∈ source)
    (hD : p ∈ ambientDomain) (τ : ℝ) : rawSource (rebuild p τ) = p := by
  simp only [rawSource, rebuild, traceParameter_eq, unpack_pack]
  exact (source_reconstruction hp hD).symm

private theorem rebuild_center_of_valid {u : E}
    (h₀ : complexParameter u 0 ≠ 0) (hm : rayAmplitude u ≠ 0) :
    rebuild (rawSource u) (rawTrace (raw u)) = u := by
  unfold rebuild
  rw [rawCoordinates_rawSource h₀, raw_trace_eq]
  change pack (complexParameter u) (u 8 * rawMass (complexParameter u) /
    rawMass (complexParameter u)) = u
  have hpos : rawMass (complexParameter u) ≠ 0 := (gram_mass_pos _ hm).ne'
  rw [mul_div_cancel_right₀ _ hpos, pack_unpack]

private theorem continuousAt_rebuild {p : Ambient} {t : ℝ} (hp : p ∈ ambientDomain) :
    ContinuousAt (fun x : Ambient × ℝ => rebuild x.1 x.2) (p, t) := by
  let q : Ambient × ℝ → Q := fun x => rawCoordinates x.1
  have hq : ContinuousAt q (p, t) :=
    ContinuousAt.comp_of_eq (f := Prod.fst) (x := (p, t))
      (continuousAt_rawCoordinates hp.1 hp.2.1) continuous_fst.continuousAt rfl
  have hτ : ContinuousAt (fun x : Ambient × ℝ => x.2 / rawMass (q x)) (p, t) :=
    continuous_snd.continuousAt.div (continuous_rawMass.continuousAt.comp hq) hp.2.2
  have hc (i : Fin 4) := continuousAt_pi.mp hq i
  have hr (i : Fin 4) := Complex.continuous_re.continuousAt.comp (hc i)
  have hi (i : Fin 4) := Complex.continuous_im.continuousAt.comp (hc i)
  apply continuousAt_pi.mpr
  intro k
  fin_cases k <;> first | exact hr _ | exact hi _ | exact hτ

/-- Nine independent normalized entries used to compare the two local germs. -/
def measured (p : Ambient) : Fin 9 → ℝ := fun i => entries (observation p) i.castSucc

private theorem raw_measured_eq (u : E) (hg : u 8 ≠ 0) (ha : rayAmplitude u ≠ 0) :
    normalizeEntries (raw u) = measured (rawSource u) :=
  normalize_raw_eq_observation u hg ha

private theorem raw_rebuild {p : Ambient} (hp : p ∈ source) (hD : p ∈ ambientDomain)
    {τ : ℝ} (hτ : τ ≠ 0) :
    raw (rebuild p τ) = restoreEntries τ (measured p) := by
  have hg : rebuild p τ 8 ≠ 0 := div_ne_zero hτ hD.2.2
  have hm : rayAmplitude (rebuild p τ) ≠ 0 := by
    intro hz
    apply hD.2.2
    have he : rayAmplitude (rebuild p τ) = amplitude (mixedTuple (rawCoordinates p)) := by
      simp [rayAmplitude, rebuild, traceParameter_eq, unpack_pack]
    rw [he] at hz
    simp [rawMass, hz, gram_trace, flatten]
  have htr : rawTrace (raw (rebuild p τ)) = τ := by
    rw [raw_trace_eq]
    change (τ / rawMass (rawCoordinates p)) *
      (gram (amplitude (mixedTuple (complexParameter (rebuild p τ))))).trace.re = τ
    simp only [rebuild, unpack_pack]
    exact div_mul_cancel₀ τ hD.2.2
  have he := raw_measured_eq (rebuild p τ) hg hm
  rw [rawSource_rebuild hp hD τ] at he
  have h := restore_normalize (raw (rebuild p τ)) (htr.symm ▸ hτ)
  rw [htr, he] at h
  exact h.symm

private theorem coordinates_zero : complexParameter (center 0) = ![1, Complex.I, 0, 0] := by
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [complexParameter, center, PeriodicMPSSixSiteSpecialJets.source, source0]

private theorem coordinates_one :
    complexParameter (center 1) = ![secondPhase, secondPhase * (-Complex.I), 0, 0] := by
  rw [secondPhase_cartesian]
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [complexParameter, center, PeriodicMPSSixSiteSpecialJets.source, source1,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]

private theorem special_coordinates (i : Fin 2) :
    rayAmplitude (center i) ≠ 0 ∧ complexParameter (center i) 0 ≠ 0 ∧
      center i 8 = 1 := by
  have ht (x y : ℂ) : amplitude (nilpotentInvariant x y) ≠ 0 := by
    rw [amplitude_nilpotentInvariant]
    intro h
    have h9 := congrFun h (9 : Fin 14)
    norm_num [PeriodicMPSSixSiteMarginal.nilpotentRay,
      PeriodicMPSSixSiteMarginal.independentSlice] at h9
  have hphase : secondPhase ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [secondPhase, Complex.div_re, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] at he
  have htrace (x y : ℂ) (i : Fin 2)
      (hxy : complexParameter (center i) = ![x, y, 0, 0]) :
      traceParameter (center i) = nilpotentInvariant x y := by
    rw [traceParameter_eq, hxy]
    funext j
    fin_cases j <;> simp [mixedTuple, nilpotentInvariant]
  fin_cases i
  · exact ⟨by change amplitude (traceParameter (center 0)) ≠ 0
              rw [htrace _ _ _ coordinates_zero]
              exact ht _ _,
      by change complexParameter (center 0) 0 ≠ 0
         rw [coordinates_zero]
         exact one_ne_zero, by
        change center 0 8 = 1
        norm_num [center, PeriodicMPSSixSiteSpecialJets.source, source0]⟩
  · exact ⟨by change amplitude (traceParameter (center 1)) ≠ 0
              rw [htrace _ _ _ coordinates_one]
              exact ht _ _,
      by change complexParameter (center 1) 0 ≠ 0
         rw [coordinates_one]
         exact hphase, by
        change center 1 8 = 1
        norm_num [center, PeriodicMPSSixSiteSpecialJets.source, source1]⟩

/-- The two points over the certified observation, with their compact source memberships. -/
def specialPoint (i : Fin 2) : source :=
  ⟨rawSource (center i),
    PeriodicMPSSixSitePhysicalObservation.graphPoint_mem_source _ (special_coordinates i).1⟩

private theorem specialPoint_in_chart (i : Fin 2) : (specialPoint i).val ∈ ambientDomain := by
  obtain ⟨hm, h₀, _⟩ := special_coordinates i
  have h₅ : traceParameter (center i) 5 = 1 := rfl
  change rawSource (center i) ∈ ambientDomain
  refine ⟨(projector_diag_ne_zero_iff _ _).2 (h₅.symm ▸ one_ne_zero), ?_, ?_⟩
  · rw [columnRatio_rawSource]
    exact h₀
  · rw [rawCoordinates_rawSource h₀]
    exact (gram_mass_pos _ hm).ne'

private theorem specialPoint_eq (i : Fin 2) :
    (specialPoint i).val =
      if i = 0 then point 1 Complex.I else point secondPhase (secondPhase * (-Complex.I)) := by
  fin_cases i
  · change graphPoint (traceParameter (center 0)) = point 1 Complex.I
    rw [traceParameter_eq, coordinates_zero]
    congr 1
    funext j
    fin_cases j <;> simp [mixedTuple, nilpotentInvariant]
  · change graphPoint (traceParameter (center 1)) = point secondPhase (secondPhase * (-Complex.I))
    rw [traceParameter_eq, coordinates_one]
    congr 1
    funext j
    fin_cases j <;> simp [mixedTuple, nilpotentInvariant]

theorem specialPoint_observation (i : Fin 2) : observation (specialPoint i).val = target := by
  apply (observation_eq_target_iff (specialPoint i).property).mpr
  rw [specialPoint_eq]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem specialPoint_exhausts {p : source} (h : observation p.val = target) :
    ∃ i, p = specialPoint i := by
  rcases (observation_eq_target_iff p.property).mp h with h | h
  · exact ⟨0, Subtype.ext (h.trans (by simp [specialPoint_eq]))⟩
  · exact ⟨1, Subtype.ext (h.trans (by simp [specialPoint_eq]))⟩

private theorem rebuild_center (i : Fin 2) :
    rebuild (specialPoint i).val (rawTrace (raw (center i))) = center i :=
  rebuild_center_of_valid (special_coordinates i).2.1 (special_coordinates i).1

private theorem eventually_valid (i : Fin 2) :
    ∀ᶠ u in 𝓝 (center i), rawSource u ∈ source ∧ rayAmplitude u ≠ 0 := by
  filter_upwards [continuous_rayAmplitude.continuousAt
    (isOpen_ne.mem_nhds (special_coordinates i).1)] with u hu
  exact ⟨PeriodicMPSSixSitePhysicalObservation.graphPoint_mem_source u hu, hu⟩

private theorem rawTrace_pos_center (i : Fin 2) : 0 < rawTrace (raw (center i)) := by
  rw [raw_trace_eq, (special_coordinates i).2.2, one_mul]
  exact gram_mass_pos _ (special_coordinates i).1

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialGerms
