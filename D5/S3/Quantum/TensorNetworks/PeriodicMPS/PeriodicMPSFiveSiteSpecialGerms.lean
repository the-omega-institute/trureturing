/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialGerms
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialGerms
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation]
   utility: none
   digest: The raw observation branches distinguish the four normalized physical germs. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteOrdinaryTrace

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialGerms

open Set hiding center
open Filter PeriodicMPSFiveSiteLocalGraphs PeriodicMPSFiveSitePhysicalObservation
  PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteCompactChart
  PeriodicMPSFiveSiteCompactSpecialFiber PeriodicMPSFiveSiteJetCoordinates
  PeriodicMPSFiveSiteTraceChart PeriodicMPSFiveSiteNormalization
open PeriodicMPSFiveSiteAnalyticDerivative (analytic_raw)
open PeriodicMPSFiveSiteOrdinaryTrace (chartDomain)
open scoped Topology

open private fromFour continuous_fromFour ambientDomain isOpen_ambientDomain
  continuousAt_affineInverse traceRatio pencilRatio mixedRatio chart_ne_zero
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart
open private root b from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAlignedFiber
open private source0 source1 source2 source3 from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialJets
open private rayAmplitude from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation
open private ordinary_mem_chartDomain from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteOrdinaryTrace
open private traceDirection from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource
open PeriodicMPSProjectiveCoordinates (projector projector_ratio projector_diag_ne_zero_iff)

noncomputable section

abbrev Q := Fin 4 → ℂ

/-- Remove the raw gain and pass to the three projectors of the compact source. -/
def rawSource (u : E) : Ambient := fromFour (complexParameter u)

private def pack (q : Q) (g : ℝ) : E :=
  ![(q 0).re, (q 0).im, (q 1).re, (q 1).im, (q 2).re, (q 2).im, (q 3).re, (q 3).im, g]

private theorem unpack_pack (q : Q) (g : ℝ) : complexParameter (pack q g) = q := by
  funext i
  fin_cases i <;> exact Complex.ext rfl rfl

private theorem pack_unpack (u : E) : pack (complexParameter u) (u 8) = u := by
  funext i
  fin_cases i <;> rfl

private theorem continuous_complexParameter : Continuous complexParameter := by
  have h (a b : Fin 9) : Continuous (fun u : E => (⟨u a, u b⟩ : ℂ)) := by
    have he (u : E) : (⟨u a, u b⟩ : ℂ) =
        Complex.equivRealProdCLM.symm (u a, u b) := by
      apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply]
    simp_rw [he]
    exact Complex.equivRealProdCLM.symm.continuous.comp
      ((continuous_apply a).prodMk (continuous_apply b))
  apply continuous_pi
  intro i
  fin_cases i <;> exact h _ _

theorem continuous_rawSource : Continuous rawSource :=
  continuous_fromFour.comp continuous_complexParameter

private def squareTrace (q : Q) : ℂ := 2 * q 0 - 3 * q 1

private def mixed (q : Q) : ℂ := 1 + 2 * q 3 * (q 0 - q 1)

private theorem valid_rawSource (u : E) (h : squareTrace (complexParameter u) ≠ 0) :
    rawSource u ∈ source :=
  affine_mem_source _ _ _ _ h

private theorem affineDomain {q : Q} (ha : squareTrace q ≠ 0) (hm : mixed q ≠ 0) :
    fromFour q ∈ ambientDomain := by
  let p := fromFour q
  let v : Fin 6 → ℂ :=
    ![squareTrace q, squareTrace q * q 3, squareTrace q * q 3 ^ 2, q 0 - q 1,
      mixed q, q 2 + q 3 + q 3 ^ 2 * (q 0 - q 1)]
  have ht : p.1.1 0 0 ≠ 0 :=
    (projector_diag_ne_zero_iff (![1, q 3] : Fin 2 → ℂ) 0).2 one_ne_zero
  have hd : p.1.2 4 4 ≠ 0 := (projector_diag_ne_zero_iff v 4).2 hm
  have hs : traceRatio p = q 3 := by
    change projector (![1, q 3] : Fin 2 → ℂ) 1 0 / projector (![1, q 3] : Fin 2 → ℂ) 0 0 = _
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, div_one] using
      projector_ratio (![1, q 3] : Fin 2 → ℂ) 1 0 one_ne_zero
  have hP (i : Fin 6) : pencilRatio p i = v i / mixed q :=
    projector_ratio v i 4 hm
  refine ⟨ht, hd, ?_, ?_⟩
  · rw [mixedRatio, hs, hP]
    change 1 - 2 * q 3 * ((q 0 - q 1) / mixed q) ≠ 0
    have he : 1 - 2 * q 3 * ((q 0 - q 1) / mixed q) = (mixed q)⁻¹ := by
      field_simp [hm]
      unfold mixed
      ring
    rw [he]
    exact inv_ne_zero hm
  · rw [hP]
    exact div_ne_zero ha hm

private theorem special_coordinates (i : Fin 4) :
    squareTrace (complexParameter (center i)) ≠ 0 ∧ mixed (complexParameter (center i)) = 1 ∧
      center i 8 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hr := congrArg Complex.re h
    fin_cases i <;>
      norm_num [squareTrace, complexParameter, center, PeriodicMPSFiveSiteSpecialJets.source,
        source0, source1, source2, source3, Complex.sub_re, Complex.mul_re] at hr
  · fin_cases i <;>
      norm_num [mixed, complexParameter, center, PeriodicMPSFiveSiteSpecialJets.source,
        source0, source1, source2, source3, Complex.ext_iff]
  · fin_cases i <;>
      norm_num [center, PeriodicMPSFiveSiteSpecialJets.source, source0, source1, source2, source3]

/-- The four source points underlying the verified raw graphs. -/
def specialPoint (i : Fin 4) : source :=
  ⟨rawSource (center i), valid_rawSource _ (special_coordinates i).1⟩

theorem specialPoint_in_chart (i : Fin 4) : (specialPoint i).val ∈ ambientDomain :=
  affineDomain (special_coordinates i).1 (by rw [(special_coordinates i).2.1]; exact one_ne_zero)

theorem specialPoint_in_ordinary (i : Fin 4) : (specialPoint i).val ∈ chartDomain := by
  let q := complexParameter (center i)
  obtain ⟨u, hu⟩ := affine_mem_ordinary (q 0) (q 1) (q 2) (q 3) (special_coordinates i).1
  change ordinary u = (specialPoint i).val at hu
  have h : (ordinary u).1.1 0 0 ≠ 0 :=
    hu.symm ▸ (specialPoint_in_chart i).1
  rw [← hu]
  exact ordinary_mem_chartDomain u ((projector_diag_ne_zero_iff (traceDirection u.val) 0).mp h)

private def sign (i : Fin 4) : ℂ := if i.val < 2 then 1 else -1

private def second (i : Fin 4) : Bool := decide (i.val % 2 = 1)

private theorem sign_cases (i : Fin 4) : sign i = 1 ∨ sign i = -1 := by
  unfold sign
  split <;> simp

private theorem specialPoint_eq (i : Fin 4) : (specialPoint i).val = specialLift (sign i) (second i) := by
  change rawSource (center i) = specialLift (sign i) (second i)
  fin_cases i <;>
    simp [rawSource, fromFour, center, PeriodicMPSFiveSiteSpecialJets.source, source0, source1,
      source2, source3, specialLift, sign, second, root, b, complexParameter] <;>
    congr 1 <;> apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      pow_two]

theorem specialPoint_observation (i : Fin 4) :
    observation (specialPoint i).val = specialObservation := by
  rw [specialPoint_eq]
  exact (specialLift_mem _ _ (sign_cases i)).2

theorem specialPoint_exhausts {p : source} (h : observation p.val = specialObservation) :
    ∃ i, p = specialPoint i := by
  obtain ⟨s, t, hs, he⟩ := compact_special_fiber_subset p.property h
  rcases hs with rfl | rfl <;> cases t
  · exact ⟨0, Subtype.ext (he.trans (specialPoint_eq 0).symm)⟩
  · exact ⟨1, Subtype.ext (he.trans (specialPoint_eq 1).symm)⟩
  · exact ⟨2, Subtype.ext (he.trans (specialPoint_eq 2).symm)⟩
  · exact ⟨3, Subtype.ext (he.trans (specialPoint_eq 3).symm)⟩

private def amp (q : Q) : Fin 8 → ℂ := chart (q 3) (q 0) (q 1) 1 (q 2)

private def massOf (q : Q) : ℝ := mass (amp q)

private theorem massOf_pos (q : Q) : 0 < massOf q :=
  mass_positive _ (chart_ne_zero _ _ _ _)

private theorem continuous_trace_raw : Continuous (rawTrace ∘ raw : E → ℝ) := by
  have h (k : Fin 10) : Continuous (fun u : E => raw u k) :=
    continuous_iff_continuousAt.mpr fun u => (analytic_raw u k).continuousAt
  change Continuous (fun u : E => raw u 0 + 2 * raw u 5 + raw u 9)
  fun_prop

private def rebuild (p : Ambient) (τ : ℝ) : E :=
  let q := affineInverse p
  pack q (τ / massOf q)

private theorem rebuild_center (i : Fin 4) :
    rebuild (specialPoint i).val (rawTrace (raw (center i))) = center i := by
  have hm : mixed (complexParameter (center i)) ≠ 0 := by
    rw [(special_coordinates i).2.1]
    exact one_ne_zero
  change rebuild (rawSource (center i)) _ = _
  have hInv : affineInverse (rawSource (center i)) = complexParameter (center i) :=
    affineInverse_affine _ _ _ _ hm
  unfold rebuild
  rw [hInv, raw_trace_eq]
  change pack (complexParameter (center i))
    (center i 8 * massOf (complexParameter (center i)) /
      massOf (complexParameter (center i))) = center i
  rw [mul_div_cancel_right₀ _ (massOf_pos _).ne', pack_unpack]

private theorem trace_rebuild (p : Ambient) (τ : ℝ) :
    rawTrace (raw (rebuild p τ)) = τ := by
  rw [raw_trace_eq]
  have he : mass (rayAmplitude (rebuild p τ)) = massOf (affineInverse p) := by
    unfold rayAmplitude rebuild massOf amp
    rw [unpack_pack]
  rw [he]
  exact div_mul_cancel₀ _ (massOf_pos _).ne'

private theorem raw_rebuild {p : Ambient} (hp : p ∈ source) (hC : p ∈ ambientDomain)
    {τ : ℝ} (hτ : τ ≠ 0) :
    raw (rebuild p τ) = restoreEntries τ (measured p) := by
  have hg : rebuild p τ 8 ≠ 0 := div_ne_zero hτ (massOf_pos _).ne'
  have he := raw_measured_eq (rebuild p τ) hg
  change normalizeEntries (raw (rebuild p τ)) = measured (rawSource (rebuild p τ)) at he
  have hp' : rawSource (rebuild p τ) = p := by
    unfold rawSource rebuild
    rw [unpack_pack, affine_round_trip_of_source hp hC]
  have htr := trace_rebuild p τ
  rw [hp'] at he
  have h := restore_normalize (raw (rebuild p τ)) (htr.symm ▸ hτ)
  rw [htr, he] at h
  exact h.symm

private theorem continuousAt_rebuild {p : Ambient} {t : ℝ} (hp : p ∈ ambientDomain) :
    ContinuousAt (fun x : Ambient × ℝ => rebuild x.1 x.2) (p, t) := by
  let q : Ambient × ℝ → Q := fun x => affineInverse x.1
  have hq : ContinuousAt q (p, t) :=
    ContinuousAt.comp_of_eq (f := Prod.fst) (x := (p, t))
      (continuousAt_affineInverse hp) continuous_fst.continuousAt rfl
  have hm : Continuous massOf := by
    have h : massOf = (rawTrace ∘ raw) ∘ (fun a => pack a 1) := by
      funext a
      change massOf a = rawTrace (raw (pack a 1))
      rw [raw_trace_eq]
      have hv : rayAmplitude (pack a 1) = amp a := by
        unfold rayAmplitude amp
        rw [unpack_pack]
      change massOf a = (1 : ℝ) * mass (rayAmplitude (pack a 1))
      rw [one_mul, hv]
      rfl
    rw [h]
    apply continuous_trace_raw.comp
    apply continuous_pi
    intro k
    fin_cases k <;> simp [pack] <;> fun_prop
  have hτ : ContinuousAt (fun x : Ambient × ℝ => x.2 / massOf (q x)) (p, t) :=
    continuous_snd.continuousAt.div (hm.continuousAt.comp hq) (massOf_pos _).ne'
  have hc (i : Fin 4) : ContinuousAt (fun x => q x i) (p, t) :=
    continuousAt_pi.mp hq i
  have hr (i : Fin 4) : ContinuousAt (fun x => (q x i).re) (p, t) :=
    Complex.continuous_re.continuousAt.comp (hc i)
  have hi (i : Fin 4) : ContinuousAt (fun x => (q x i).im) (p, t) :=
    Complex.continuous_im.continuousAt.comp (hc i)
  apply continuousAt_pi.mpr
  intro k
  fin_cases k <;> first | exact hr _ | exact hi _ | exact hτ

private theorem eventually_valid (i : Fin 4) :
    ∀ᶠ u in 𝓝 (center i), rawSource u ∈ source := by
  have h : Continuous (fun u => squareTrace (complexParameter u)) := by
    have h₀ (k : Fin 4) := (continuous_apply k).comp continuous_complexParameter
    unfold squareTrace
    fun_prop
  filter_upwards [h.continuousAt (isOpen_ne.mem_nhds (special_coordinates i).1)] with u hu
  exact valid_rawSource u hu

private theorem rawTrace_pos_center (i : Fin 4) : 0 < rawTrace (raw (center i)) := by
  rw [raw_trace_eq, (special_coordinates i).2.2, one_mul]
  exact massOf_pos _

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialGerms
