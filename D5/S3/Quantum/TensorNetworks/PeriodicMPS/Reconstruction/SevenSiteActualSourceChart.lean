/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteActualSourceChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteActualSourceChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: An actual-state chart at the seven-site hard-core projector. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformHardCoreCompactRecovery
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteActualSourceChart

open Set Filter Function
open scoped Topology ENNReal NNReal Matrix.Norms.Elementwise
open PeriodicMPSUniformHardCoreLocalization
open PeriodicMPSUniformHardCorePencilDecoder
  (Tensor ordinaryInvariants ordinaryDecoder exists_open_ordinaryDecoder witnessTensor
    guardedPolynomial pencilCoefficients firstRoot secondRoot
    analyticAt_firstRoot analyticAt_secondRoot contract p0 p1 p2)
open PeriodicMPSUniformDeterminantPencil (guardedFlattening observedFlattening)
open PeriodicMPSUniformHardCoreFirstJet (Coord cores witness)
open PeriodicMPSUniformHardCoreWitnessAmplitude (traceWord_witnessCore_eq_indicator)
open PeriodicMPSProjectiveCoordinates (projector projector_diag_ne_zero_iff projector_scale)
open UniformMPSExpectedDimensionRefutation (traceWord)

open private vacuum vacuumChart continuousAt_vacuumChart vacuumChart_projector witnessTensor_vacuum
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization
open private fromOrdinary fromOrdinary_base continuousAt_fromOrdinary
  chartTrace chartB chartA chartD coreInvariants eventually_chartTrace traceWord_eq_scaled_chart
  chartProjector continuousAt_chartProjector eventually_nonzero_traceWord
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticChart
open private traceWord_witness
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature
open private roots physicalFrame frame ratios fromFrame guardedCoeff_zero_witness
  pencilCoefficients_witness physicalFrame_witness roots_witness p012_witness
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCorePencilDecoder

noncomputable section

abbrev Parameters := ℂ × ℂ × ℂ × ℂ
abbrev Source := closure (actualProjectors 5)

def center : Source :=
  ⟨witnessProjector 5, subset_closure (witnessProjector_mem_actualProjectors (by decide))⟩

/-- The vacuum-column ratios fix the representative used by the pencil decoder. -/
def decode (P : StateMatrix 5) : Parameters := ordinaryDecoder 7 (by decide) (vacuumChart P)

private theorem analyticAt_guardedCoeff (T : Tensor 7) (j : ℕ) :
    AnalyticAt ℂ (fun S : Tensor 7 => (guardedPolynomial 7 (by decide) S).coeff j) T := by
  have entry (v : Fin 2 → ℂ) (i k : PeriodicMPSUniformDeterminantPencil.Guard) :
      AnalyticAt ℂ (fun S : Tensor 7 => guardedFlattening 7 (by decide) S v i k) T := by
    unfold guardedFlattening observedFlattening
    exact Finset.analyticAt_fun_sum _ fun a _ =>
      analyticAt_const.mul ((ContinuousLinearMap.proj _ : Tensor 7 →L[ℂ] ℂ).analyticAt T)
  classical
  have prodCoeff {ι : Type} (s : Finset ι) (F : ι → Tensor 7 → Polynomial ℂ)
      (h : ∀ i ∈ s, ∀ k, AnalyticAt ℂ (fun S => (F i S).coeff k) T) (k : ℕ) :
      AnalyticAt ℂ (fun S => (∏ i ∈ s, F i S).coeff k) T := by
    induction s using Finset.induction generalizing k with
    | empty => simpa using analyticAt_const
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
      exact Finset.analyticAt_fun_sum _ fun l _ =>
        (h i (Finset.mem_insert_self i s) l.1).mul
          (ih (fun a ha => h a (Finset.mem_insert_of_mem ha)) l.2)
  simp only [guardedPolynomial, Matrix.det_apply', Polynomial.finsetSum_coeff,
    ← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, Matrix.of_apply]
  refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (prodCoeff _ _ ?_ _)
  intro i _ k
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
  split_ifs <;> simp only [mul_one, mul_zero, zero_add, add_zero]
  all_goals
    first
    | exact entry 1 _ _
    | exact entry ![0, 1] _ _
    | exact (entry 1 _ _).add (entry ![0, 1] _ _)
    | exact analyticAt_const

private theorem analyticAt_witnessDecoder :
    AnalyticAt ℂ (ordinaryDecoder 7 (by decide)) (witnessTensor 7) := by
  let hn : 7 ≤ 7 := by decide
  let T := witnessTensor 7
  have hH : (guardedPolynomial 7 hn T).coeff 0 ≠ 0 := by
    rw [guardedCoeff_zero_witness]
    exact neg_ne_zero.mpr one_ne_zero
  have h (i : ℕ) := analyticAt_guardedCoeff T i
  have h₁ := (h 1).div (analyticAt_const (v := (2 : ℂ)).mul (h 0))
    (mul_ne_zero two_ne_zero hH)
  have hcoeff : AnalyticAt ℂ (pencilCoefficients 7 hn) T :=
    h₁.prod ((((h 2).div (h 0) hH).sub (h₁.pow 2)).div_const)
  have hbase : pencilCoefficients 7 hn T = (1, 0) := pencilCoefficients_witness 7 hn
  have ha : AnalyticAt ℂ (fun S => (roots 7 hn S).1) T :=
    analyticAt_firstRoot.comp_of_eq hcoeff hbase
  have hb : AnalyticAt ℂ (fun S => (roots 7 hn S).2) T :=
    analyticAt_secondRoot.comp_of_eq hcoeff hbase
  have hU (i j : Fin 2) : AnalyticAt ℂ (fun S => physicalFrame 7 hn S i j) T := by
    fin_cases i <;> fin_cases j <;> first | exact analyticAt_const | exact ha | exact hb
  have hcontract (w : PeriodicMPSParentIntersection.Word 7) :
      AnalyticAt ℂ (fun S => contract (physicalFrame 7 hn S) S w) T := by
    unfold contract
    exact Finset.analyticAt_fun_sum _ fun u _ =>
      (Finset.analyticAt_fun_prod _ fun i _ => hU (w i) (u i)).mul
        ((ContinuousLinearMap.proj u : Tensor 7 →L[ℂ] ℂ).analyticAt T)
  obtain ⟨h0, h1, _⟩ := p012_witness 7 (by decide)
  have hn0 : p0 (physicalFrame 7 hn T) T ≠ 0 := by
    rw [show T = witnessTensor 7 from rfl, physicalFrame_witness, h0]
    exact one_ne_zero
  have hn1 : p1 (by decide) (physicalFrame 7 hn T) T ≠ 0 := by
    rw [show T = witnessTensor 7 from rfl, physicalFrame_witness, h1]
    exact one_ne_zero
  have hv : AnalyticAt ℂ (fun S => (ratios 7 hn S).1) T :=
    (hcontract _).div (hcontract _) hn1
  have hk : AnalyticAt ℂ (fun S => (ratios 7 hn S).2) T :=
    (hcontract _).div (hcontract _) hn0
  have ht := (analyticAt_const (v := (1 : ℂ))).sub (ha.mul hv)
  have ht0 : 1 - (roots 7 hn T).1 * (ratios 7 hn T).1 ≠ 0 := by
    rw [show T = witnessTensor 7 from rfl, roots_witness]
    simp
  change AnalyticAt ℂ
    (fun S => fromFrame (roots 7 hn S).1 (roots 7 hn S).2 (ratios 7 hn S).1 (ratios 7 hn S).2) T
  exact ((hv.sub hb).div ht ht0).prod
    (((ha.neg.mul (hv.sub hk)).div (ht.pow 2) (pow_ne_zero 2 ht0)).prod
      (((hb.neg.mul (hv.sub hk)).div (ht.pow 2) (pow_ne_zero 2 ht0)).prod
        (((((analyticAt_const.add (ha.mul hb)).mul hk).sub hb).sub
          (ha.mul (hv.pow 2))).div (ht.pow 2) (pow_ne_zero 2 ht0))))

private def amplitude (p : Parameters) := traceWord 2 2 7 (cores (fromOrdinary p))

private def encode (p : Parameters) : Source :=
  if hp : amplitude p ≠ 0 then
    ⟨projector (amplitude p), subset_closure ⟨cores (fromOrdinary p), hp, rfl⟩⟩
  else center

private theorem encode_val {p : Parameters} (hp : amplitude p ≠ 0) :
    (encode p).val = projector (amplitude p) := by simp [encode, hp]

private theorem ordinaryInvariants_fromOrdinary (p : Parameters) (ht : chartTrace p ≠ 0)
    (hb : chartB p ≠ 0) (ha : chartA p = p.2.1 * chartTrace p ^ 2) :
    ordinaryInvariants (cores (fromOrdinary p)) = p := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := coreInvariants p
  have hm : chartB p + chartA p * chartD p = chartTrace p ^ 2 * p.2.2.2 := by
    simp [chartB]
  unfold ordinaryInvariants
  rw [h₀, h₁, h₂, h₃, h₄, hm, ha, chartD]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> dsimp <;> field_simp

private theorem encode_center : encode (0, 0, 0, 1) = center := by
  have ha : amplitude (0, 0, 0, 1) = witnessTensor 7 := by
    rw [amplitude, fromOrdinary_base, witnessTensor]
    exact funext fun w => (traceWord_witness 7 (by decide) w).trans
      (traceWord_witnessCore_eq_indicator (by decide) w).symm
  have hn : amplitude (0, 0, 0, 1) ≠ 0 := by
    rw [ha]
    intro h
    have hz := congrFun h (vacuum 5)
    rw [witnessTensor_vacuum (show 7 ≤ 2 + 5 by decide)] at hz
    exact one_ne_zero hz
  apply Subtype.ext
  rw [encode_val hn, ha]
  rfl

private theorem eventually_continuousAt_fromOrdinary :
    ∀ᶠ p : Parameters in 𝓝 (0, 0, 0, 1), ContinuousAt fromOrdinary p := by
  let a : Parameters → ℂ × ℂ := fun p => (1, p.2.1)
  have ha : Continuous a := by fun_prop
  have hroot := PeriodicMPSUniformHardCorePencilDecoder.analyticAt_firstRoot
  filter_upwards [ha.continuousAt.eventually hroot.eventually_continuousAt,
    eventually_chartTrace (0, 0, 0, 1) rfl] with p hp hgood
  have hA : ContinuousAt chartA p := (hp.comp ha.continuousAt).neg
  have ht : ContinuousAt chartTrace p := continuousAt_const.add hA
  have hD : ContinuousAt chartD p := ht.mul continuous_fst.continuousAt
  have hB : ContinuousAt chartB p :=
    ((ht.pow 2).mul continuous_snd.snd.snd.continuousAt).sub (hA.mul hD)
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact hA
  · exact hB
  · exact (((ht.pow 2).mul continuous_snd.snd.fst.continuousAt).neg).div hB hgood.2.1
  · exact hD

private def chartOfLocalInverse {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (g : Y → X) {S : Set X} {T : Set Y}
    (hS : IsOpen S) (hT : IsOpen T) (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (hleft : ∀ x ∈ S, f x ∈ T → g (f x) = x)
    (hright : ∀ y ∈ T, g y ∈ S → f (g y) = y) :
    OpenPartialHomeomorph X Y where
  toFun := f
  invFun := g
  source := S ∩ f ⁻¹' T
  target := T ∩ g ⁻¹' S
  map_source' x hx := by
    refine ⟨hx.2, ?_⟩
    change g (f x) ∈ S
    rw [hleft x hx.1 hx.2]
    exact hx.1
  map_target' y hy := by
    refine ⟨hy.2, ?_⟩
    change f (g y) ∈ T
    rw [hright y hy.1 hy.2]
    exact hy.1
  left_inv' x hx := hleft x hx.1 hx.2
  right_inv' y hy := hright y hy.1 hy.2
  open_source := hf.isOpen_inter_preimage hS hT
  open_target := hg.isOpen_inter_preimage hT hS
  continuousOn_toFun := hf.mono inter_subset_left
  continuousOn_invFun := hg.mono inter_subset_left

private theorem lipschitzOn_subtype {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} {K : ℝ≥0} {A M : Set X} {S : Set A}
    (hf : LipschitzOnWith K f M) (hS : MapsTo Subtype.val S M) :
    LipschitzOnWith K (f ∘ Subtype.val) S :=
  fun _ hx _ hy => hf (hS hx) (hS hy)

set_option maxHeartbeats 1500000 in
/-- The existing tensor decoder and compact witness guard give an ordinary
four-complex-parameter chart with relatively open target in the compact source. -/
theorem exists_witness_chart :
    ∃ (c : OpenPartialHomeomorph Parameters Source) (K : ℝ≥0),
      center ∈ c.target ∧ (0, 0, 0, 1) ∈ c.source ∧
      EqOn c encode c.source ∧ EqOn c.symm (decode ∘ Subtype.val) c.target ∧
      LipschitzOnWith K c.symm c.target ∧ ∀ P ∈ c.target, P.val ∈ actualProjectors 5 := by
  let p₀ : Parameters := (0, 0, 0, 1)
  obtain ⟨V, hVo, hwV, hcont, hread⟩ := exists_open_ordinaryDecoder 7 (by decide)
  obtain ⟨W, hWo, hwW, hactual⟩ :=
    PeriodicMPSUniformHardCoreCompactRecovery.exists_open_guard_actual 3 (by decide)
  have hwvac : witnessTensor 7 (vacuum 5) = 1 :=
    witnessTensor_vacuum (show 7 ≤ 2 + 5 by decide)
  have hdiag : center.val (vacuum 5) (vacuum 5) ≠ 0 :=
    (projector_diag_ne_zero_iff _ _).2 (hwvac.trans_ne one_ne_zero)
  have hrep : vacuumChart (m := 5) center.val = witnessTensor 7 := by
    rw [show center.val = witnessProjector 5 from rfl, witnessProjector]
    rw [vacuumChart_projector _ (hwvac.trans_ne one_ne_zero), hwvac, inv_one, one_smul]
  have hdec : decode center.val = p₀ := by
    simp [decode, hrep, p₀]
  have hratio : AnalyticAt ℂ (vacuumChart (m := 5)) center.val := by
    refine AnalyticAt.pi fun u => ?_
    let entry (w : PeriodicMPSParentIntersection.Word 7) : StateMatrix 5 →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (vacuum 5) : Tensor 7 →L[ℂ] ℂ).comp
        (ContinuousLinearMap.proj w : StateMatrix 5 →L[ℂ] Tensor 7)
    exact ((entry u).analyticAt _).div ((entry (vacuum 5)).analyticAt _) hdiag
  have hdSmooth : ContDiffAt ℂ 1 decode center.val :=
    (analyticAt_witnessDecoder.comp_of_eq hratio hrep).contDiffAt
  obtain ⟨K, M, hM, hLip⟩ := hdSmooth.exists_lipschitzOnWith
  have hentry : Continuous (fun P : StateMatrix 5 => P (vacuum 5) (vacuum 5)) :=
    (continuous_apply _).comp (continuous_apply _)
  have hGnear : ∀ᶠ P : StateMatrix 5 in 𝓝 center.val,
      P (vacuum 5) (vacuum 5) ≠ 0 ∧ vacuumChart P ∈ V ∧ twoSiteObservation 5 P ∈ W :=
    (hentry.continuousAt.eventually_ne hdiag).and
      (((continuousAt_vacuumChart hdiag).eventually (hVo.mem_nhds (hrep ▸ hwV))).and
        ((continuous_twoSiteObservation 5).continuousAt.eventually (hWo.mem_nhds hwW)))
  obtain ⟨G, hGsub, hGo, hGw⟩ := mem_nhds_iff.mp (inter_mem hGnear hM)
  have hG : G ⊆ {P | P (vacuum 5) (vacuum 5) ≠ 0 ∧ vacuumChart P ∈ V ∧
      twoSiteObservation 5 P ∈ W} := hGsub.trans inter_subset_left
  have hGM : G ⊆ M := hGsub.trans inter_subset_right
  have hDcont : ∀ P ∈ G, ContinuousAt decode P := by
    intro P hP
    exact ((hcont _ (hG hP).2.1).continuousAt (hVo.mem_nhds (hG hP).2.1)).comp
      (continuousAt_vacuumChart (hG hP).1)
  have hDactual (P : Source) (hP : P.val ∈ G) : P.val ∈ actualProjectors 5 :=
    hactual _ P.property (hG hP).2.2
  have hDcorrect (A : Fin 2 → PeriodicMPSParentIntersection.Bond)
      (hP : projector (traceWord 2 2 7 A) ∈ G) :
      (A 0).trace ≠ 0 ∧ decode (projector (traceWord 2 2 7 A)) = ordinaryInvariants A := by
    let T : PeriodicMPSUniformHardCorePencilDecoder.Tensor 7 := traceWord 2 2 7 A
    have hT : T (vacuum 5) ≠ 0 := (projector_diag_ne_zero_iff _ _).1 (hG hP).1
    have hrepA := vacuumChart_projector (m := 5) T hT
    exact hread (vacuumChart (m := 5) (projector T)) (hG hP).2.1 A
      ((T (vacuum 5))⁻¹) hrepA
  have hgood : ∀ᶠ p in 𝓝 p₀,
      chartTrace p ≠ 0 ∧ chartB p ≠ 0 ∧ chartA p = p.2.1 * chartTrace p ^ 2 :=
    eventually_chartTrace p₀ rfl
  have hFne : ∀ᶠ p in 𝓝 p₀, amplitude p ≠ 0 := by
    have hfrom : Tendsto fromOrdinary (𝓝 p₀) (𝓝 witness) := by
      rw [← fromOrdinary_base]
      exact continuousAt_fromOrdinary
    exact hfrom.eventually (eventually_nonzero_traceWord 3 (by decide))
  obtain ⟨S, hS, hSo, hSw⟩ := mem_nhds_iff.mp
    (hgood.and (hFne.and eventually_continuousAt_fromOrdinary))
  have hEcont : ContinuousOn encode S := by
    intro p hp
    have hfrom : ContinuousWithinAt fromOrdinary S p := (hS hp).2.2.continuousWithinAt
    apply Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr
    have hFn : ContinuousWithinAt (fun q => projector (amplitude q)) S p :=
      (continuousAt_chartProjector 3 (fromOrdinary p) (hS hp).2.1).comp_continuousWithinAt hfrom
    exact hFn.congr (fun q hq => encode_val (hS hq).2.1) (encode_val (hS hp).2.1)
  have hleft (p : Parameters) (hp : p ∈ S) (hG' : (encode p).val ∈ G) :
      decode (encode p).val = p := by
    obtain ⟨⟨ht, hb, ha⟩, hne, _⟩ := hS hp
    rw [encode_val hne] at hG' ⊢
    exact (hDcorrect _ hG').2.trans (ordinaryInvariants_fromOrdinary p ht hb ha)
  have hright (P : Source) (hP : P.val ∈ G) (hS' : decode P.val ∈ S) :
      encode (decode P.val) = P := by
    obtain ⟨A, _, hA⟩ := hDactual P hP
    change projector (traceWord 2 2 7 A) = P.val at hA
    have hG' : projector (traceWord 2 2 7 A) ∈ G := hA.symm ▸ hP
    have hcore := hDcorrect A hG'
    obtain ⟨⟨ht, hb, ha⟩, hne, _⟩ := hS hS'
    obtain ⟨z, hz, hscale⟩ := traceWord_eq_scaled_chart A hcore.1
      (hA ▸ hcore.2) ht hb ha 7
    apply Subtype.ext
    rw [encode_val hne, amplitude]
    exact ((congrArg projector hscale).trans (projector_scale _ hz)).symm.trans hA
  let T : Set Source := Subtype.val ⁻¹' G
  let d : Source → Parameters := decode ∘ Subtype.val
  have hTo : IsOpen T := hGo.preimage continuous_subtype_val
  have hdt : ContinuousOn d T := fun P hP =>
    ((hDcont P.val hP).comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hcenterS : d center ∈ S := by
    change decode center.val ∈ S
    rwa [hdec]
  have hencodeT : encode p₀ ∈ T := by
    change (encode (0, 0, 0, 1)).val ∈ G
    rw [encode_center]
    exact hGw
  refine ⟨chartOfLocalInverse encode d hSo hTo hEcont hdt hleft hright, K,
    ⟨hGw, hcenterS⟩, ⟨hSw, hencodeT⟩, ?_, ?_, ?_, ?_⟩
  · intro p _
    rfl
  · intro P _
    rfl
  · change LipschitzOnWith K d (T ∩ d ⁻¹' S)
    exact lipschitzOn_subtype hLip (fun _ hP => hGM hP.1)
  · intro P hP
    exact hDactual P hP.1

#print axioms exists_witness_chart

end

end D5.S3.Quantum.TensorNetworks.SevenSiteActualSourceChart
