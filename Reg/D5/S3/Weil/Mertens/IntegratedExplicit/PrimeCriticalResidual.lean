import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual
import D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass
import Reg.Support.SingleDependentReadout

/-! The real contribution of the maximal line is measured by the real part of
its complex series. A constant exaggerated readout violates the root-scale
bound at the admissible upper bound one. For the window alternative, a small
constant exponential collapses the local window and the intermediate sum,
while the normalized wide-window mass diverges. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass
  (prime_tail_wide_window_mass)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)
open _root_.MaximalRealPartProjection (maximalSeries)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual

abbrev lineSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actualLine : Realization lineSignature :=
  realize lineSignature (fun _ _ => Complex.re) (fun e => nomatch e)

private def coefficientNormSum : ℝ := ∑' k : ℕ, ‖actualCoeff k‖

def exaggeratedLine : Realization lineSignature :=
  realize lineSignature (fun _ _ _ => coefficientNormSum + 1) (fun e => nomatch e)

def rootScaleArena : Arena where
  signature := lineSignature
  Law V :=
    let lineRealPart := V.readout () ()
    (∀ β t : ℝ, Summable
      (fun k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β} =>
        ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * t))) ∧
    ∀ d : ℝ, 0 < d → d < 2 - (101 / 100 : ℝ) * firstLiMass →
      ∀ᶠ t : ℝ in atTop, ∀ β : ℝ, 1 / 2 < β →
        (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
        Real.exp (t / 2) * primeTail (Real.exp t) ≤
          Real.exp ((β - 1 / 2) * t) * (-lineRealPart (maximalSeries actualCoeff actualZero β t)) +
            (∑' k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β},
              ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * t)) - d

private theorem one_lt_margin_bound : (1 : ℝ) < 2 - (101 / 100 : ℝ) * firstLiMass := by
  linarith only [firstLiMass_lt_third]

private theorem exaggeratedLine_fails : ¬ rootScaleArena.Law exaggeratedLine := by
  intro h
  have htend : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨t, ht, hroot, htail⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((h.2 1 zero_lt_one one_lt_margin_bound).and ((htend.comp Real.tendsto_exp_atTop).eventually_const_lt
      (show (-1 : ℝ) < 0 by norm_num)))).exists
  let intermediate : Set ℕ := {k | 1 / 2 < (actualZero k).re ∧ (actualZero k).re < 1}
  have hscaled : (∑' k : intermediate,
      ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * t)) ≤
      coefficientNormSum * Real.exp (t / 2) := by
    calc
      _ ≤ ∑' k : intermediate, ‖actualCoeff k.1‖ * Real.exp (t / 2) := by
        refine (h.1 1 t).tsum_le_tsum (fun k => ?_)
          ((actualCoeff_hasSum.summable.norm.subtype intermediate).mul_right _)
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        calc
          _ ≤ (1 - 1 / 2) * t :=
            mul_le_mul_of_nonneg_right (sub_le_sub_right k.2.2.le _) ht
          _ = t / 2 := by ring
      _ ≤ _ := by
        rw [tsum_mul_right]
        exact mul_le_mul_of_nonneg_right
          (actualCoeff_hasSum.summable.norm.tsum_subtype_le _ intermediate (fun _ => norm_nonneg _))
          (Real.exp_nonneg _)
  have hbad := hroot 1 (by norm_num) (fun _ hz => hz.2.2.le)
  change Real.exp (t / 2) * primeTail (Real.exp t) ≤
    Real.exp ((1 - 1 / 2) * t) * -(coefficientNormSum + 1) +
      (∑' k : intermediate, ‖actualCoeff k.1‖ *
        Real.exp (((actualZero k.1).re - 1 / 2) * t)) - 1 at hbad
  rw [show (1 - 1 / 2 : ℝ) * t = t / 2 by ring] at hbad
  have hbad' : Real.exp (t / 2) * primeTail (Real.exp t) ≤ Real.exp (t / 2) * (-1) := by
    linarith only [hbad, hscaled,
      show Real.exp (t / 2) * -(coefficientNormSum + 1) + coefficientNormSum * Real.exp (t / 2) =
        Real.exp (t / 2) * (-1) by ring]
  exact (not_lt.mpr hbad') (mul_lt_mul_of_pos_left htail (Real.exp_pos _))

private theorem actualLine_dependence : ObservationalDependence lineSignature actualLine := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def rootScaleFamily : Registration rootScaleArena (type_of% @eventually_prime_tail_root_scale) where
  actual := actualLine
  bridge := Iff.rfl
  variation := ⟨eventually_prime_tail_root_scale, exaggeratedLine, exaggeratedLine_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    rootScaleArena.Law actualLine exaggeratedLine exaggeratedLine_fails
  dependence := actualLine_dependence

def rootScaleRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventually_prime_tail_root_scale) (Realization lineSignature) Unit Unit where
  unitName := .str ``eventually_prime_tail_root_scale "__information_unit"
  realizationName := ``rootScaleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rootScaleArena⟩
  objectArena := .source ⟨rootScaleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootScaleArena ⟨rootScaleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lineSignature (fun _ _ => Complex.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev scaleSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actualScale : Realization scaleSignature :=
  realize scaleSignature (fun _ _ => Real.exp) (fun e => nomatch e)

private def collapsedValue : ℝ := (coefficientNormSum + 1)⁻¹

def collapsedScale : Realization scaleSignature :=
  realize scaleSignature (fun _ _ _ => collapsedValue) (fun e => nomatch e)

def windowArena : Arena where
  signature := scaleSignature
  Law V :=
    let scale := V.readout () ()
    ∀ d : ℝ, 0 < d → d < 2 - (101 / 100 : ℝ) * firstLiMass →
      ∃ T : ℝ, ∀ β : ℝ, 1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
        ∀ t W : ℝ, 0 < W → T ≤ t - W →
          0 < (∫ x in scale (t - W)..scale t, max (-primeTail x) 0 / Real.sqrt x) ∨
          (∃ u ∈ Icc (t - W) t, d ≤
            ∑' k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β},
              ‖actualCoeff k.1‖ * scale (((actualZero k.1).re - 1 / 2) * u)) ∨
          ∃ W' > W, MapClusterPt 0 atTop (fun B : ℝ =>
            (∫ x in scale (Real.log B - W')..B, max (-primeTail x) 0 / Real.sqrt x) /
              scale (Real.log B * (β - 1 / 2)))

private theorem continuousOn_density_above {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    ContinuousOn (fun x : ℝ => max (-primeTail x) 0 / Real.sqrt x) (Ici a) := by
  let kernel (x : ℝ) := (Chebyshev.theta x - x) / x ^ 2
  have hinterval : IntervalIntegrable (fun x : ℝ => -1 / x) volume a 1 :=
    (continuousOn_const.div continuousOn_id
      (fun _ hx => (ha.trans_le hx.1).ne')).intervalIntegrable_of_Icc ha₁
  have hshort : IntegrableOn kernel (Ioc a 1) := by
    refine hinterval.1.congr_fun (fun x hx => ?_) measurableSet_Ioc
    dsimp [kernel]
    rw [Chebyshev.theta_eq_zero_of_le_one hx.2]
    field_simp [(ha.trans hx.1).ne']
    ring
  have hIoi : Ioi a = Ioc a 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi ha₁).symm
  have hkernel : IntegrableOn kernel (Ioi a) := hIoi ▸ hshort.union prime_integrable
  exact (hkernel.continuousOn_Ici_primitive_Ioi.neg.sup continuousOn_const).div
    Real.continuous_sqrt.continuousOn
    (fun _ hx => (Real.sqrt_pos.mpr (ha.trans_le hx)).ne')

private theorem collapsedScale_fails : ¬ windowArena.Law collapsedScale := by
  have hC : 0 ≤ coefficientNormSum := tsum_nonneg fun _ => norm_nonneg _
  have hc : 0 < collapsedValue := inv_pos.mpr (by linarith only [hC])
  have hc₁ : collapsedValue ≤ 1 := (inv_le_one₀ (by linarith only [hC])).mpr
    (by linarith only [hC])
  have hsmall : coefficientNormSum * collapsedValue < 1 := by
    rw [collapsedValue, ← div_eq_mul_inv, div_lt_iff₀ (by linarith only [hC])]
    linarith
  intro h
  obtain ⟨T, hT⟩ := h 1 zero_lt_one one_lt_margin_bound
  rcases hT 1 (by norm_num) (fun _ hz => hz.2.2.le) (T + 1) 1 zero_lt_one (by linarith) with
    hlocal | ⟨u, hu, hlarge⟩ | ⟨W', hW', hcluster⟩
  · change 0 < ∫ x in collapsedValue..collapsedValue, max (-primeTail x) 0 / Real.sqrt x at hlocal
    simp only [intervalIntegral.integral_same, lt_irrefl] at hlocal
  · let intermediate : Set ℕ := {k | 1 / 2 < (actualZero k).re ∧ (actualZero k).re < 1}
    change 1 ≤ ∑' k : intermediate, ‖actualCoeff k.1‖ * collapsedValue at hlarge
    rw [tsum_mul_right] at hlarge
    have hnorms := actualCoeff_hasSum.summable.norm.tsum_subtype_le _ intermediate
      (fun _ => norm_nonneg _)
    exact hsmall.not_ge (hlarge.trans (mul_le_mul_of_nonneg_right hnorms hc.le))
  · let density (x : ℝ) := max (-primeTail x) 0 / Real.sqrt x
    change MapClusterPt 0 atTop (fun B : ℝ => (∫ x in collapsedValue..B, density x) /
      collapsedValue) at hcluster
    obtain ⟨C, _, hwide⟩ := (prime_tail_wide_window_mass 2 (by norm_num)).2
    have hlog : Tendsto (fun B : ℝ => Real.log (B / 2)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have hbound : ∀ᶠ B : ℝ in atTop,
        1 ≤ (∫ x in collapsedValue..B, density x) / collapsedValue := by
      filter_upwards [eventually_ge_atTop (4 : ℝ),
        hlog.eventually_ge_atTop ((C + 1) / 2)] with B hB hBlarge
      have h₂B : 2 ≤ B := (by norm_num : (2 : ℝ) ≤ 4).trans hB
      have hfour : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_two]
      have hwide' := hwide 2 B le_rfl (hfour.le.trans hB)
      have hle : collapsedValue ≤ 2 := hc₁.trans one_le_two
      have hdensity : IntervalIntegrable density volume collapsedValue B :=
        ((continuousOn_density_above hc hc₁).mono
          (fun _ hx => hx.1)).intervalIntegrable_of_Icc (hle.trans h₂B)
      have hmono := intervalIntegral.integral_mono_interval hle h₂B le_rfl
        (Eventually.of_forall fun _ => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
        hdensity
      apply (le_div_iff₀ hc).mpr
      linarith only [hwide', hBlarge, hmono, hc₁]
    have hopen : ∃ᶠ B : ℝ in atTop, (∫ x in collapsedValue..B, density x) / collapsedValue < 1 :=
      hcluster.frequently (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact (hopen.and_eventually hbound).exists.elim fun _ h => h.1.not_ge h.2

private theorem actualScale_dependence : ObservationalDependence scaleSignature actualScale := by
  intro _
  exact ⟨(), 0, 1, Real.exp_lt_exp.mpr zero_lt_one |>.ne⟩

def windowFamily : Registration windowArena
    (type_of% @prime_tail_mass_pos_or_intermediate_or_wider_zero_cluster) where
  actual := actualScale
  bridge := Iff.rfl
  variation := ⟨prime_tail_mass_pos_or_intermediate_or_wider_zero_cluster,
    collapsedScale, collapsedScale_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    windowArena.Law actualScale collapsedScale collapsedScale_fails
  dependence := actualScale_dependence

def windowRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_mass_pos_or_intermediate_or_wider_zero_cluster)
      (Realization scaleSignature) Unit Unit where
  unitName := .str ``prime_tail_mass_pos_or_intermediate_or_wider_zero_cluster "__information_unit"
  realizationName := ``windowFamily
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scaleSignature (fun _ _ => Real.exp) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual
