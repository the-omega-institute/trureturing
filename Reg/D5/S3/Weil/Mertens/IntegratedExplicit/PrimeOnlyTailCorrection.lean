import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

/-- The varying root normalization in the integrated limit. -/
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def zeroScale : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    Tendsto (fun x => V.readout () () x * (Q x - primeTail x)) atTop (𝓝 2) ∧
    ∀ C : ℝ, (∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) →
      (∀ x, 1 ≤ x → 0 ≤ Q x - primeTail x ∧ Q x - primeTail x ≤ 2 * C / Real.sqrt x) ∧
      ∀ a b : ℝ, 1 ≤ a → a ≤ b →
        let W := ∫ x in a..b, (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x
        0 ≤ W ∧ W ≤ 2 * C * Real.log (b / a)

private theorem zeroScale_fails : ¬ arena.Law zeroScale := by
  intro h
  have ht := h.1
  change Tendsto (fun x => (0 : ℝ) * (Q x - primeTail x)) atTop (𝓝 2) at ht
  simp only [zero_mul] at ht
  have he : (0 : ℝ) = 2 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change Real.sqrt 0 ≠ Real.sqrt 1
  norm_num

def family : Registration arena (type_of% @prime_power_window_correction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_power_window_correction, zeroScale, zeroScale_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroScale zeroScale_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_power_window_correction) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection.prime_power_window_correction
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem primeTail_two_le : primeTail 2 ≤ -1 / 4 := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have horder := ((prime_power_window_correction.2 C (fun t _ => hC t)).1 2 (by norm_num)).1
  have hQ := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable
    (t := 2) le_rfl
  change Q 2 = _ at hQ
  have hfloor : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  have hsmall : Finset.Ioc (0 : ℕ) 2 = {1, 2} := by decide
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he := Real.one_half_lt_eulerMascheroniConstant
  simp [Chebyshev.psi, hfloor, hsmall, ArithmeticFunction.vonMangoldt_apply_one] at hQ
  linarith

abbrev windowLowerArena : Arena where
  signature := signature
  Law V :=
    ∀ {a b x r : ℝ}, 1 ≤ a → a ≤ (1 - r) * x → (1 + r) * x ≤ b →
      0 < r → r ≤ 1 / 2 → primeTail x ≤ -4 * r ^ 2 →
      r ^ 3 * Real.sqrt x ≤ ∫ z in a..b, max (-primeTail z) 0 / V.readout () () z

private theorem zeroScale_fails_window_lower : ¬ windowLowerArena.Law zeroScale := by
  intro h
  have hp := h (a := 1) (b := 3) (x := 2) (r := 1 / 4)
    le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (primeTail_two_le.trans_eq (by norm_num))
  change (1 / 4 : ℝ) ^ 3 * Real.sqrt 2 ≤
    ∫ z in (1 : ℝ)..3, max (-primeTail z) 0 / 0 at hp
  simp only [div_zero, intervalIntegral.integral_zero] at hp
  exact (not_le_of_gt (by positivity :
    0 < (1 / 4 : ℝ) ^ 3 * Real.sqrt 2)) hp

def windowLowerFamily : Registration windowLowerArena (type_of% @prime_tail_negative_window_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_tail_negative_window_lower, zeroScale, zeroScale_fails_window_lower⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    windowLowerArena.Law actual zeroScale zeroScale_fails_window_lower
  dependence := actual_dependence

noncomputable def windowLowerAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_tail_negative_window_lower) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection.prime_tail_negative_window_lower
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection "windowLowerFamily"
  realizationSource := none
  generated := false
  arena := .source ⟨windowLowerArena⟩
  objectArena := .source ⟨windowLowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowLowerArena ⟨windowLowerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "fn", "arg", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)

abbrev frequencySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ → ℝ, ℝ) (fun _ => ℕ) (fun _ => ℝ)

def exponentialReadout : Realization frequencySignature :=
  realize frequencySignature (fun _ p n => Real.exp (p.2 * p.1 n)) (fun e => nomatch e)

def windowReadout : Realization frequencySignature :=
  realize frequencySignature
    (fun _ p n => ∫ t in p.1 n - Real.log 2..p.1 n, U (Real.exp t))
    (fun e => nomatch e)

abbrev frequencyArena : Arena where
  signature := frequencySignature
  Law V :=
    ∀ {u : ℕ → ℝ} {β c M : ℝ},
      Tendsto u atTop atTop →
      Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 1) →
      0 < c → 1 / 2 < β →
      (∀ᶠ n in atTop, c * V.readout () ⟨u, β⟩ n / (u n) ^ M ≤
        ∫ t in u n - Real.log 2..u n, U (Real.exp t)) →
      ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ y : ℝ in atTop, Real.exp (((3 / 2) * (β - 1 / 2) - ε) * y) ≤
        ∫ z in Real.exp y..Real.exp ((3 / 2) * y), max (-primeTail z) 0 / Real.sqrt z

private theorem primeTail_negative_part_bounded :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ≥ 1, max (-primeTail z) 0 ≤ K := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let total := ∫ t in Ioi (1 : ℝ), ‖psiErrorKernel t‖
  have htotal : 0 ≤ total :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => norm_nonneg (psiErrorKernel t))
  refine ⟨total + 2 * |C|, by positivity, ?_⟩
  intro z hz
  have hs : 1 ≤ Real.sqrt z := by simpa using Real.sqrt_le_sqrt hz
  have hnorm : ‖Q z‖ ≤ total := by
    apply (norm_integral_le_integral_norm _).trans
    exact setIntegral_mono_set chebyshev_error_kernel_integrable.norm
      (Eventually.of_forall (fun t => norm_nonneg (psiErrorKernel t)))
      (Ioi_subset_Ioi hz).eventuallySubset
  have hCorr : Q z - primeTail z ≤ 2 * |C| / Real.sqrt z :=
    ((prime_power_window_correction.2 |C| (fun t _ =>
      (hC t).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg t)))).1 z hz).2
  have hCorr' := hCorr.trans (div_le_self (by positivity : 0 ≤ 2 * |C|) hs)
  rw [Real.norm_eq_abs] at hnorm
  exact max_le (by linarith [(neg_le_abs (Q z)).trans hnorm]) (by positivity)

private theorem windowReadout_fails : ¬ frequencyArena.Law windowReadout := by
  intro h
  let u : ℕ → ℝ := fun n => n
  have hu : Tendsto u atTop atTop := tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n => (u n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hu
    apply (by simpa using hinv.const_add (1 : ℝ) :
      Tendsto (fun n => 1 + (u n)⁻¹) atTop (𝓝 1)).congr'
    filter_upwards [hu.eventually_gt_atTop 0] with n hn
    have hadd : u (n + 1) = u n + 1 := by simp [u]
    rw [hadd]
    field_simp [hn.ne']
  have hpeak : ∀ᶠ n in atTop,
      (1 : ℝ) * windowReadout.readout () ⟨u, 2⟩ n / (u n) ^ (0 : ℝ) ≤
        ∫ t in u n - Real.log 2..u n, U (Real.exp t) :=
    Eventually.of_forall fun n => by
      change (1 : ℝ) * (∫ t in u n - Real.log 2..u n, U (Real.exp t)) / (u n) ^ (0 : ℝ) ≤ _
      simp
  have hbad := h (u := u) (β := 2) (c := 1) (M := 0) hu hratio
    (by norm_num) (by norm_num) hpeak (ε := 1 / 4) (by norm_num)
  obtain ⟨K, hK0, hK⟩ := primeTail_negative_part_bounded
  have hlimit : Tendsto (fun y : ℝ => Real.exp (y / 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (by
      simpa [div_eq_mul_inv] using (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 2⁻¹)))
  obtain ⟨y, hyBad, hy0, hyK⟩ := (hbad.and
    ((eventually_ge_atTop (0 : ℝ)).and (hlimit.eventually_gt_atTop K))).exists
  have hy_order : Real.exp y ≤ Real.exp ((3 / 2) * y) := Real.exp_le_exp.mpr (by linarith)
  have hupper : (∫ z in Real.exp y..Real.exp ((3 / 2) * y),
        max (-primeTail z) 0 / Real.sqrt z) ≤ K * Real.exp ((3 / 2) * y) := by
    by_cases hi : IntervalIntegrable (fun z => max (-primeTail z) 0 / Real.sqrt z)
        volume (Real.exp y) (Real.exp ((3 / 2) * y))
    · calc
        _ ≤ ∫ _ in Real.exp y..Real.exp ((3 / 2) * y), K := by
          apply intervalIntegral.integral_mono_on hy_order hi intervalIntegrable_const
          intro z hz
          have hz1 := (Real.one_le_exp hy0).trans hz.1
          have hs : 1 ≤ Real.sqrt z := by simpa using Real.sqrt_le_sqrt hz1
          exact (div_le_self (le_max_right _ _) hs).trans (hK z hz1)
        _ ≤ _ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          nlinarith [Real.exp_nonneg y]
    · rw [intervalIntegral.integral_undef hi]
      positivity
  norm_num at hyBad
  have hn := hyBad.trans hupper
  have hsplit : Real.exp (2 * y) = Real.exp (y / 2) * Real.exp ((3 / 2) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit] at hn
  exact (not_le_of_gt hyK) (le_of_mul_le_mul_right hn (Real.exp_pos _))

private theorem exponentialReadout_dependence :
    ObservationalDependence frequencySignature exponentialReadout := by
  intro _
  refine ⟨⟨fun n : ℕ => (n : ℝ), 1⟩, 0, 1, ?_⟩
  change Real.exp ((1 : ℝ) * (0 : ℕ)) ≠ Real.exp ((1 : ℝ) * (1 : ℕ))
  exact Real.exp_injective.ne (by norm_num)

def frequencyFamily : Registration frequencyArena
    (type_of% @eventual_prime_window_lower_of_log_frequency) where
  actual := exponentialReadout
  bridge := Iff.rfl
  variation := ⟨@eventual_prime_window_lower_of_log_frequency, windowReadout, windowReadout_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    frequencyArena.Law exponentialReadout windowReadout windowReadout_fails
  dependence := exponentialReadout_dependence

noncomputable def frequencyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_prime_window_lower_of_log_frequency) (Realization frequencySignature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection.eventual_prime_window_lower_of_log_frequency
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection "frequencyFamily"
  realizationSource := none
  generated := false
  arena := .source ⟨frequencyArena⟩
  objectArena := .source ⟨frequencyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frequencyArena ⟨frequencyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature
    (fun _ p n => Real.exp (p.2 * p.1 n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
