import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
import Reg.Support.DependentFamily

/-! The observed value is the weighted sine score at the selected time. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open _root_.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
open LeanInformationAudit Filter Set
open scoped Topology BigOperators

private abbrev unitSpectrum : Spectrum where
  index := Fin 1
  gamma := fun _ => 1
  mult := fun _ => 1
  gamma_pos _ := zero_lt_one
  gamma_injective := by
    intro a b _
    exact Subsingleton.elim a b
  mult_pos _ := Nat.one_pos
  finite_le _ := Set.toFinite _

private theorem cut_one {T : ℝ} (hT : 1 ≤ T) : unitSpectrum.cut T = {(0 : Fin 1)} := by
  ext j
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  exact iff_of_true ((unitSpectrum.finite_le T).mem_toFinset.mpr hT)
    (Finset.mem_singleton_self _)

private theorem mass_one {T : ℝ} (hT : 1 ≤ T) :
    mass unitSpectrum (fun _ => 1) T = 1 := by
  rw [mass, cut_one hT, Finset.sum_singleton]

private theorem singleton_gap : HasBoxGap unitSpectrum := by
  classical
  intro η _
  refine ⟨1, zero_lt_one, fun _ => Filter.Eventually.of_forall ?_⟩
  intro X k hk _
  obtain ⟨j, hj⟩ := hk
  have hone : (1 : ℝ) ≤ |(k j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  have hsum : (∑ i, (k i : ℝ) * unitSpectrum.gamma i.val) = (k j : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      exact (hij (Subtype.ext (Subsingleton.elim (α := Fin 1) i.val j.val))).elim
    · simp
  rw [hsum, one_mul]
  exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (by
    have hjX := (unitSpectrum.finite_le X).mem_toFinset.mp j.property
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hjX) _))).trans hone

abbrev signature : Signature where
  Params := Σ S : Spectrum, Σ _ : S.index → ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => sine p.1 p.2.1 p.2.2 v) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (S : Spectrum) (w : S.index → ℝ) (_ : ∀ j, 0 ≤ w j)
    (_ : ∀ᶠ T : ℝ in atTop, 0 < mass S w T)
    (_ : ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ((S.cut X).card : ℝ) ≤ B * (X * Real.log X))
    (_ : HasBoxGap S)
    (_ : ∀ α : ℝ, 0 < α → α < 1 → ∃ q : ℝ, α ^ 2 ≤ q ∧
      Tendsto (fun T : ℝ => mass S w (T ^ α) / mass S w T) atTop (nhds q))
    {r β ε : ℝ}, 0 < r → 0 < β → 2 * (1 - (min β 1) ^ 2) < ε →
    ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ a : ℝ, ∃ u ∈ Icc a (a + Real.exp (T ^ β)),
        1 - V.readout () ⟨S, w, T⟩ (u / r) / mass S w T < ε

private theorem half_loss (V : Realization signature) (hV : arena.Law V) :
    ∃ T u : ℝ, 0 < mass unitSpectrum (fun _ => 1) T ∧
      1 - V.readout () ⟨unitSpectrum, fun _ => 1, T⟩ u /
        mass unitSpectrum (fun _ => 1) T < 1 / 2 := by
  have hpos : ∀ᶠ T : ℝ in atTop, 0 < mass unitSpectrum (fun _ => 1) T := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [mass_one hT]
    norm_num
  have hdim : ∃ B : ℝ, 0 < B ∧ ∀ᶠ T : ℝ in atTop,
      ((unitSpectrum.cut T).card : ℝ) ≤ B * (T * Real.log T) := by
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
    have hT₁ := (Real.one_le_exp_iff.mpr zero_le_one).trans hT
    have hlog := (Real.le_log_iff_exp_le (zero_lt_one.trans_le hT₁)).mpr hT
    rw [cut_one hT₁, Finset.card_singleton, Nat.cast_one, one_mul]
    exact one_le_mul_of_one_le_of_one_le hT₁ hlog
  have hratio : ∀ α : ℝ, 0 < α → α < 1 → ∃ q : ℝ, α ^ 2 ≤ q ∧
      Tendsto (fun T : ℝ => mass unitSpectrum (fun _ => 1) (T ^ α) /
        mass unitSpectrum (fun _ => 1) T) atTop (nhds q) := by
    intro α hα hα₁
    refine ⟨1, ?_, ?_⟩
    · nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hα₁.le)]
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ),
        (tendsto_rpow_atTop hα).eventually_ge_atTop 1] with T hT hX
      simp [mass_one hX, mass_one hT]
  have he := hV unitSpectrum (fun _ => 1) (fun _ => zero_le_one)
    hpos hdim singleton_gap hratio (r := 1) (β := 1) (ε := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨T, hT, hwindow⟩ := he.exists
  obtain ⟨u, _, hu⟩ := hwindow 0
  exact ⟨T, u, hT, by simpa only [div_one] using hu⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hV
  obtain ⟨_, _, _, h⟩ := half_loss rejected hV
  norm_num [rejected, realize] at h

private theorem actual_dependence : ObservationalDependence signature actual := by
  rintro ⟨⟩
  refine ⟨⟨unitSpectrum, fun _ => 1, 1⟩, 0, Real.pi / 2, ?_⟩
  change sine unitSpectrum (fun _ => 1) 1 0 ≠ sine unitSpectrum (fun _ => 1) 1 (Real.pi / 2)
  simp [sine, cut_one (le_refl 1), Real.sin_pi_div_two]

def evidence : Registration arena (type_of% @eventual_sine_cutoff_tradeoff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventual_sine_cutoff_tradeoff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventual_sine_cutoff_tradeoff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff.unit
  realizationName := `Reg.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p v => sine p.1 p.2.1 p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
    definition := none
    coordinates := #[0, 1, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "body", "arg", "body", "arg", "body",
        "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
