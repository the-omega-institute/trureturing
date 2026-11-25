import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap
import Reg.Support.SingleDependentReadout

/-! The word and horizon observations for the original three-matrix game. -/

open LeanInformationAudit Filter Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeyerovitchYoungQ61Complete (ConnectsAt Legal completeGraph matrixMinimum)
open _root_.MeyerovitchYoungQ61FrequencyGap
open scoped Topology

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap

noncomputable section

private abbrev Parameters := Σ _ : ℝ, ℝ

abbrev wordSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => List Letter) (fun _ => ℝ)

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ p a => centeredScore p.1 p.2 a) (fun e => nomatch e)

private def wordPerturbed : Realization wordSignature :=
  realize wordSignature (fun _ p a => centeredScore p.1 p.2 a + 1) (fun e => nomatch e)

private theorem word_dependence : ObservationalDependence wordSignature wordActual := by
  intro _
  refine ⟨⟨1, 0⟩, [], [.plus], ?_⟩
  change centeredScore 1 0 [] ≠ centeredScore 1 0 [.plus]
  have hlo : 0 ≤ shift .plus := by
    change 0 ≤ Real.sqrt 2 - 1 / 2
    linarith [Real.one_lt_sqrt_two]
  have hhi : shift .plus ≤ 1 := by
    change Real.sqrt 2 - 1 / 2 ≤ 1
    have hs : Real.sqrt 2 < (3 : ℝ) / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  have h := (MeyerovitchYoungQ61Subcritical.overshoot_eq_zero_iff 1 (shift .plus)).2 ⟨hlo, hhi⟩
  norm_num [centeredScore, centeredStep, reward, h]

def recurrenceArena : Arena where
  signature := wordSignature
  Law r := ∀ (c ρ : ℝ) (a : List Letter),
    (a.foldl (centeredStep c ρ) (0, 0)).1 = normalizedState c ρ a ∧
    normalizedState c ρ a ∈ Icc 0 1 ∧
    matrixMinimum (matrices c ρ) a = r.readout () ⟨c, ρ⟩ a - normalizedState c ρ a / 2

private theorem recurrence_rejects : ¬ recurrenceArena.Law wordPerturbed := by
  intro h
  have hp := (h 0 0 []).2.2
  have ha := (matrixMinimum_eq_centered 0 0 []).2.2
  change matrixMinimum (matrices 0 0) [] =
    centeredScore 0 0 [] + 1 - normalizedState 0 0 [] / 2 at hp
  linarith

def recurrenceFamily : Registration recurrenceArena (type_of% (@matrixMinimum_eq_centered)) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨@matrixMinimum_eq_centered, wordPerturbed, recurrence_rejects⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ recurrence_rejects
  dependence := word_dependence

def blockArena : Arena where
  signature := wordSignature
  Law r := ∀ (c : ℝ) {ρ : ℝ} (_ : 0 ≤ ρ) (_ : ρ ≤ epsilon) (a : List Letter),
    r.readout () ⟨c, ρ⟩ a ≤ (a.length : ℝ) * (c + ρ / 8) - ρ * (↑(a.length / 4) : ℝ) ∧
    matrixMinimum (matrices c ρ) a + normalizedState c ρ a / 2 ≤
      (a.length : ℝ) * (c + ρ / 8) - ρ * (↑(a.length / 4) : ℝ) ∧
    (∀ d ∈ Icc (0 : ℝ) 1, ∀ u : List Letter, u.length = 4 →
      (u.foldl (centeredStep c ρ) (d, 0)).2 ≤ 4 * (c + ρ / 8) - ρ) ∧
    (([.star, .minus, .plus, .minus] : List Letter).foldl
      (centeredStep c ρ) (1 / 2, 0)).2 = 4 * (c + ρ / 8) - ρ

private theorem epsilon_pos : 0 < epsilon :=
  sub_pos.mpr (Real.lt_sqrt_of_sq_lt (by norm_num))

private theorem block_rejects : ¬ blockArena.Law wordPerturbed := by
  intro h
  have hp := (h 0 (ρ := 0) le_rfl epsilon_pos.le []).1
  norm_num [wordPerturbed, realize, centeredScore] at hp

def blockFamily : Registration blockArena (type_of% (@matrixMinimum_le_four_block)) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨@matrixMinimum_le_four_block, wordPerturbed, block_rejects⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ block_rejects
  dependence := word_dependence

abbrev horizonSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => ℕ) (fun _ => ℝ)

def horizonActual : Realization horizonSignature :=
  realize horizonSignature (fun _ p n => maximin p.1 p.2 n) (fun e => nomatch e)

private def horizonPerturbed : Realization horizonSignature :=
  realize horizonSignature (fun _ _ n => (n : ℝ) ^ 2) (fun e => nomatch e)

def thresholdArena : Arena where
  signature := horizonSignature
  Law r := ∀ (c : ℝ) {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ epsilon),
    ConnectsAt aliceGraph 1 ∧ ConnectsAt (completeGraph Bool) 1 ∧
    (∀ a, Legal aliceGraph a) ∧
    (c ∈ quadraticField → ρ ∈ quadraticField → ∀ e i j, matrices c ρ e i j ∈ quadraticField) ∧
    IsGreatest (frequencyValues c ρ) (c + ρ / 8) ∧ c < c + ρ / 8 ∧
    (∀ n, IsGreatest (horizonValues c ρ n) (maximin c ρ n) ∧
      maximin c ρ n ≤ (n : ℝ) * (c + ρ / 8) - ρ * (↑(n / 4) : ℝ)) ∧
    (range (normalizedState c ρ)).Infinite ∧
    ∃ V : ℝ, Tendsto (fun n : ℕ => r.readout () ⟨c, ρ⟩ n / (n : ℝ)) atTop (𝓝 V) ∧
      V ≤ c - ρ / 8 ∧ V < c

private theorem threshold_rejects : ¬ thresholdArena.Law horizonPerturbed := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, V, hlim, _, _⟩ := h 0 epsilon_pos le_rfl
  change Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 V) at hlim
  have hdiverges : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (n : ℝ)) atTop atTop := by
    apply (tendsto_natCast_atTop_atTop (R := ℝ)).congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [pow_two, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]
  exact not_tendsto_nhds_of_tendsto_atTop hdiverges _ hlim

private theorem horizon_dependence : ObservationalDependence horizonSignature horizonActual := by
  intro _
  refine ⟨⟨0, epsilon⟩, 0, 4, ?_⟩
  change maximin 0 epsilon 0 ≠ maximin 0 epsilon 4
  obtain ⟨_, _, _, _, _, _, hfinite, _, _⟩ := frequency_threshold_gap 0 epsilon_pos le_rfl
  obtain ⟨a, ha, hscore⟩ := (hfinite 0).1.1
  change a.length = 0 at ha
  have ha' : a = [] := List.length_eq_zero_iff.mp ha
  subst a
  have hz : maximin 0 epsilon 0 = 0 := by
    rw [← hscore, (matrixMinimum_eq_centered 0 epsilon []).2.2]
    change (0 : ℝ) - (0 - 0) / 2 = 0
    norm_num
  have h₄ := (hfinite 4).2
  norm_num at h₄
  rw [hz]
  linarith

def thresholdFamily : Registration thresholdArena (type_of% (@frequency_threshold_gap)) where
  actual := horizonActual
  bridge := Iff.rfl
  variation := ⟨@frequency_threshold_gap, horizonPerturbed, threshold_rejects⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ threshold_rejects
  dependence := horizon_dependence


def recurrenceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matrixMinimum_eq_centered) (Realization wordSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap.recurrenceUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap.recurrenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨recurrenceArena⟩
  objectArena := .source ⟨recurrenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recurrenceArena ⟨recurrenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature wordActual.readout wordActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def blockRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matrixMinimum_le_four_block) (Realization wordSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap.blockUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap.blockFamily
  realizationSource := none
  generated := false
  arena := .source ⟨blockArena⟩
  objectArena := .source ⟨blockArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source blockArena ⟨blockFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature wordActual.readout wordActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def thresholdRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@frequency_threshold_gap) (Realization horizonSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap.thresholdUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap.thresholdFamily
  realizationSource := none
  generated := false
  arena := .source ⟨thresholdArena⟩
  objectArena := .source ⟨thresholdArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source thresholdArena ⟨thresholdFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize horizonSignature horizonActual.readout horizonActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "body", "fn", "arg", "fn", "fn",
        "arg", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61FrequencyGap
