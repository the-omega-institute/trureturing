import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Observer.Linear.ReflectingHeatQuantile

/-! The first endpoint value controls the lower signed discrepancy. -/

open Filter MeasureTheory Set LeanInformationAudit
open _root_.Reg.Support
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.ReflectingHeatInterpolation.EqualMassBins
open _root_.D5.S3.Observer.Linear.ReflectingHeatInterpolation
open scoped Topology

noncomputable section

namespace Reg.D5.S3.Observer.Linear.ReflectingHeatQuantile

abbrev signature := SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ β f => f β) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {β : ℝ} {density : ℝ → ℝ} (bins : EqualMassBins β density) {f : ℝ → ℝ}
    (_ : ContinuousOn f (Ici β)) (_ : AntitoneOn f (Ici β)) (_ : Tendsto f atTop (𝓝 0))
    (_ : Summable fun k => f (bins.endpoint (k + 1)))
    (_ : IntegrableOn (fun x => f x * density x) (Ioi β)),
    -R.readout () β f ≤
        (∑' k, f (bins.endpoint (k + 1))) - (∫ x in Ioi β, f x * density x) ∧
      (∑' k, f (bins.endpoint (k + 1))) - (∫ x in Ioi β, f x * density x) ≤ 0

private def unitBins : EqualMassBins 0 (fun _ => 1) where
  endpoint := fun k => k
  start := Nat.cast_zero
  increasing := by
    intro k l h
    change (k : ℝ) < (l : ℝ)
    exact_mod_cast h
  unbounded := tendsto_natCast_atTop_atTop
  continuous_density := continuousOn_const
  nonnegative := fun _ _ => zero_le_one
  mass := fun k => by simp [intervalIntegral.integral_const, Nat.cast_add]

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have ht := h unitBins (f := fun _ => 0) continuousOn_const
    (fun _ _ _ _ _ => le_rfl) hzero (by simp) (by simp)
  norm_num [rejected, realize] at ht

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @discrepancy_antitone) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨discrepancy_antitone, rejected, rejectedLaw⟩
  sensitivity := SingleDependentReadout.sensitivity _ _ _ rejectedLaw
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@discrepancy_antitone) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.EqualMassBins.discrepancy_antitone.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatQuantile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ β f => f β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatQuantile
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


private def rejectedMinimum : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def minimumArena : Arena where
  signature := signature
  Law R := ∀ {β : ℝ} {density : ℝ → ℝ} (bins : EqualMassBins β density) {f : ℝ → ℝ}
    {s : ℝ} (_ : β ≤ s) (_ : ContinuousOn f (Ici β)) (_ : AntitoneOn f (Icc β s))
    (_ : MonotoneOn f (Ici s)) (_ : Tendsto f atTop (𝓝 0))
    (_ : Summable fun k => f (bins.endpoint (k + 1)))
    (_ : IntegrableOn (fun x => f x * density x) (Ioi β)),
    (∑' k, f (bins.endpoint (k + 1))) - (∫ x in Ioi β, f x * density x) ≤ -R.readout () s f

private theorem rejectedMinimumLaw : ¬ minimumArena.Law rejectedMinimum := by
  intro h
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have ht := h unitBins (f := fun _ => 0) (s := 0) le_rfl continuousOn_const
    (fun _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) hzero (by simp) (by simp)
  norm_num [rejectedMinimum, realize] at ht

def minimumFamily : Registration minimumArena (type_of% @discrepancy_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨discrepancy_le, rejectedMinimum, rejectedMinimumLaw⟩
  sensitivity := SingleDependentReadout.sensitivity _ _ _ rejectedMinimumLaw
  dependence := dependence

def minimumRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@discrepancy_le) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.EqualMassBins.discrepancy_le.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatQuantile.minimumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨minimumArena⟩
  objectArena := .source ⟨minimumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source minimumArena ⟨minimumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s f => f s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatQuantile
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.Linear.ReflectingHeatQuantile
