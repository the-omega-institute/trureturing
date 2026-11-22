import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.BKMSharpWeightedInterval

/-! Source-bound observations of the spacing deficit and the varying-cutoff coefficient. -/

namespace Reg.D5.S3.Quantum.Recovery.BKMSharpWeightedInterval

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.BKMSharpWeightedInterval
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

noncomputable section

namespace Spacing

abbrev meshSignature : Signature := signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization meshSignature :=
  realize meshSignature (fun _ p z => meshCoefficient p.1 p.2 z) (fun e => nomatch e)

def rejected : Realization meshSignature :=
  realize meshSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := meshSignature
  Law R := ∀ x y z : ℝ,
    let m := (x + y + z) / 3
    (8 / 27 : ℝ) * (x + y + z) ^ 3 - R.readout () ⟨x, y⟩ z =
      ((x - m) ^ 2 * (x + 2 * m) + (y - m) ^ 2 * (y + 2 * m) +
        (z - m) ^ 2 * (z + 2 * m)) / 3

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := h 1 1 1
  norm_num [rejected, realize] at h'

def family : Registration arena (type_of% three_interval_mesh_deficit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨three_interval_mesh_deficit, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    change meshCoefficient 1 1 0 ≠ meshCoefficient 1 1 1
    norm_num [meshCoefficient_eq_cubes]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    three_interval_mesh_deficit (Realization meshSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMSharpWeightedInterval.three_interval_mesh_deficit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMSharpWeightedInterval.Spacing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize meshSignature (fun _ p z => meshCoefficient p.1 p.2 z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMSharpWeightedInterval
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Spacing

namespace Cutoff

abbrev cutoffSignature : Signature := signature (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization cutoffSignature :=
  realize cutoffSignature (fun _ p c => bandCoefficient p.1 p.2.1 c (1 - p.2.2))
    (fun e => nomatch e)

def rejected : Realization cutoffSignature :=
  realize cutoffSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := cutoffSignature
  Law R := ∀ {s t v η : ℝ}, 0 < s → s ≤ t → s + t ≤ 1 → 0 ≤ v → 0 ≤ η →
    t < s + t - v - η →
    R.readout () ⟨s, t, v⟩ (s + t - v - η) ≤ meshCoefficient s t (1 - (s + t)) + η

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := h (s := 1 / 3) (t := 1 / 3) (v := 0) (η := 0)
    (by norm_num) le_rfl (by norm_num) le_rfl le_rfl (by norm_num)
  change (1 : ℝ) ≤ meshCoefficient (1 / 3) (1 / 3) (1 - (1 / 3 + 1 / 3)) + 0 at h'
  norm_num [meshCoefficient_eq_cubes] at h'

def family : Registration arena (type_of% @band_coefficient_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@band_coefficient_bound, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨1 / 3, 1 / 3, 0⟩, 1 / 2, 2 / 3, ?_⟩
    change bandCoefficient (1 / 3) (1 / 3) (1 / 2) (1 - 0) ≠
      bandCoefficient (1 / 3) (1 / 3) (2 / 3) (1 - 0)
    norm_num [bandCoefficient, headCoefficient, tailCoefficient, intervalCoefficient, min_def,
      max_def]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@band_coefficient_bound) (Realization cutoffSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMSharpWeightedInterval.band_coefficient_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMSharpWeightedInterval.Cutoff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cutoffSignature
    (fun _ p c => bandCoefficient p.1 p.2.1 c (1 - p.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMSharpWeightedInterval
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cutoff

end
end Reg.D5.S3.Quantum.Recovery.BKMSharpWeightedInterval
