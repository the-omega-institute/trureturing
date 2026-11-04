import D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open _root_.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open _root_.D5.S0.Certificates.JacoExponentialDominationRefutation

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
abbrev sig : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig := realize sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
private theorem depends : ObservationalDependence sig actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; omega⟩

namespace Target0
abbrev arena : Arena where
  signature := sig
  Law R := ∀ n : ℕ, 1 ≤ n → jacoRight (R.readout () () n) = 2*n - ((Finset.range n).filter fun i => 1 ≤ i ∧ n ≤ jacoRight i).card
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1 (by decide)
  change jacoRight 0 = 2 * 1 -
    ((Finset.range 1).filter fun i => 1 ≤ i ∧ 1 ≤ jacoRight i).card at h1
  rw [← endpoint_recurrence 1 (by decide)] at h1
  exact (by decide +kernel : jacoRight 0 ≠ jacoRight 1) h1
def evidence : Registration arena (type_of% @endpoint_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨endpoint_recurrence, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@endpoint_recurrence) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.endpoint_recurrence.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.Target0.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
end Target0

namespace Target1
abbrev arena : Arena where
  signature := sig
  Law R := ∀ n : ℕ, 1 ≤ n → 1 ≤ beattyOut (R.readout () () n) ∧ beattyOut n ≤ n
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h1 := (h 1 (by decide)).1
  have hb0 : beattyOut 0 = 0 := by
    apply Nat.floor_eq_zero.mpr
    simpa using (div_lt_one Real.goldenRatio_pos).2 Real.one_lt_goldenRatio
  change 1 ≤ beattyOut 0 at h1
  rw [hb0] at h1
  omega
def evidence : Registration arena (type_of% @beatty_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨beatty_bounds, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@beatty_bounds) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.beatty_bounds.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.Target1.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
end Target1

namespace Target2
abbrev arena : Arena where
  signature := sig
  Law R := ∀ n i : ℕ, R.readout () () n ≤ i + beattyOut i ↔ beattyOut n ≤ i
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h1 := (h 1 0).mp (Nat.zero_le _)
  have hb := (beatty_bounds 1 (by decide)).1
  omega
def evidence : Registration arena (type_of% @beatty_threshold) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨beatty_threshold, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@beatty_threshold) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.beatty_threshold.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.Target2.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
end Target2

namespace Target3
abbrev arena : Arena where
  signature := sig
  Law R := ∀ n : ℕ, jacoRight (R.readout () () n) = n + beattyOut n
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1
  change 0 = 1 + beattyOut 1 at h1
  omega
def evidence : Registration arena (type_of% @endpoint_eq_beatty) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨endpoint_eq_beatty, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@endpoint_eq_beatty) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.endpoint_eq_beatty.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty.Target3.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
end Target3

end

end Reg.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
