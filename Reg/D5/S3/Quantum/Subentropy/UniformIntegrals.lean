import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.UniformIntegrals
import Reg.Support.SingleDependentReadout

noncomputable section
open MeasureTheory Set
open _root_.D5.S3.Quantum.Subentropy.UniformIntegrals
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Subentropy.UniformIntegrals

namespace Two
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := (∫ t in Ioi (0 : ℝ), 1 / (t + 1 / 2) - 1 / (t + 1) - 1 / (4 * (t + 1 / 2) ^ 2)) = R.readout () () 2 - 1 / 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hv := integral_uniformTwo_kernel
  change _ = Real.log 2 + 1 - 1 / 2 at h
  linarith
def family : Registration arena (type_of% integral_uniformTwo_kernel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_uniformTwo_kernel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, Real.exp 1, ?_⟩
    simp [actual, realize]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    integral_uniformTwo_kernel (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.UniformIntegrals.integral_uniformTwo_kernel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.UniformIntegrals.Two.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.UniformIntegrals
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Two

namespace Four
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := (∫ t in Ioi (0 : ℝ), 1 / (t + 1 / 4) - 1 / (t + 1) - 3 / (8 * (t + 1 / 4) ^ 2) + 1 / (16 * (t + 1 / 4) ^ 3) - 1 / (256 * (t + 1 / 4) ^ 4)) = R.readout () () 4 - 13 / 12
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hv := integral_uniformFour_kernel
  change _ = Real.log 4 + 1 - 13 / 12 at h
  linarith
def family : Registration arena (type_of% integral_uniformFour_kernel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_uniformFour_kernel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, Real.exp 1, ?_⟩
    simp [actual, realize]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    integral_uniformFour_kernel (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.UniformIntegrals.integral_uniformFour_kernel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.UniformIntegrals.Four.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.UniformIntegrals
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Four


namespace ReciprocalDifference
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => (Real.log x) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℝ), 0 < a → a ≤ b →
    IntegrableOn (fun t : ℝ => 1 / (t + a) - 1 / (t + b)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), 1 / (t + a) - 1 / (t + b)) = Real.log b - R.readout () () a
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 1 (by norm_num) (by norm_num)).2
  have hv := (reciprocal_difference 1 1 (by norm_num) (by norm_num)).2
  change _ = Real.log 1 - (Real.log 1 + 1) at hbad
  linarith
def family : Registration arena (type_of% reciprocal_difference) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reciprocal_difference, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, Real.exp 1, ?_⟩
    norm_num [actual, realize]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    reciprocal_difference (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.UniformIntegrals.reciprocal_difference.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.UniformIntegrals.ReciprocalDifference.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.UniformIntegrals
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ReciprocalDifference

namespace InversePower
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => 1 / x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => (1 / x) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ), 0 < a → ∀ (n : ℕ),
    IntegrableOn (fun t : ℝ => 1 / (t + a) ^ (n + 2)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), 1 / (t + a) ^ (n + 2)) =
        R.readout () () (((n : ℝ) + 1) * a ^ (n + 1))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 (by norm_num) 0).2
  have hv := (inverse_power 1 (by norm_num) 0).2
  norm_num [rejected, realize] at hbad hv
  linarith
def family : Registration arena (type_of% inverse_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inverse_power, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    inverse_power (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.UniformIntegrals.inverse_power.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.UniformIntegrals.InversePower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 1 / x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.UniformIntegrals
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end InversePower
end Reg.D5.S3.Quantum.Subentropy.UniformIntegrals
