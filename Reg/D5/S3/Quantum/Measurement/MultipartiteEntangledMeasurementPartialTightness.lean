import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the attained multipartite measurement score. -/

namespace Reg.D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness

open _root_.D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe equality between the attained score and the partial bound. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Preserve all parameters, admissibility conditions and existential witnesses. -/
abbrev arena : Arena where
  signature := signature
  Law R := by
    classical
    exact ∀ n d m : ℕ, (hn : 2 ≤ n) → (hd : 2 ≤ d) → m ≤ d ^ (n - 1) →
      letI : NeZero n := NeZero.of_pos (by omega : 0 < n)
      letI : NeZero d := NeZero.of_pos (by omega : 0 < d)
      ∃ (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
        (u : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
        (p : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ),
        IsDensity ρ ∧
        (∀ k x y, u k x y ∈ Matrix.unitaryGroup (ZMod d) ℂ) ∧
        IsProjectiveMeasurement p ∧
        ((Finset.univ.filter (fun b => IsFullySeparable (p b))).card = d * m) ∧
        R.readout () () (score ρ u p) (((d : ℝ) ^ n - d * m + m) / (d : ℝ) ^ n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, u, p, _, _, _, _, hfalse⟩ := h 2 2 0 (by decide) (by decide) (by decide)
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

def source : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
    definition := some {
      owner := `D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
      name := `D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
