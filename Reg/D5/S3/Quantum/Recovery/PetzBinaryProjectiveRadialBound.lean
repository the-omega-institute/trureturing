import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the coefficient-two inequality on the radial qubit segment. -/

set_option autoImplicit false

noncomputable section

open Set
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.QubitNormalFormState (qubitState)
open _root_.D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive (errorSq loss)
open _root_.D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound (radial_bounds)

namespace Reg.D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (ha : a ∈ Icc (0 : ℝ) 1),
    let ρ := qubitState (a * u) (a * z) (by
      have hR₀ := hz₀.trans hzR
      have hscaled : (a * u) ^ 2 + (a * z) ^ 2 = (a * R) ^ 2 := by simp only [mul_pow, hR]; ring
      have ham : a * R ≤ R := by simpa using mul_le_mul_of_nonneg_right ha.2 hR₀
      rw [hscaled]
      simpa using pow_le_pow_left₀ (mul_nonneg ha.1 hR₀) (ham.trans hR₁.le) 2)
    let σ := qubitState u z (by
      rw [← hR]
      simpa using pow_le_pow_left₀ (hz₀.trans hzR) hR₁.le 2)
    F.readout () () (errorSq ρ σ) (2 * loss ρ σ) ∧
    (1 - a) ^ 2 * Real.log ((1 - z ^ 2) / (1 - R ^ 2)) / 2 ≤ loss ρ σ ∧
    Real.log ((1 - z ^ 2) / (1 - R ^ 2)) * errorSq ρ σ ≤
      2 * ((R ^ 2 - z ^ 2) / (1 - z ^ 2)) * loss ρ σ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (u := 0) (z := 0) (R := 0) (a := 0) (by norm_num)
    le_rfl le_rfl zero_lt_one ⟨le_rfl, zero_le_one⟩).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @radial_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@radial_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@radial_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound.radial_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound
