import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization

/-! Observe the squared contrast controlling rational group-kernel realizability. -/

namespace Reg.D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization
  (exists_rational_group_kernel_with_readings)
open Omega.Geometry.QuaternionContrast (IsSeparatedBiInvariantKernel)
open LeanInformationAudit

set_option autoImplicit false

universe u

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ c => c ^ 2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t d : ℚ) (_ : 0 ≤ t) (_ : R.readout () () d ≤ 1 - t),
    ∃ (G : Type) (_ : Group G) (K : G → G → ℚ),
      IsSeparatedBiInvariantKernel.{0,u} K ∧ (∃ p : G, K 1 p = 0) ∧
      (∃ u v : G, u * v ≠ v * u) ∧ (∃ y z : G, K 1 y = t ∧ K 1 z - K y z = d)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨G, group, K, hK, _, _, y, z, hy, hz⟩ := h 1 1 (by decide)
    (by change (0 : ℚ) ≤ 1 - 1; norm_num)
  letI := group
  have heq : (1 : G) = y := (hK.separated 1 y).mp hy
  subst y
  rw [sub_self] at hz
  exact zero_ne_one hz

def family : Registration arena.{u} (type_of% @exists_rational_group_kernel_with_readings.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_rational_group_kernel_with_readings.{u}, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, by change (0 : ℚ) ^ 2 ≠ 1 ^ 2; norm_num⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_rational_group_kernel_with_readings.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization
