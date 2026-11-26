import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum
import Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel
import Reg.Support.DependentFamily

/-! Source-bound audit of the extremum and integral of the reading over a phase-circle fibre of
the unit quaternions. -/

namespace Reg.D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum

open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionRayKernel
open _root_.D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-! `rayKernel_isGreatest_and_integral`, observed in its integral conjunct through the ray kernel
against a fixed first argument (signature and realizations of the ray-kernel mirror). -/
namespace Fibre

open Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel (signature actual shifted dependence)

/-- Retain the complete argument telescope and all three conjuncts of
`rayKernel_isGreatest_and_integral`; only the value on the right of the integral identity is read
out. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y : unitary ℍ[ℝ],
    IsGreatest {r | ∃ c ∈ phaseCircle,
        r = quaternionModel.kappa y (quaternionModel.tri (x * c) y (x * c))} (rayKernel x y) ∧
      IsGreatest {r | ∃ c ∈ phaseCircle,
        r = (2 * quaternionModel.kappa (x * c) y - 1) ^ 2} (rayKernel x y) ∧
      ∫ χ in (0 : ℝ)..(2 * Real.pi),
          ⟪(x : ℍ[ℝ]) * ⟨Real.cos χ, Real.sin χ, 0, 0⟩, (y : ℍ[ℝ])⟫_ℝ ^ 2 =
        Real.pi * r.readout () x y

/-- Shifting the ray kernel by one would add `π` to the integral. -/
theorem rejected_law : ¬ arena.Law shifted := by
  intro h
  have hh : ∫ χ in (0 : ℝ)..(2 * Real.pi),
      ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]) * ⟨Real.cos χ, Real.sin χ, 0, 0⟩,
        ((1 : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ ^ 2 = Real.pi * (rayKernel 1 1 + 1) := (h 1 1).2.2
  have ha := (rayKernel_isGreatest_and_integral 1 1).2.2
  have hpi := Real.pi_pos
  linarith

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @rayKernel_isGreatest_and_integral

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_isGreatest_and_integral, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨shifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Fibre

def rayKernel_isGreatest_and_integral_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_isGreatest_and_integral)
      (Realization Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum.rayKernel_isGreatest_and_integral_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum.Fibre.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Fibre.arena⟩
  objectArena := .source ⟨Fibre.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Fibre.arena ⟨Fibre.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.signature
    (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum
