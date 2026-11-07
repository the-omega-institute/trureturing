import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Asymptotics.GeometricScaleRigidity
import Reg.Support.DependentFamily

/-! Contract registration for the geometric shrinking-orbit theorem. -/

noncomputable section

namespace Reg.D5.S0.Asymptotics.GeometricScaleRigidity

open _root_.D5.S0.Asymptotics.GeometricScaleRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := (ℝ → ℝ) × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M => p.1 M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℝ → ℝ} {rho M : ℝ},
    ContinuousAt h 0 →
      0 ≤ rho →
      rho < 1 →
      (∀ n : ℕ, h (rho ^ n * M) = h M) →
      R.readout () (h, rho) M = h 0

abbrev sourceScope := type_of% (@_root_.D5.S0.Asymptotics.GeometricScaleRigidity.geometric_scale_rigidity)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual :=
  source_bridge.mp (@_root_.D5.S0.Asymptotics.GeometricScaleRigidity.geometric_scale_rigidity)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let one : ℝ → ℝ := fun _ => 1
  have hconst : ContinuousAt one 0 := continuousAt_const
  have hscale : ∀ n : ℕ, one ((0 : ℝ) ^ n * 0) = one 0 := by
    intro n
    rfl
  have hh := h (h := one) (rho := (0 : ℝ)) (M := (0 : ℝ)) hconst
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) hscale
  norm_num [rejected, realize, one] at hh

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(fun x : ℝ => x, 0), 0, 1, ?_⟩
    norm_num [actual, realize]

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S0.Asymptotics.GeometricScaleRigidity.geometric_scale_rigidity)
      (Realization signature) Unit Unit := {
  unitName := `D5.S0.Asymptotics.GeometricScaleRigidity.geometric_scale_rigidity.__information_unit
  realizationName := `Reg.D5.S0.Asymptotics.GeometricScaleRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => p.1 M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S0.Asymptotics.GeometricScaleRigidity
