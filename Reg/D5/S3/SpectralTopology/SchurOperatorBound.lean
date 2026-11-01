import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.SpectralTopology.SchurOperatorBound

namespace Reg.D5.S3.SpectralTopology.SchurOperatorBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev scalarSignature : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
universe u v w

def l2_opNorm_le_schur_readout : ∀ (_ : Unit) (_ : Unit), ℝ → ℝ := fun _ _ => Real.sqrt
abbrev l2_opNorm_le_schur_actual : Realization scalarSignature :=
  realize scalarSignature l2_opNorm_le_schur_readout (fun e => nomatch e)
abbrev l2_opNorm_le_schur_arena : Arena where
  signature := scalarSignature
  Law R := ∀ {𝕜 : Type u} [RCLike 𝕜] {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ 𝕜) {r c : ℝ},
    0 ≤ r → 0 ≤ c → (∀ i, ∑ j, ‖A i j‖ ≤ r) →
      (∀ j, ∑ i, ‖A i j‖ ≤ c) → ‖A‖ ≤ R.readout () () (r*c)
private def bad : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem bad_reject : ¬ l2_opNorm_le_schur_arena.{u,v,w}.Law bad := by
  intro h
  have hh := @h (ULift.{u} ℝ) inferInstance (ULift.{v} Unit) (ULift.{w} Unit)
    inferInstance inferInstance inferInstance 0 0 0 (by norm_num) (by norm_num)
      (by intro i; simp) (by intro j; simp)
  simpa [bad, realize] using hh

def l2_opNorm_le_schur_family : Registration l2_opNorm_le_schur_arena
    (type_of% (@_root_.D5.S3.SpectralTopology.SchurOperatorBound.l2_opNorm_le_schur)) where
  actual := l2_opNorm_le_schur_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.SpectralTopology.SchurOperatorBound.l2_opNorm_le_schur, bad, bad_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [l2_opNorm_le_schur_actual, l2_opNorm_le_schur_readout, realize]
def registration_l2_opNorm_le_schur : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.SpectralTopology.SchurOperatorBound.l2_opNorm_le_schur) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.SpectralTopology.SchurOperatorBound.l2_opNorm_le_schur_unit
  realizationName := `Reg.D5.S3.SpectralTopology.SchurOperatorBound.l2_opNorm_le_schur_family
  realizationSource := none
  generated := false
  arena := .source ⟨l2_opNorm_le_schur_arena⟩
  objectArena := .source ⟨l2_opNorm_le_schur_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source l2_opNorm_le_schur_arena ⟨l2_opNorm_le_schur_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature l2_opNorm_le_schur_readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.SpectralTopology.SchurOperatorBound
