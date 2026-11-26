import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TwoSource.MasslessResidue
import Reg.Support.SingleDependentReadout

/-! The mixed-entry magnitude is essential for two-source positivity. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.TwoSource.MasslessResidue
open LeanInformationAudit Matrix
namespace Reg.D5.S3.Quantum.TwoSource.MasslessResidue
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => |x|) (fun e => nomatch e)
def discarded : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ r : ℝ,
    ((∃ Z : Matrix (Fin 2) (Fin 2) ℝ, Z.PosSemidef ∧ (1-Z).PosSemidef ∧ Z 0 1 = r) ↔
      R.readout () () r ≤ 1/2) ∧
    (|r| = 1/2 → ∀ Z : Matrix (Fin 2) (Fin 2) ℝ,
      Z.PosSemidef → (1-Z).PosSemidef → Z 0 1 = r → Z = balanced r)

private theorem discarded_fails : ¬arena.Law discarded := by
  intro law
  have hex := (law 1).1.mpr (by change (0 : ℝ) ≤ 1/2; norm_num)
  have h := (sharp_mixed_residue 1).1.mp hex
  norm_num at h

def family : Registration arena (type_of% @sharp_mixed_residue) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_mixed_residue, discarded, discarded_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), by change |(0 : ℝ)| ≠ |(1 : ℝ)|; norm_num⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TwoSource.MasslessResidue.sharp_mixed_residue) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.TwoSource.MasslessResidue.unit
  realizationName := `Reg.D5.S3.Quantum.TwoSource.MasslessResidue.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TwoSource.MasslessResidue
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.TwoSource.MasslessResidue
