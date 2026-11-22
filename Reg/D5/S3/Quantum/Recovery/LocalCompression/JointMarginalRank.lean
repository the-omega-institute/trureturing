import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank

/-! Source-bound observation of the division in the marginal-rank minimum. -/

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank (minimum)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ e k => k / e) (fun a => nomatch a)

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {m e : ℕ} (_he : 0 < e)
    (X : Matrix (Fin m × Fin e) (Fin m × Fin e) ℂ) (_hX : X.PosSemidef),
    IsLeast (Set.range (fun U : unitaryGroup (Fin m × Fin e) ℂ =>
      (partialTraceRight ((U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ)).rank))
      (R.readout () e (X.rank + e - 1))

abbrev sourceScope := type_of% (@minimum)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  let X : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ := 1
  have hX : X.PosSemidef := Matrix.PosSemidef.one
  have hmin := minimum (by decide : 0 < 2) X hX
  have hceil : (X.rank + 2 - 1) / 2 = 1 := by
    simp [X, Matrix.rank_one]
  rw [hceil] at hmin
  exact (by decide : (0 : ℕ) ≠ 1) ((h (by decide : 0 < 2) X hX).unique hmin)

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨minimum, rejected, rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := by
    intro i
    cases i
    refine ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), ?_⟩
    change (1 : ℕ) / 2 ≠ 3 / 2
    decide

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@minimum) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank.minimum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ e k => k / e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank
