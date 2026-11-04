import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.MalkounJordanElementary
import Reg.Support.DependentFamily

/-! Source-bound audit of the real comparison in the complete elementary symmetric claim. -/

namespace Reg.D5.S3.Quantum.Matrix.MalkounJordanElementary

open _root_.D5.S3.Quantum.Matrix.MalkounJordanElementary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem jordan {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) : (X * Y + Y * X).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hX.eq, hY.eq, add_comm]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ (X Y : Matrix (Fin n) (Fin n) ℂ),
    ∀ (hX : X.PosSemidef) (hY : Y.PosSemidef), ∀ (k : ℕ), 1 ≤ k → k ≤ n →
    R.readout () ()
      (elementarySymmetric (jordan hX.isHermitian hY.isHermitian).eigenvalues k)
      (elementarySymmetric ((hX.isHermitian.pow 2).add (hY.isHermitian.pow 2)).eigenvalues k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by norm_num) 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero 1
    (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have bad := congrFun h 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at bad
  have : (1 : ℝ) ≤ 0 := Eq.mp bad (le_refl 0)
  norm_num at this

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.MalkounJordanElementary.result)
    (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.MalkounJordanElementary.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.MalkounJordanElementary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.MalkounJordanElementary
    definition := some {
      owner := `D5.S3.Quantum.Matrix.MalkounJordanElementary
      name := `D5.S3.Quantum.Matrix.MalkounJordanElementary.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.MalkounJordanElementary
