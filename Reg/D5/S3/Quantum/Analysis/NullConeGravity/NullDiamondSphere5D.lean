import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.NullConeGravity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout
open MeasureTheory
open scoped InnerProductSpace

namespace Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D

abbrev sig := signature Unit (fun _ => Sphere5D × Sphere5D) (fun _ => ℝ)

abbrev arena : Arena where
  signature := sig
  Law r :=
    (∫ p, r.readout () () p ∂(sphere5DMeasure.prod sphere5DMeasure)) = 8 * Real.pi ^ 4

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  change ¬ (∫ _ : Sphere5D × Sphere5D, (0 : ℝ) ∂(sphere5DMeasure.prod sphere5DMeasure)) =
    8 * Real.pi ^ 4
  rw [integral_zero]
  exact (show 0 < 8 * Real.pi ^ 4 by positivity).ne

abbrev sourceStatement : Prop := type_of% @sphere5D_inv_sqrt_sq_integral

def source_registration : Registration arena sourceStatement where
  actual := realize sig (fun _ _ p => (1 - sphere5DDot p.1 p.2)⁻¹) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@sphere5D_inv_sqrt_sq_integral, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    let i : Fin (Module.finrank ℝ E4) := ⟨0, by simp⟩
    have hn : ‖(stdOrthonormalBasis ℝ E4) i‖ = 1 :=
      (stdOrthonormalBasis ℝ E4).orthonormal.norm_eq_one i
    let n : Sphere5D := ⟨(stdOrthonormalBasis ℝ E4) i, by simp [hn]⟩
    let m : Sphere5D := ⟨-(n : E4), by simp [hn]⟩
    refine ⟨(), (n, n), (n, m), ?_⟩
    have hnn : sphere5DDot n n = 1 := by
      change ⟪((stdOrthonormalBasis ℝ E4) i), ((stdOrthonormalBasis ℝ E4) i)⟫_ℝ = 1
      rw [real_inner_self_eq_norm_sq, hn]
      norm_num
    have hnm : sphere5DDot n m = -1 := by
      change ⟪(n : E4), -(n : E4)⟫_ℝ = -1
      rw [inner_neg_right]
      exact congrArg Neg.neg hnn
    change (1 - sphere5DDot n n)⁻¹ ≠ (1 - sphere5DDot n m)⁻¹
    rw [hnn, hnm]
    norm_num

def sphere5D_inv_sqrt_sq_integral_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sphere5D_inv_sqrt_sq_integral) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D.integral_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ p => (1 - sphere5DDot p.1 p.2)⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D
    definition := none
    coordinates := #[]
    readouts := #[{
        path := #["fn", "arg", "arg", "body"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D
