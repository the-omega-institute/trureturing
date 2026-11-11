import D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/- SOURCE ONLY. RegUNVALIDATED / UNCOMPILED_UNACCEPTED.
These are full-telescope typed ATTEMPTS, not registrations or validation.
Actual arithmetic realization, actual_law and definitional source_bridge are
provided. Compiled occurrence/sourceSelection binding, lawful enrollment,
rejected lawful families, whole-family intervention and realizability,
anchor/other-readout-fixed sensitivity, actual observational dependence and
axiom closure are UNKNOWN. No .unknown object closes a source proof gap. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh.CurvatureConsumed
open Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace positive_curvature_floor_mesh
/- RegUNVALIDATED. Readout: actual mesh residual. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := ℝ × ℝ × ℝ
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t ab => t.2.2 - (ab.1 : ℝ) * t.1 - (ab.2 : ℝ) * (2 * t.1 + t.2.1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α δ Δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hδα : δ < α)
    (hΔ : 4 * α ^ 2 / δ + 2 * α ≤ Δ),
    let N : ℤ := ⌊Δ / α⌋
    let r := Δ - ((N : ℝ) - 1) * α
    ∃ A B : ℕ,
      (B : ℤ) = ⌊r / δ⌋ - 1 ∧
      (A : ℤ) = N - 1 - 2 * B ∧
      (A : ℤ) + 2 * B = N - 1 ∧
      (A + B : ℝ) ≤ Δ / α ∧
      δ ≤ ((V.readout ()) (α, δ, Δ) (A, B)) ∧
      ((V.readout ()) (α, δ, Δ) (A, B)) < 2 * δ

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh.positive_curvature_floor_mesh

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh.positive_curvature_floor_mesh)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end positive_curvature_floor_mesh

end Reg.D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh.CurvatureConsumed
