import D5.S3.Quantum.Foundation.NiceConeFaces
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original-domain reconstruction for support-zero observations.
This bridge alone is not a four-slot registration. -/

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.NiceConeFaces

open _root_.D5.S3.Quantum.Foundation.NiceConeFaces
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := (P.V →ₗ[ℝ] ℝ) × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ ax => ax.1 ax.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u}, IsClosed (P.cone : Set P.V) → Nice P.cone →
    ∀ F : P.cone.Face, ∃ a : P.V →ₗ[ℝ] ℝ,
      (∀ x ∈ P.cone, 0 ≤ a x) ∧
      ∀ x, x ∈ F ↔ x ∈ P.cone ∧ O.readout () P (a, x) = 0

abbrev sourceScope : Prop := type_of% (@every_face_exposed.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P hc hn F
    obtain ⟨a, ha, he⟩ := @h P.V P.add P.space P.finite P.cone hc hn F
    exact ⟨a, ha, fun x => Set.ext_iff.mp he x⟩
  · intro h V add space finite C hc hn F
    obtain ⟨a, ha, he⟩ := h (@Inputs.mk V add space finite C) hc hn F
    exact ⟨a, ha, Set.ext he⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@every_face_exposed.{u})

end Reg.D5.S3.Quantum.Foundation.NiceConeFaces
