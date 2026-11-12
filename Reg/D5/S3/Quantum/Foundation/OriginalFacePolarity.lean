import D5.S3.Quantum.Foundation.OriginalFacePolarity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Original exclusion readouts and the full source telescope. -/

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.OriginalFacePolarity

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalFacePolarity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nonzero : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.nonzero

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => exclusion P.cone P.unit x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ →
    exclusionBalls C u → pairProper C u →
    ∃ F : FacePolarity C u, ∀ p : pure C u, (F.pole p).val = O.readout () P p

abbrev sourceScope : Prop := type_of% (@original_face_polarity.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P hc hu hs hB hp
    obtain ⟨F⟩ := @h P.V P.add P.space P.finite P.nonzero P.cone P.unit hc hu hs hB hp
    exact ⟨F, F.pole_val⟩
  · intro h V add space finite nonzero C u hc hu hs hB hp
    obtain ⟨F, _⟩ := h (@Inputs.mk V add space finite nonzero C u) hc hu hs hB hp
    exact ⟨F⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@original_face_polarity.{u})

end Reg.D5.S3.Quantum.Foundation.OriginalFacePolarity
