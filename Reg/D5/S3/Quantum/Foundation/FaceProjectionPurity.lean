import D5.S3.Quantum.Foundation.FaceProjectionPurity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.FaceProjectionPurity

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FaceProjectionPurity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Inputs where
  A : Type u
  [add : NormedAddCommGroup A]
  [space : NormedSpace ℝ A]
  [finite : FiniteDimensional ℝ A]
  cone : PointedCone ℝ A
  unit : A →ₗ[ℝ] ℝ
  pairing : A →ₗ[ℝ] A →ₗ[ℝ] ℝ
  face : PointedCone.Face cone
  projection : A →ₗ[ℝ] A

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => (P.unit (P.projection x))⁻¹ • P.projection x)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    let B := P.pairing
    let F := P.face
    let Q := P.projection
    IsClosed (C : Set P.A) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    (∃ x ∈ C, x ≠ (0 : P.A)) →
    (∀ x y, B x y = B y x) →
    (∀ x : P.A, x ≠ 0 → 0 < B x x) →
    (∀ x, x ∈ C ↔ ∀ y ∈ C, 0 ≤ B x y) →
    (∀ p : pure C u, confirms C u p (B p)) →
    (∀ (p : pure C u) f, confirms C u p f → ∀ x ∈ C, B p x ≤ f x) →
    (∀ x, Q (Q x) = Q x) →
    (∀ x y, B (Q x) y = B x (Q y)) →
    (∀ x ∈ C, Q x ∈ F) →
    (∀ x ∈ F, Q x = x) →
    pure C u = {x | x ∈ base C u ∧ B x x = 1} ∧
      IsCompact (pure C u) ∧ (pure C u).Nonempty ∧
      ∀ p : pure C u, Q p = 0 ∨
        (0 < u (Q p) ∧ O.readout () P p ∈ pure C u ∧
          Q p = u (Q p) • O.readout () P p)

abbrev sourceScope : Prop := type_of% (@least_confirmation_face_purity.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P hclosed hu hne hsym hpos hdual hc hleast hid hadj hface hfix
    exact @h P.A P.add P.space P.finite P.cone P.unit hclosed hu hne P.pairing
      hsym hpos hdual hc hleast P.face P.projection hid hadj hface hfix
  · intro h A add space finite C u hclosed hu hne B hsym hpos hdual hc hleast F Q
    exact h (@Inputs.mk A add space finite C u B F Q) hclosed hu hne hsym hpos hdual hc hleast

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@least_confirmation_face_purity.{u})

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Quantum.Foundation.FaceProjectionPurity
