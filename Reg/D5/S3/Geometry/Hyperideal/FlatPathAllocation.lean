import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.FlatPathAllocation
import Reg.D5.S3.Geometry.Hyperideal.FlatComponentBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget
open _root_.D5.S3.Geometry.Hyperideal.FlatPathAllocation
open _root_.D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
namespace Reg.D5.S3.Geometry.Hyperideal.FlatPathAllocation
universe u

abbrev signature := Reg.D5.S3.Geometry.Hyperideal.FlatComponentBudget.Components.signature.{u}
def actual : Realization signature :=
  Reg.D5.S3.Geometry.Hyperideal.FlatComponentBudget.Components.actual

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {T : Type u} [finite : Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (_hell : ∀ e, 0 < ell e) (_hsum : AngleSums p ell)
    (_hdegree : ∀ e, 6 ≤ degree p e) (_hF : (flats p ell).Nonempty),
    piVertexCount p ell = flatCount p ell + pathCount p ell ∧
    faceComponentCount p ell ≤ pathCount p ell ∧
    1 ≤ faceComponentCount p ell ∧
    flatCount p ell ≤ piVertexCount p ell-faceComponentCount p ell ∧
    piVertexCount p ell-faceComponentCount p ell ≤ Nat.card p.GlobalEdge-faceComponentCount p ell ∧
    ∀ t : T, Flat p ell t → ∃ e₀ e₁ : p.GlobalEdge, e₀ ≠ e₁ ∧
      Endpoint p ell (R.readout () ⟨T,finite,p,ell⟩ t) e₀ ∧
      Endpoint p ell (component p ell t) e₁

theorem actual_law : arena.Law actual := by
  intro T finite p ell hell hsum hdegree hF
  exact complete_flat_counting p ell hell hsum hdegree hF

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatPathAllocation.complete_flat_counting.{u})) ↔
      arena.{u}.Law actual.{u} := Iff.rfl

end Reg.D5.S3.Geometry.Hyperideal.FlatPathAllocation
