import D5.S3.Quantum.Foundation.HermitianExclusionKernel
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Original exclusion membership on the entire complex Hermitian carrier.
Variation, sensitivity, observational dependence and source selection are unsupplied. -/

noncomputable section
universe u
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace

namespace Reg.D5.S3.Quantum.Foundation.HermitianExclusionKernel

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.SectionROGFrame
open _root_.D5.S3.Quantum.Foundation.HermitianExclusionKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Σ A : Type u, Set A
  State P := P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P X => X ∈ P.2) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law O := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) (X : HermitianMat ι ℂ),
    O.readout () ⟨HermitianMat ι ℂ, exclusion cone unit (rankOne v)⟩ X ↔
      0 ≤ X ∧ X.trace = 1 ∧ X.mat *ᵥ (v : ι → ℂ) = 0

abbrev sourceScope : Prop := type_of% (@exclusion_iff_kernel.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_positive : arena.{u}.Law actual :=
  source_bridge.mp (@exclusion_iff_kernel.{u})

end Reg.D5.S3.Quantum.Foundation.HermitianExclusionKernel
