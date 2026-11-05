import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries

/- Source-owner audit attempt. This module constructs the dependent observation
and exact original-telescope bridge. It does not assert a completed four-slot
Contract.Registration: variation, sensitivity, dependence, lawful source
selection, and the other target declarations still require evidence. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries
open _root_.D5.S3.VertexAlgebra.SupportedChannelSeries
open _root_.D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
universe u
noncomputable section

structure Parameter where
  R : Type u
  ringR : CommRing R
  algebraR : @Algebra ℂ R _ ringR.toSemiring
  N : ℕ
  B : ℕ
  a : ℤ
  b : ℤ

def signature : Signature where
  Params := Parameter.{u}
  State p := ℤ → ℤ → p.R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.R
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p F => F p.a p.b) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ {R : Type u} [instR : CommRing R] [instA : Algebra ℂ R]
    (F : ℤ → ℤ → R) (N B : ℕ)
    (_lower : ∀ a b : ℤ, b < -(B : ℤ) → F a b = 0)
    (a b : ℤ) (_nonneg : 0 ≤ b + B),
    r.readout () ⟨R, instR, instA, N, B, a, b⟩ F =
      ∑ j ∈ Finset.range ((b + B).toNat + 1),
        (((-1 : ℂ) ^ j) * integerBinomial (-(N : ℤ)) j) •
          clear N F (a + N + j) (b - j)

theorem source_bridge :
    (type_of% (@supported_reconstruction.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl

/-- These are precisely the remaining source-family mathematical obligations;
no inhabitant or validated registration is claimed by this attempt. -/
abbrev RequiredEvidence := Registration arena.{u} (type_of% (@supported_reconstruction.{u}))

end
end Reg.D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries
