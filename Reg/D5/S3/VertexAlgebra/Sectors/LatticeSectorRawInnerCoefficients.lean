import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeSectorRawInnerCoefficients

/-! The dependent realization retains the original lattice data, charges,
states and complete witness telescope. Its readout is the original proposition.
The exact source bridge does not supply the variation, intervention or
observational-dependence evidence required by a four-slot registration. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorRawInnerCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open _root_.D5.S3.VertexAlgebra.LatticeSectorRawInnerCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

structure Parameter where
  D : LatticeData
  α : Charge D
  β : Charge D
  γ : Charge D

def signature : Signature where
  Params := Parameter
  State p := Sector p.D p.α × Sector p.D p.β × Sector p.D p.γ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p states => type_of% (actual_three_field_raw_inner_coefficients
      p.D p.α p.β p.γ states.1 states.2.1 states.2.2))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ),
      r.readout () ⟨D, α, β, γ⟩ (u, v, t)

theorem source_bridge :
    (type_of% (@actual_three_field_raw_inner_coefficients)) ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := actual_three_field_raw_inner_coefficients

/-- A proposition readout of a universally proved law cannot witness dependence. -/
theorem proposition_readout_has_no_dependence :
    ¬ ObservationalDependence signature actual := by
  intro dependence
  obtain ⟨p, x, y, different⟩ := dependence ()
  apply different
  apply propext
  constructor <;> intro _
  · exact actual_three_field_raw_inner_coefficients p.D p.α p.β p.γ
      y.1 y.2.1 y.2.2
  · exact actual_three_field_raw_inner_coefficients p.D p.α p.β p.γ
      x.1 x.2.1 x.2.2

abbrev RequiredEvidence :=
  Registration arena (type_of% (@actual_three_field_raw_inner_coefficients))

#print source_bridge
#print axioms source_bridge
end
end Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorRawInnerCoefficients
