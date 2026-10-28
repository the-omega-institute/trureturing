import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra

set_option autoImplicit false

open D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra.Core (star)
open private axisState
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open Lattice.NormFourVacuumIrreducible Lattice.NormFourZhuFinite
open Lattice.NormFourZhuAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- The original determinant-unit family, actual product and actual axis
are retained. Whole-family variation, sensitivity, actual observational
dependence, lawful enrolled readout and source selection remain unproved.
These source bridges are not Contract.Registration declarations.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22489 -/
structure Params where
  D : LatticeData
  hd : IsUnit D.G.det
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ
  hs : s ^ 2 = 1

abbrev Q (p : Params) :=
  vacuumDescendants p.D p.a p.s ⧸
    (zhuO p.D p.a p.s).comap (vacuumDescendants p.D p.a p.s).subtype

namespace AlgebraAudit

abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Q p →ₗ[ℂ] Q p →ₗ[ℂ] Q p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => quotientProduct p.D p.hd p.a p.ha p.s p.hs)
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hd : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    letI := quotientRing D hd a ha s hs
    letI := quotientAlgebra D hd a ha s hs
    let O := (zhuO D a s).comap (vacuumDescendants D a s).subtype
    let q := O.mkQ
    let x := q (axisState D a ha s hs)
    (∀ u v, q (star D a ha s hs u v)=
      r.readout () (⟨D,hd,a,ha,s,hs⟩ : Params) () (q u) (q v)) ∧
    FiniteDimensional ℂ (_root_.Reg.D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra.Q
      (⟨D,hd,a,ha,s,hs⟩ : Params)) ∧
    Module.finrank ℂ (vacuumDescendants D a s ⧸ O)=3 ∧
    x*(x-algebraMap ℂ (vacuumDescendants D a s ⧸ O) (1/16))*
      (x-algebraMap ℂ (vacuumDescendants D a s ⧸ O) (1/2))=0

theorem source_bridge :
    (type_of% (@actual_zhu_algebra)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := source_bridge.mp (@actual_zhu_algebra)

end AlgebraAudit

namespace PresentationAudit

abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Q p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ =>
    ((zhuO p.D p.a p.s).comap (vacuumDescendants p.D p.a p.s).subtype).mkQ
      (axisState p.D p.a p.ha p.s p.hs))
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hd : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    letI := quotientRing D hd a ha s hs
    letI := quotientAlgebra D hd a ha s hs
    let O := (zhuO D a s).comap (vacuumDescendants D a s).subtype
    let x := r.readout () (⟨D,hd,a,ha,s,hs⟩ : Params) ()
    zhuPolynomial.Monic ∧
    (∃ E : AdjoinRoot zhuPolynomial ≃ₐ[ℂ] (vacuumDescendants D a s ⧸ O),
      E (AdjoinRoot.root zhuPolynomial)=x) ∧
    (64:ℂ) • x^3-(36:ℂ) • x^2+(2:ℂ) • x=0

theorem source_bridge :
    (type_of% (@actual_zhu_presentation)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := source_bridge.mp (@actual_zhu_presentation)

end PresentationAudit
end Reg.D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra
