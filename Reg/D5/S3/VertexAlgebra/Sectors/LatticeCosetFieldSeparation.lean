import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetFieldSeparation

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeDiscriminantTheta
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped VertexOperator

noncomputable section

structure Params where
  D : LatticeData
  e : ℕ
  B : Matrix (Fin D.rank) (Fin e) ℤ
  C : Matrix (Fin e) (Fin e) ℤ
  hC : ∀ i j, C i j = C j i
  hCe : ∀ i, Even (C i i)
  hD : (gramReal D).PosDef
  a : Fin e → ℤ
  u : Carrier D
  j : Fin e
  k : ℕ
  m : ℤ

abbrev signature : Signature where
  Params := Params
  State p := Carrier (ambient p.D p.e p.B p.C p.hC p.hCe)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Carrier (ambient p.D p.e p.B p.C p.hC p.hCe)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p v => if role then
    multiply _ (transverse p.D p.B p.C p.hC p.hCe p.j p.k)
      (((Y (ambient p.D p.e p.B p.C p.hC p.hCe)
        (injection p.D p.B p.C p.hC p.hCe p.a p.u))[[p.m]]) v) -
    (transversePair p.D p.B p.C p.a p.j : ℂ) •
      (((Y (ambient p.D p.e p.B p.C p.hC p.hCe)
        (injection p.D p.B p.C p.hC p.hCe p.a p.u))[[p.m-(p.k+1 : ℕ)]]) v)
    else
      ((Y (ambient p.D p.e p.B p.C p.hC p.hCe)
        (injection p.D p.B p.C p.hC p.hCe p.a p.u))[[p.m]])
          (multiply _ (transverse p.D p.B p.C p.hC p.hCe p.j p.k) v))
  (fun x => nomatch x)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) {e : ℕ}
    (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
    (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))
    (hD : (gramReal D).PosDef) (a : Fin e → ℤ) (u : Carrier D)
    (j : Fin e) (k : ℕ) (m : ℤ) (v : Carrier (ambient D e B C hC hCe)),
    r.readout false ⟨D,e,B,C,hC,hCe,hD,a,u,j,k,m⟩ v =
      r.readout true ⟨D,e,B,C,hC,hCe,hD,a,u,j,k,m⟩ v

theorem source_bridge :
    (type_of% (@LatticeCosetFieldSeparation.field_transverse_commutator)) ↔
      arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual :=
  source_bridge.mp (@LatticeCosetFieldSeparation.field_transverse_commutator)

/- A full Contract.Registration additionally requires the enrolled dependent
readout tied to these exact source roles, sourceSelection and the proofs of
whole-family Variation, Sensitivity and ObservationalDependence. No value of
that type and no declared_validated status is asserted by this partial arena. -/

end
end Reg.D5.S3.VertexAlgebra.LatticeCosetFieldSeparation
