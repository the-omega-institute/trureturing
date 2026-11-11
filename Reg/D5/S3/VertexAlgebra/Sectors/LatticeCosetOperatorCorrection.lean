import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetOperatorCorrection

/-! Exact dependent source realization of the native all-state correction.
The enrolled readout and intervention evidence remain unconstructed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetOperatorCorrection

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeCosetCompression LatticeDiscriminantTheta
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator

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
  b : Fin e → ℤ
  c : Fin e → ℤ
  u : Carrier D
  v : Carrier D
  p : ℤ
  q : ℤ

abbrev signature : Signature where
  Params := Params
  State p := Carrier p.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Carrier p.D
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role t w => if role then
    ∑ᶠ j : ℕ, correction t.D t.B t.C t.a t.b j •
      compressed t.D t.B t.C t.hC t.hCe t.a (t.b+t.c) t.u (t.p-j)
        (compressed t.D t.B t.C t.hC t.hCe t.b t.c t.v (t.q+j) w)
    else
      projection t.D t.B t.C t.hC t.hCe (t.a+t.b+t.c)
        (((Y (ambient t.D t.e t.B t.C t.hC t.hCe)
          (injection t.D t.B t.C t.hC t.hCe t.a t.u))[[t.p]])
          (((Y (ambient t.D t.e t.B t.C t.hC t.hCe)
            (injection t.D t.B t.C t.hC t.hCe t.b t.v))[[t.q]])
              (injection t.D t.B t.C t.hC t.hCe t.c w))))
  (fun x => nomatch x)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) {e : ℕ}
    (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
    (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))
    (hD : (gramReal D).PosDef) (a b c : Fin e → ℤ)
    (u v w : Carrier D) (p q : ℤ),
    r.readout false ⟨D,e,B,C,hC,hCe,hD,a,b,c,u,v,p,q⟩ w =
      r.readout true ⟨D,e,B,C,hC,hCe,hD,a,b,c,u,v,p,q⟩ w

theorem source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetOperatorCorrection.intermediate_projection_correction)) ↔
      arena.Law actual := by
  constructor
  · intro h D e B C hC hCe hD a b c u v w p q
    exact (h D B C hC hCe hD a b c u v w p q).2
  · intro h D e B C hC hCe hD a b c u v w p q
    exact ⟨correction_finite D B C hC hCe a b c u v w p q,
      h D B C hC hCe hD a b c u v w p q⟩

theorem source_actual : arena.Law actual :=
  source_bridge.mp
    (@_root_.D5.S3.VertexAlgebra.LatticeCosetOperatorCorrection.intermediate_projection_correction)

/- The actual realization and exact source equivalence retain the full
infinite dependent telescope, including zero-rank fibers. A lawful enrolled
readout, sourceSelection and whole-family Variation, Sensitivity and
ObservationalDependence are still required for Contract.Registration.
No value of that type and no declared_validated status is asserted. -/

end
end Reg.D5.S3.VertexAlgebra.LatticeCosetOperatorCorrection
