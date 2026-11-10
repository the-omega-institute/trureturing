import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.OriginalCriticalBRST
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyProduct

/-! Source-only registration candidate for the actual quotient product_assoc.
The native source is pinned by inputs.json, SHA256
282eaadefba0c6fced4d8e3096d126b8cc3f235f10154ccd882dbf5279189627.
Its full critical telescope and arbitrary mixed-parity classes are retained.
The diagonal witness only inhabits the intervention/dependence parameter domain.
Source selection and its compiler evidence remain absent; no certificate,
native Reg acceptance, or registration of other public helpers is claimed.
Original mathematical attribution remains with the imported suppliers. -/

set_option autoImplicit false
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.OriginalCriticalBRST
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyProduct

abbrev signature : Signature where
  Params := Σ x : Input, Space x × Space x × Space x
  State x := Space x.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (x : signature.Params) : signature.State x :=
  product x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH
    (product x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH x.2.1 x.2.2.1) x.2.2.2

def actual : Realization signature := realize signature
  (fun _ x y => lhs x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (a b c : Cohomology D H h26 hHG hGH),
    R.readout () ⟨⟨D,H,h26,hHG,hGH⟩,a,b,c⟩
      (product D H h26 hHG hGH a (product D H h26 hHG hGH b c))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0 0

def family : Registration arena (type_of% @product_assoc) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨product_assoc, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let x : signature.Params := ⟨witness,0,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@product_assoc) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyProduct.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => lhs x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some LatticeData
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyProduct
