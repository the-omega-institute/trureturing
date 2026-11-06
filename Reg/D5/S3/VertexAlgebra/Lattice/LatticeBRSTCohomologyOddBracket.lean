import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.OriginalCriticalBRST
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyOddBracket

/-! Faithful source-family audit attempt for the actual shifted antisymmetry
law. The source selector is intentionally unresolved; this records the full
critical telescope and leaves binding acceptance to the audit machinery. -/

set_option autoImplicit false
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.OriginalCriticalBRST
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket

namespace Antisymm
structure Parameters where
  input : Input
  a : Space input
  b : Space input
  p : ℕ
  q : ℕ
  ha : parity input.D input.H input.h26 input.hHG input.hGH a = (-1 : ℂ) ^ p • a
  hb : parity input.D input.H input.h26 input.hHG input.hGH b = (-1 : ℂ) ^ q • b

abbrev signature : Signature where
  Params := Parameters
  State x := Space x.input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (x : signature.Params) : signature.State x :=
  oddBracket x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH x.a x.b

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
    (a b : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ) ^ p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ) ^ q • b),
    R.readout () ⟨⟨D,H,h26,hHG,hGH⟩,a,b,p,q,ha,hb⟩
      (-((-1 : ℂ)^((p + 1) * (q + 1))) •
        oddBracket D H h26 hHG hGH b a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0 0 0
    (by simp) (by simp)

def family : Registration arena (type_of% @oddBracket_antisymm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨oddBracket_antisymm, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let x : signature.Params := ⟨witness,0,0,0,0,by simp,by simp⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@oddBracket_antisymm) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.Antisymm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.Antisymm.family
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
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Antisymm
end Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket
