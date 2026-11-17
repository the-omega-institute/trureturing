import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.OriginalCriticalBRST
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

/-! Faithful full-telescope source-family audit attempts for the two public
endpoints. The dependent-family kernel obligations below do not replace
compiler-bound source reconstruction. sourceSelection remains absent, so no
declared_validated registration or source-selection certificate is claimed. -/

set_option autoImplicit false
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
open _root_.D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyReduction
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.OriginalCriticalBRST
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder

namespace Defect
abbrev signature : Signature where
  Params := Σ x : Input, Space x × Space x
  State x := Space x.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (x : signature.Params) : signature.State x :=
  Delta x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH
      (product x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH x.2.1 x.2.2) -
    product x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH
      (Delta x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH x.2.1) x.2.2 -
    product x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH
      (parity x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH x.2.1)
      (Delta x.1.D x.1.H x.1.h26 x.1.hHG x.1.hGH x.2.2)

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
    (a b : Cohomology D H h26 hHG hGH),
    R.readout () ⟨⟨D,H,h26,hHG,hGH⟩,a,b⟩
      (cohomologyCurrent D H h26 hHG hGH a b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0

def family : Registration arena (type_of% @Delta_product_defect) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Delta_product_defect, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let x : signature.Params := ⟨witness,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Delta_product_defect) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder.Defect.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder.Defect.family
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

end Defect

namespace Leibniz
structure Parameters where
  input : Input
  a : Space input
  b : Space input
  c : Space input
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
  homogeneousDefect x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH x.p x.a
    (product x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH x.b x.c)

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
    (a b c : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ) ^ p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ) ^ q • b),
    R.readout () ⟨⟨D,H,h26,hHG,hGH⟩,a,b,c,p,q,ha,hb⟩
      (product D H h26 hHG hGH (homogeneousDefect D H h26 hHG hGH p a b) c +
        (-1 : ℂ) ^ ((p + 1) * q) • product D H h26 hHG hGH b
          (homogeneousDefect D H h26 hHG hGH p a c))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0 0 0 0
    (by simp) (by simp)

def family : Registration arena (type_of% @Delta_second_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Delta_second_order, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let x : signature.Params := ⟨witness,0,0,0,0,0,by simp,by simp⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Delta_second_order) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder.Leibniz.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder.Leibniz.family
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

end Leibniz

end Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder
