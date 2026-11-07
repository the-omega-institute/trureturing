import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.OriginalCriticalBRST
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyOddBracket

/-! Full critical source families for shifted antisymmetry, current/Delta
compatibility, bracket/Delta compatibility and Jacobi. The realization and
intervention proofs retain the full telescope. Compiler-bound source selectors
and escaping source types remain unspecified. -/

set_option autoImplicit false
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder (cohomologyCurrent)
open _root_.D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyReduction (Delta)
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

namespace CurrentDelta
structure Parameters where
  input : Input
  a : Space input
  b : Space input

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
  Delta x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH
    (cohomologyCurrent x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH
      x.a x.b)

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
      (-cohomologyCurrent D H h26 hHG hGH (Delta D H h26 hHG hGH a) b -
        cohomologyCurrent D H h26 hHG hGH (parity D H h26 hHG hGH a)
          (Delta D H h26 hHG hGH b))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0

def family : Registration arena (type_of% @cohomologyCurrent_delta) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cohomologyCurrent_delta, rejected, rejected_law⟩
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
    (@cohomologyCurrent_delta) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.CurrentDelta.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.CurrentDelta.family
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

end CurrentDelta

namespace DeltaBracket
structure Parameters where
  input : Input
  a : Space input
  b : Space input

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
  Delta x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH
    (oddBracket x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH x.a x.b)

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
      (oddBracket D H h26 hHG hGH (Delta D H h26 hHG hGH a) b -
        oddBracket D H h26 hHG hGH (parity D H h26 hHG hGH a)
          (Delta D H h26 hHG hGH b))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0

def family : Registration arena (type_of% @Delta_bracket) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Delta_bracket, rejected, rejected_law⟩
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
    (@Delta_bracket) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.DeltaBracket.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.DeltaBracket.family
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

end DeltaBracket

namespace Jacobi
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
  oddBracket x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH x.a
    (oddBracket x.input.D x.input.H x.input.h26 x.input.hHG x.input.hGH x.b x.c)

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
      (oddBracket D H h26 hHG hGH (oddBracket D H h26 hHG hGH a b) c +
        (-1 : ℂ)^((p + 1) * (q + 1)) •
          oddBracket D H h26 hHG hGH b
            (oddBracket D H h26 hHG hGH a c))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h witness.D witness.H witness.h26 witness.hHG witness.hGH 0 0 0 0 0
    (by simp) (by simp)

def family : Registration arena (type_of% @oddBracket_jacobi) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨oddBracket_jacobi, rejected, rejected_law⟩
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
    (@oddBracket_jacobi) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.Jacobi.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket.Jacobi.family
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

end Jacobi
end Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket
